use crate::connection::Connection;
use crate::control;
use crate::jupyter::JupyterMessage;
use crate::lang::{interp, lexer, parser};
use anyhow::Result;
use json::JsonValue;
use std::collections::HashMap;
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

#[derive(Clone)]
pub(crate) struct Server {
    iopub: Arc<Mutex<Connection>>,
    latest_execution_request: Arc<Mutex<Option<JupyterMessage>>>,
    shutdown_requested_receiver: Arc<Mutex<mpsc::Receiver<()>>>,
    shutdown_requested_sender: Arc<Mutex<mpsc::Sender<()>>>,
    interpreter: Arc<Mutex<interp::Interpreter>>,
}

impl Server {
    pub(crate) fn start(config: &control::Control) -> Result<Server> {
        use zmq::SocketType;

        let zmq_context = zmq::Context::new();
        let heartbeat = bind_socket(config, config.hb_port, zmq_context.socket(SocketType::REP)?)?;
        let shell_socket = bind_socket(
            config,
            config.shell_port,
            zmq_context.socket(SocketType::ROUTER)?,
        )?;
        let control_socket = bind_socket(
            config,
            config.control_port,
            zmq_context.socket(SocketType::ROUTER)?,
        )?;
        bind_socket(
            config,
            config.stdin_port,
            zmq_context.socket(SocketType::ROUTER)?,
        )?;
        let iopub = Arc::new(Mutex::new(bind_socket(
            config,
            config.iopub_port,
            zmq_context.socket(SocketType::PUB)?,
        )?));

        let (shutdown_requested_sender, shutdown_requested_receiver) = mpsc::channel();

        let latest_execution_request = Arc::new(Mutex::new(None));
        let server = Server {
            iopub: iopub.clone(),
            latest_execution_request: latest_execution_request.clone(),
            shutdown_requested_receiver: Arc::new(Mutex::new(shutdown_requested_receiver)),
            shutdown_requested_sender: Arc::new(Mutex::new(shutdown_requested_sender)),
            interpreter: Arc::new(Mutex::new(interp::Interpreter::new(move |text: &str| {
                if let Some(message) = &*latest_execution_request.lock().unwrap() {
                    message
                        .new_message("stream")
                        .with_content(object! {
                            "name" => "stdout",
                            "text" => text,
                        })
                        .send(&*iopub.lock().unwrap())
                        .unwrap();
                }
            }))),
        };

        let (execution_sender, execution_receiver) = mpsc::channel();
        let (execution_response_sender, execution_response_receiver) = mpsc::channel();

        thread::spawn(move || Self::handle_hb(&heartbeat));
        server.start_thread(move |server: Server| server.handle_control(control_socket));
        server.start_thread({
            move |server: Server| {
                server.handle_shell(
                    shell_socket,
                    &execution_sender,
                    &execution_response_receiver,
                )
            }
        });
        server.start_thread(move |server: Server| {
            server.handle_execution_requests(&execution_receiver, &execution_response_sender)
        });
        Ok(server)
    }

    pub(crate) fn wait_for_shutdown(&self) {
        self.shutdown_requested_receiver
            .lock()
            .unwrap()
            .recv()
            .unwrap();
    }

    fn signal_shutdown(&self) {
        self.shutdown_requested_sender
            .lock()
            .unwrap()
            .send(())
            .unwrap();
    }

    fn start_thread<F>(&self, body: F)
    where
        F: FnOnce(Server) -> Result<()> + std::marker::Send + 'static,
    {
        let server_clone = self.clone();
        thread::spawn(move || {
            if let Err(error) = body(server_clone) {
                eprintln!("{:?}", error);
            }
        });
    }

    fn handle_hb(connection: &Connection) -> Result<()> {
        let mut message = zmq::Message::new();
        let ping: &[u8] = b"ping";
        loop {
            connection.socket.recv(&mut message, 0)?;
            connection.socket.send(ping, 0)?;
        }
    }

    fn handle_execution_requests(
        mut self,
        receiver: &mpsc::Receiver<JupyterMessage>,
        execution_reply_sender: &mpsc::Sender<JupyterMessage>,
    ) -> Result<()> {
        let mut execution_count = 1;
        loop {
            let message = receiver.recv()?;

            *self.latest_execution_request.lock().unwrap() = Some(message.clone());
            let src = message.code();
            execution_count += 1;
            message
                .new_message("execute_input")
                .with_content(object! {
                    "execution_count" => execution_count,
                    "code" => src
                })
                .send(&*self.iopub.lock().unwrap())?;

            match self.process(src) {
                Ok(()) => {
                    let data: HashMap<&str, &str> = HashMap::from([("text/plain", "")]);
                    message
                        .new_message("execute_result")
                        .with_content(object! {
                            "execution_count" => execution_count,
                            "data" => data,
                            "metadata" => object!(),
                        })
                        .send(&*self.iopub.lock().unwrap())?;
                    execution_reply_sender.send(message.new_reply().with_content(object! {
                        "status" => "ok",
                        "execution_count" => execution_count,
                    }))?;
                }
                Err(error) => {
                    let result = format!("\u{001b}[1;31mError:\u{001b}[0m\n{}", error);
                    message
                        .new_message("error")
                        .with_content(object! {
                            "ename" => "Error",
                            "evalue" => "lox error",
                            "traceback" => array![result],
                            "data" => "",
                        })
                        .send(&*self.iopub.lock().unwrap())?;
                    execution_reply_sender.send(message.new_reply().with_content(object! {
                        "status" => "error",
                        "execution_count" => execution_count
                    }))?;
                }
            }
        }
    }

    fn handle_shell(
        self,
        connection: Connection,
        execution_channel: &mpsc::Sender<JupyterMessage>,
        execution_reply_receiver: &mpsc::Receiver<JupyterMessage>,
    ) -> Result<()> {
        loop {
            let message = JupyterMessage::read(&connection)?;
            message
                .new_message("status")
                .with_content(object! {"execution_state" => "busy"})
                .send(&*self.iopub.lock().unwrap())?;
            let idle = message
                .new_message("status")
                .with_content(object! {"execution_state" => "idle"});
            if message.message_type() == "kernel_info_request" {
                message
                    .new_reply()
                    .with_content(kernel_info())
                    .send(&connection)?;
            } else if message.message_type() == "is_complete_request" {
                message
                    .new_reply()
                    .with_content(object! {"status" => "complete"})
                    .send(&connection)?;
            } else if message.message_type() == "execute_request" {
                execution_channel.send(message)?;
                execution_reply_receiver.recv()?.send(&connection)?;
            } else if message.message_type() == "comm_open" {
                message
                    .comm_close_message()
                    .send(&self.iopub.lock().unwrap())?;
            } else if message.message_type() == "comm_msg"
                || message.message_type() == "comm_info_request"
            {
                // We don't handle this yet.
            } else if message.message_type() == "complete_request" {
                message
                    .new_reply()
                    .with_content(object! {
                        "status" => "ok",
                        "matches" => Vec::<String>::new(),
                        "cursor_start" => message.cursor_pos(),
                        "cursor_end" => message.cursor_pos(),
                        "metadata" => object!{},
                    })
                    .send(&connection)?;
            } else {
                eprintln!(
                    "Got unrecognized message type on shell channel: {}",
                    message.message_type()
                );
            }
            idle.send(&*self.iopub.lock().unwrap())?;
        }
    }

    fn handle_control(self, connection: Connection) -> Result<()> {
        loop {
            let message = JupyterMessage::read(&connection)?;
            match message.message_type() {
                "shutdown_request" => self.signal_shutdown(),
                "interrupt_request" => {
                    message.new_reply().send(&connection)?;
                    eprintln!(
                        "Lox doesn't support interrupting execution. Perhaps restart kernel?"
                    );
                }
                _ => {
                    eprintln!(
                        "Got unrecognized message type on control channel: {}",
                        message.message_type()
                    );
                }
            }
        }
    }

    fn process(&mut self, src: &str) -> Result<()> {
        let program = parser::Parser::new(lexer::Lexer::from_str(src)).parse()?;
        self.interpreter.lock().unwrap().eval(&program)
    }
}

fn bind_socket(config: &control::Control, port: u16, socket: zmq::Socket) -> Result<Connection> {
    let endpoint = format!("{}://{}:{}", config.transport, config.ip, port);
    socket.bind(&endpoint)?;
    Connection::new(socket, &config.key)
}

/// See [Kernel info documentation](https://jupyter-client.readthedocs.io/en/stable/messaging.html#kernel-info)
fn kernel_info() -> JsonValue {
    object! {
        "protocol_version" => "5.3",
        "implementation" => env!("CARGO_PKG_NAME"),
        "implementation_version" => env!("CARGO_PKG_VERSION"),
        "language_info" => object!{
            "name" => "Lox",
            "version" => "",
            "mimetype" => "text/lox",
            "file_extension" => ".lox",
            "pygment_lexer" => "lox",
            "codemirror_mode" => "lox",
        },
        "banner" => format!("lox {} - Evaluation Context for Lox", env!("CARGO_PKG_VERSION")),
        "help_links" => array![
            object!{"text" => "Lox Language",
                    "url" => "https://craftinginterpreters.com/the-lox-language.html"}
        ],
        "status" => "ok"
    }
}

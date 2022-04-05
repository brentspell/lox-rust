#[macro_use]
extern crate json;
extern crate lazy_static;

use anyhow::{anyhow, bail, Result};

mod lang;

mod connection;
mod control;
mod install;
mod jupyter;
mod server;

fn run(control_file_name: &str) -> Result<()> {
    let config = control::Control::parse_file(control_file_name)?;
    let server = server::Server::start(&config)?;
    server.wait_for_shutdown();
    Ok(())
}

fn main() -> Result<()> {
    let mut args = std::env::args();
    let bin = args.next().unwrap();
    if let Some(arg) = args.next() {
        match arg.as_str() {
            "--control_file" => {
                if let Err(error) = install::update_if_necessary() {
                    eprintln!("Warning: tried to update client, but failed: {}", error);
                }
                return run(&args.next().ok_or_else(|| anyhow!("Missing control file"))?);
            }
            "--install" => return install::install(),
            "--uninstall" => return install::uninstall(),
            "--help" => {}
            x => bail!("Unrecognised option {}", x),
        }
    }
    println!("To install, run:\n  {} --install", bin);
    println!("To uninstall, run:\n  {} --uninstall", bin);
    Ok(())
}

#[cfg(feature = "mimalloc")]
#[global_allocator]
static MIMALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

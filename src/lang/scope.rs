use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Default)]
pub struct Scope {
    name: String,
    names: HashMap<String, String>,
    parent: Option<Rc<Scope>>,
}

impl Scope {
    pub fn push(scope: &Rc<Scope>, name: &str) -> Rc<Scope> {
        Rc::new(Scope {
            name: name.to_string(),
            names: HashMap::new(),
            parent: Some(scope.clone()),
        })
    }

    pub fn pop(scope: &Rc<Scope>) -> Option<Rc<Scope>> {
        scope.parent.clone()
    }

    pub fn define(&mut self, name: &str) -> String {
        let qname = self.qname(name);
        self.names.insert(name.to_string(), qname.clone());
        qname
    }

    pub fn resolve(&self, name: &str) -> String {
        match self.names.get(name) {
            Some(value) => value.clone(),
            None => match &self.parent {
                Some(parent) => parent.resolve(name),
                None => format!("::{}", name),
            },
        }
    }

    fn qname(&self, name: &str) -> String {
        let mut qname = match &self.parent {
            None => self.name.clone(),
            Some(parent) => parent.qname(&self.name),
        };
        qname.push_str("::");
        qname.push_str(name);
        qname
    }
}

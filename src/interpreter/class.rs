use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::ast::ClassBody;

use super::{
    callable::Func,
    callable::LoxFunc,
    runtime::{Environment, RuntimeError},
    Interpreter, Value,
};

pub const INIT_METHOD_NAME: &str = "init";

#[derive(Clone)]
pub struct Class {
    pub inner: Rc<ClassInner>,
}

impl Class {
    pub fn get_method(&self, method: &str) -> Option<Rc<LoxFunc>> {
        self.inner.methods.get(method).cloned()
    }
}

pub struct ClassInner {
    pub name: String,
    pub methods: HashMap<String, Rc<LoxFunc>>,
    pub class_methods: HashMap<String, Rc<LoxFunc>>,
}

impl Class {
    // Build the runtime class structure out of the ClassDecl pieces
    pub fn new(name: &str, body: &ClassBody, closure: Rc<Environment>) -> Class {
        let mut methods = HashMap::new();
        for method in body.methods.iter() {
            let func = Rc::new(LoxFunc {
                name: method.name.clone(),
                parameters: method.parameters.clone(),
                body: method.body.as_ref().clone(),
                closure: closure.clone(),
                is_init: false,
            });
            methods.insert(method.name.clone(), func);
        }

        let mut class_methods = HashMap::new();
        for method in body.class_methods.iter() {
            let func = Rc::new(LoxFunc {
                name: method.name.clone(),
                parameters: method.parameters.clone(),
                body: method.body.as_ref().clone(),
                closure: closure.clone(),
                is_init: false,
            });
            class_methods.insert(method.name.clone(), func);
        }

        Class {
            inner: Rc::new(ClassInner {
                name: name.to_string(),
                methods,
                class_methods,
            }),
        }
    }

    pub fn name(&self) -> &str {
        &self.inner.name
    }

    pub fn arity(&self) -> u8 {
        match &self.inner.methods.get(INIT_METHOD_NAME) {
            Some(init) => init.arity(),
            None => 0u8,
        }
    }

    pub fn construct(
        &self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        let instance = Instance {
            fields: Rc::new(RefCell::new(HashMap::new())),
            class: self.clone(),
        };

        if let Some(init) = self.inner.methods.get(INIT_METHOD_NAME) {
            _ = init.bind(instance.clone()).call(interpreter, args)?;
        }

        Ok(Value::Instance(instance))
    }
}

#[derive(Clone)]
pub struct Instance {
    pub fields: Rc<RefCell<HashMap<String, Value>>>,
    pub class: Class,
}

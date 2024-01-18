use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::ast::ClassBody;

use super::{
    callable::LoxFunc,
    callable::{Func, UnboundLoxFunc},
    runtime::{Environment, RuntimeError},
    Interpreter, Value,
};

pub const INIT_METHOD_NAME: &str = "init";

#[derive(Clone)]
pub struct Class {
    pub inner: Rc<ClassInner>,
}

pub struct ClassInner {
    pub name: String,
    pub init: Option<UnboundLoxFunc>,
    pub methods: Vec<UnboundLoxFunc>,
    pub class_methods: HashMap<String, Rc<LoxFunc>>,
}

impl Class {
    // Build the runtime class structure out of the ClassDecl pieces
    pub fn new(name: &str, body: &ClassBody, closure: Rc<Environment>) -> Class {
        let mut init: Option<UnboundLoxFunc> = None;

        let methods: Vec<UnboundLoxFunc> = body
            .methods
            .iter()
            .map(|fun_decl| {
                let is_init = fun_decl.name == INIT_METHOD_NAME;
                let unbound = UnboundLoxFunc {
                    name: fun_decl.name.clone(),
                    parameters: fun_decl.parameters.clone(),
                    body: fun_decl.body.as_ref().clone(),
                    is_init,
                };
                if is_init {
                    init = Some(unbound.clone())
                }
                unbound
            })
            .collect();

        let mut class_methods = HashMap::new();
        for member in body.class_methods.iter() {
            let func = Rc::new(LoxFunc {
                name: member.name.clone(),
                parameters: member.parameters.clone(),
                body: member.body.as_ref().clone(),
                closure: closure.clone(),
                is_init: false,
            });
            class_methods.insert(member.name.clone(), func);
        }

        Class {
            inner: Rc::new(ClassInner {
                name: name.to_string(),
                init,
                methods,
                class_methods,
            }),
        }
    }

    pub fn name(&self) -> &str {
        &self.inner.name
    }

    pub fn arity(&self) -> u8 {
        match &self.inner.init {
            Some(init) => init.arity(),
            None => 0u8,
        }
    }

    pub fn construct(
        &self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        let fields = Rc::new(RefCell::new(HashMap::new()));

        let instance = Value::Instance(Instance {
            fields: fields.clone(),
            class: self.clone(),
        });

        let closure = interpreter.current_env_closure().open_scope();
        closure.bind("this", Some(instance.clone()));

        for method in self.inner.methods.iter() {
            let bound_method = Rc::new(method.bind(closure.clone()));
            fields
                .borrow_mut()
                .insert(bound_method.name.clone(), Value::Callable(bound_method));
        }

        if let Some(init) = &self.inner.init {
            // The init function should also have been part of the bound methods above, but we can just bind it again
            let bound_init = init.bind(closure.clone());
            _ = bound_init.call(&mut Interpreter::new_from_closure(closure.clone()), args)?;
        }

        Ok(instance)
    }
}

#[derive(Clone)]
pub struct Instance {
    pub fields: Rc<RefCell<HashMap<String, Value>>>,
    pub class: Class,
}

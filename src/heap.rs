use std::{
    alloc::Layout,
    cell::RefCell,
    fmt::{Debug, Display},
    rc::Rc,
};

use crate::bytecode::Chunk;

#[derive(Debug, Clone)]
#[repr(C, u8)]
pub enum Object {
    String(Rc<String>), // Pretend static
    Function {
        name: Rc<String>,
        arity: u8,
        chunk: Chunk,
    },
}

impl Object {
    pub fn is_string(&self) -> bool {
        match self {
            Object::String(_) => true,
            _ => false,
        }
    }

    pub fn string_slice(&self) -> &str {
        match self {
            Object::String(s) => s,
            _ => panic!("not a string"),
        }
    }
}

#[derive(Clone)]
pub enum Value {
    Bool(bool),
    Nil,
    Number(f64),
    Object(Object), // Wee... pointer casts
}

impl Value {
    pub fn to_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Nil => false,
            _ => true,
        }
    }

    // Create the string representation
    // This will return a Value::Object(Object::String(..))
    // If self is already one, it will return a cloned reference
    pub fn create_string(&self) -> Object {
        match self {
            Value::Object(obj) => unsafe {
                match obj {
                    // Already a string
                    Object::String(str) => Object::String(str.clone()),
                    Object::Function {
                        name,
                        arity: _,
                        chunk: _,
                    } => Object::String(name.clone()),
                }
            },
            Value::Nil => Object::String(Rc::new("nil".to_owned())),
            Value::Number(n) => Object::String(Rc::new(format!("{}", n))),
            Value::Bool(b) => Object::String(Rc::new(format!("{}", b))),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bool(l), Self::Bool(r)) => l == r,
            (Self::Number(l), Self::Number(r)) => l == r,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl Eq for Value {}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Value::Bool(value)
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Value::Number(value)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::Nil => f.write_str("nil"),
            Value::Number(n) => write!(f, "{}", n),
            Value::Object(obj) => unsafe {
                match obj {
                    Object::String(string) => {
                        // We don't allow construct non-utf8 string representations
                        write!(f, "\"{}\"", string)
                    }
                    Object::Function {
                        name,
                        arity: _,
                        chunk: _,
                    } => {
                        write!(f, "<fn {}>", name)
                    }
                }
            },
        }
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

#[derive(Clone)]
pub struct Heap {
    inner: Rc<RefCell<HeapInner>>,
}

struct HeapInner(Vec<(*mut u8, Layout)>);

impl Heap {
    pub fn new() -> Heap {
        Heap {
            inner: Rc::new(RefCell::new(HeapInner(Vec::new()))),
        }
    }

    // // TODO: Something, something, allocation
    // pub fn alloc_string_in_heap(&self, str: &str) -> *mut Object {
    //     // self.inner.as_ref().borrow_mut().objects.push(obj_ptr);
    //     let bytes = str.as_bytes();
    //     let (layout, _) = Layout::new::<u8>().repeat(bytes.len()).unwrap();
    //     let ptr = unsafe { std::alloc::alloc_zeroed(layout) };

    //     self.inner.as_ref().borrow_mut().0.push((ptr, layout));

    //     let slice = unsafe { std::slice::from_raw_parts_mut(ptr, bytes.len()) };

    //     slice.copy_from_slice(bytes);

    //     // Now let us allocate an object
    //     unsafe {
    //         let layout = Layout::new::<Object>();
    //         let obj = std::alloc::alloc_zeroed(layout);
    //         self.inner.as_ref().borrow_mut().0.push((obj, layout));

    //         let obj = obj as *mut Object;
    //         obj.write(Object::String(slice));
    //         obj
    //     }
    // }

    // pub fn alloc_string_buf(&self, len: usize) -> *mut u8 {
    //     let (layout, _) = Layout::new::<u8>().repeat(len).unwrap();
    //     let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
    //     self.inner.as_ref().borrow_mut().0.push((ptr, layout));
    //     ptr
    // }

    // pub fn alloc_object(&self) -> *mut Object {
    //     let layout = Layout::new::<Object>();
    //     let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
    //     self.inner.as_ref().borrow_mut().0.push((ptr, layout));
    //     ptr as *mut Object
    // }
}

impl Drop for HeapInner {
    fn drop(&mut self) {
        for (ptr, layout) in self.0.iter() {
            unsafe {
                std::alloc::dealloc(*ptr, *layout);
            }
        }
    }
}

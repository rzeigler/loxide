use std::{
    alloc::{alloc, Layout},
    cell::RefCell,
    fmt::Display,
    rc::Rc,
};

#[derive(Debug, Clone, Copy)]
pub enum ObjectType {
    String,
}

#[derive(Debug, Clone, Copy)]
#[repr(C, u8)]
pub enum Object {
    String(&'static [u8]), // Pretend static
}

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Bool(bool),
    Nil,
    Number(f64),
    Object(*mut Object), // Wee... pointer casts
}

impl Value {
    pub fn to_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Nil => false,
            _ => true,
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
            Value::Object(o) => write!(f, "{:?}", o),
        }
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

    // TODO: Something, something, allocation
    pub fn alloc_str_copy(&mut self, str: &str) -> Value {
        // self.inner.as_ref().borrow_mut().objects.push(obj_ptr);
        let bytes = str.as_bytes();
        let (layout, _) = Layout::new::<u8>().repeat(bytes.len()).unwrap();
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };

        self.inner.as_ref().borrow_mut().0.push((ptr, layout));

        let slice = unsafe { std::slice::from_raw_parts_mut(ptr, bytes.len()) };

        for (from, to) in bytes.iter().zip(slice.iter_mut()) {
            *to = *from
        }

        // Now let us allocate an object
        unsafe {
            let layout = Layout::new::<Object>();
            let obj = std::alloc::alloc_zeroed(layout);
            self.inner.as_ref().borrow_mut().0.push((obj, layout));

            let obj = obj as *mut Object;
            obj.write(Object::String(slice));
            Value::Object(obj)
        }
    }
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

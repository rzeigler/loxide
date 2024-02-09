use std::{
    alloc::Layout,
    cell::RefCell,
    fmt::{Debug, Display},
    rc::Rc,
};

#[derive(Debug, Clone, Copy)]
#[repr(C, u8)]
pub enum Object {
    String(&'static [u8]), // Pretend static
}

impl Object {
    pub fn is_string(&self) -> bool {
        match self {
            Object::String(_) => true,
        }
    }

    pub fn string_slice(&self) -> &'static [u8] {
        match self {
            Object::String(s) => s,
        }
    }
}

#[derive(Clone, Copy)]
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

    // Create the string representation
    // This will return a Value::Object(Object::String(..))
    // If self is already one, it will return a cloned reference
    pub fn create_string(&self, heap: &Heap) -> *mut Object {
        match self {
            Value::Object(obj_ptr) => unsafe {
                match std::ptr::read(*obj_ptr) {
                    // Already a string
                    Object::String(_) => *obj_ptr,
                }
            },
            Value::Nil => heap.alloc_string_in_heap("nil"),
            Value::Number(n) => heap.alloc_string_in_heap(&format!("{}", n)),
            Value::Bool(b) => heap.alloc_string_in_heap(&format!("{}", b)),
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
            Value::Object(obj_ptr) => unsafe {
                match &**obj_ptr {
                    Object::String(slice) => {
                        // We don't allow construct non-utf8 string representations
                        write!(f, "\"{}\"", std::str::from_utf8_unchecked(slice))
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

    // TODO: Something, something, allocation
    pub fn alloc_string_in_heap(&self, str: &str) -> *mut Object {
        // self.inner.as_ref().borrow_mut().objects.push(obj_ptr);
        let bytes = str.as_bytes();
        let (layout, _) = Layout::new::<u8>().repeat(bytes.len()).unwrap();
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };

        self.inner.as_ref().borrow_mut().0.push((ptr, layout));

        let slice = unsafe { std::slice::from_raw_parts_mut(ptr, bytes.len()) };

        slice.copy_from_slice(bytes);

        // Now let us allocate an object
        unsafe {
            let layout = Layout::new::<Object>();
            let obj = std::alloc::alloc_zeroed(layout);
            self.inner.as_ref().borrow_mut().0.push((obj, layout));

            let obj = obj as *mut Object;
            obj.write(Object::String(slice));
            obj
        }
    }

    pub fn alloc_string_buf(&self, len: usize) -> *mut u8 {
        let (layout, _) = Layout::new::<u8>().repeat(len).unwrap();
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
        self.inner.as_ref().borrow_mut().0.push((ptr, layout));
        ptr
    }

    pub fn alloc_object(&self) -> *mut Object {
        let layout = Layout::new::<Object>();
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
        self.inner.as_ref().borrow_mut().0.push((ptr, layout));
        ptr as *mut Object
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

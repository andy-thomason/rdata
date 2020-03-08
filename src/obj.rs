use num_traits::FromPrimitive;
use std::sync::Arc;
use std::any::Any;

/// An idiomatic representation of an R object.
#[derive(PartialEq, Clone)]
pub enum Obj {
    // Sym and Env can have muliple references to the same object.
    Sym(Obe, Arc<Symbol>),
    Env(Obe, Arc<Env>),

    // Pair lists are lisp-style car/cdr pairs of symbol + object.
    // Design question: should these be structures like Sym and Env?
    PairList(Obe, Vec<(Obj, Obj)>),
    Closure(Obe, Vec<(Obj, Obj)>),
    Promise(Obe, Vec<(Obj, Obj)>),
    Lang(Obe, Vec<(Obj, Obj)>),
    Dot(Obe, Vec<(Obj, Obj)>),

    // These are vectors.
    // Design question: Should these be Arcs?
    Char(Obe, String),
    Ary(Obe, ArrayRef),
    Str(Obe, Vec<String>),
    List(Obe, Vec<Obj>),
    Expr(Obe, Vec<Obj>),

    // Special functions. eg. operators, sin, log etc.
    // Design question: Should these be enums?
    Special(Obe, String),
    Builtin(Obe, String),

    // Special values.
    Nil(Obe),
    Global(Obe),
    Unbound(Obe),
    MissingArg(Obe),
    BaseNamespace(Obe),
    EmptyEnv(Obe),
    BaseEnv(Obe),
}

pub const NA_INTEGER : i32 = -0x80000000;
// Note there is no current way to do this in Rust that I know of.
// (Answers on a postcard).
// pub const NA_REAL : f64 = f64::from_bits(0x7ff0000000000000 + 1954);

/// Extra attributes for an object.
/// These are relatively rare and so have a separate structure.
#[derive(PartialEq, Clone)]
pub struct Extras {
    // Symbol eg. "x"
    pub tag: Obj,

    // PairList of attributes eg. {"x": 1, "y": 2}
    pub attr: Obj,

    //
    pub levels: i32,

    //
    pub is_obj: bool,
}

impl std::fmt::Debug for Extras {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<")?;
        if !self.tag.is_null() {
            write!(f, "tag={:?} ", self.tag)?;
        }
        if !self.attr.is_null() {
            write!(f, "attr={:?} ", self.attr)?;
        }
        if self.levels != 0 {
            write!(f, "levels={} ", self.levels)?;
        }
        if self.is_obj {
            write!(f, "is_obj={} ", self.is_obj)?;
        }
        write!(f, ">")
    }
}


fn _str_hash(s: &str) -> i32 {
    s.as_bytes().iter().fold(0, |h, p| {
        let h = h * 16 + (*p as i8 as i32);
        let g = h & -0x10000000;
        h ^ (g >> 24) ^ g
    })
}

#[derive(PartialEq, Clone)]
pub struct Symbol {
    pub name: String,
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", &self.name)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Env {
    pub locked: bool,
    pub enclos: Obj,
    pub frame: Obj,
    pub keyvals: Vec<(Obj, Obj)>
}

pub type Obe = Option<Box<Extras>>;


#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

macro_rules! make_type {
    ($t: ty, $id: ident) => {
        // Get an ArrayRef from a slice
        impl From<&[$t]> for ArrayRef {
            fn from(val: &[$t]) -> ArrayRef {
                ArrayRef(Arc::new(PrimArray::<$t>{ data: Vec::from(val), elem_type: Type::$id }))
            }
        }

        // Get an Obj from a slice
        impl From<&[$t]> for Obj {
            fn from(val: &[$t]) -> Obj {
                Obj::Ary(None, ArrayRef::from(val))
            }
        }

        // Get an Obj from a vector
        impl From<Vec<$t>> for Obj {
            fn from(val: Vec<$t>) -> Obj {
                Obj::Ary(None, ArrayRef::from(val.as_slice()))
            }
        }
    }
}

make_type!(bool, Bool);
make_type!(i8, I8);
make_type!(i16, I16);
make_type!(i32, I32);
make_type!(i64, I64);
make_type!(u8, U8);
make_type!(u16, U16);
make_type!(u32, U32);
make_type!(u64, U64);
make_type!(f32, F32);
make_type!(f64, F64);

// A bucket of bits on the heap.
struct PrimArray<T> {
    data: Vec<T>,
    elem_type: Type,
}

struct _StringArray<'a> {
    data: Vec<&'a str>,
    len: usize,
    elem_type: Type,
    text: Vec<u8>,
}

struct _BoolArray {
    data: Vec<u8>,
    len: usize,
    elem_type: Type,
    nulls: Vec<u8>,
}

// An arbitrary vector of elements.
// This could be heap allocated, memory mapped, RDMA shared or some other source of bytes
// such as apache arrow.
pub trait Array {
    // Use this to dynamically downcast the Array.
    fn as_any(&self) -> &dyn Any;

    // Number of elements
    fn len(&self) -> usize;

    // Type of the contained element
    fn elem_type(&self) -> Type;

    // Return a pointer to the data or NULL if unavailable.
    fn as_ptr(&self) -> * const u8;

    // Return a writable pointer to the data or NULL if unavailable.
    fn as_mut_ptr(&mut self) -> * mut u8;
}

impl<T : 'static> Array for PrimArray<T> {
    fn as_any(&self) -> &dyn Any {
        self as &dyn Any
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }

    fn elem_type(&self) -> Type {
        self.elem_type.clone()
    }

    fn as_ptr(&self) -> * const u8 {
        self.data.as_ptr() as * const u8
    }

    fn as_mut_ptr(&mut self) -> * mut u8 {
        self.data.as_mut_ptr() as * mut u8
    }
 }

#[derive(Clone)]
pub struct ArrayRef(Arc<dyn Array>);

impl PartialEq for ArrayRef {
    fn eq(&self, other: &ArrayRef) -> bool {
        // TODO: check elements
        self.elem_type() == other.elem_type() && self.len() == other.len()
    }
}

// This will expose the Array interface to ArrayRef.
impl std::ops::Deref for ArrayRef {
    type Target = dyn Array;

    fn deref(&self) -> &Self::Target {
        return self.0.deref();
    }
}

impl std::fmt::Debug for ArrayRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ArrayRef[{} x {:?}]", self.len(), self.elem_type())?;
        Ok(())
    }
}

// Call a function with a template parameter of the correct type
// for an ArrayRef.
#[macro_export]
macro_rules! do_typed {
    ($f : ident, $a : expr) => {
        match $a.elem_type() {
            Type::Bool => $f::<bool>($a),
            Type::I8 => $f::<i8>($a),
            Type::I16 => $f::<i16>($a),
            Type::I32 => $f::<i32>($a),
            Type::I64 => $f::<i64>($a),
            Type::U8 => $f::<u8>($a),
            Type::U16 => $f::<u16>($a),
            Type::U32 => $f::<u32>($a),
            Type::U64 => $f::<u64>($a),
            Type::F32 => $f::<f32>($a),
            Type::F64 => $f::<f64>($a),
        }
    }
}

impl ArrayRef {
    pub fn as_slice<T>(&self) -> Option<&[T]> {
        let ptr = self.0.as_ptr() as * const T;
        if ptr.is_null() {
            None
        } else {
            Some(unsafe { std::slice::from_raw_parts(ptr, self.0.len()) })
        }
    }

    /*pub fn as_mut_slice<T>(&mut self) -> Option<&mut [T]> {
        let ptr = self.as_mut_ptr() as * mut T;
        if ptr.is_null() {
            None
        } else {
            Some(unsafe { std::slice::from_raw_parts_mut(ptr, self.0.len()) })
        }
    }*/

}


// Conversion
impl From<()> for Obj {
    fn from(_: ()) -> Obj {
       Obj::Nil(None)
    }
}

impl From<&String> for Obj {
    fn from(val: &String) -> Obj {
       Obj::Str(None, vec![val.clone()])
    }
}

impl From<String> for Obj {
    fn from(val: String) -> Obj {
       Obj::Str(None, vec![val])
    }
}

impl From<&str> for Obj {
    fn from(val: &str) -> Obj {
       Obj::Str(None, vec![val.to_string()])
    }
}

impl From<&[&str]> for Obj {
    fn from(val: &[&str]) -> Obj {
        let strings : Vec<_> = val.iter().map(|s| s.to_string()).collect();
        Obj::Str(None, strings)
    }
}

impl From<Vec<&str>> for Obj {
    fn from(val: Vec<&str>) -> Obj {
        let strings : Vec<_> = val.iter().map(|s| s.to_string()).collect();
        Obj::Str(None, strings)
    }
}

impl From<Vec<(Obj, Obj)>> for Obj {
    fn from(val: Vec<(Obj, Obj)>) -> Obj {
       Obj::PairList(None, val)
    }
}

impl From<Vec<Obj>> for Obj {
    fn from(val: Vec<Obj>) -> Obj {
       Obj::List(None, val)
    }
}

impl From<bool> for Obj {
    fn from(val: bool) -> Obj {
        Obj::from(vec![val])
    }
}

impl From<i32> for Obj {
    fn from(val: i32) -> Obj {
        Obj::from(vec![val])
    }
}

impl From<f64> for Obj {
    fn from(val: f64) -> Obj {
        Obj::from(vec![val])
    }
}

impl PartialEq<&str> for Obj {
    fn eq(&self, rhs: &&str) -> bool {
        if let Obj::Str(_, ref val) = self {
            val.len() == 1 && &val[0] == rhs
        } else {
            false
        }
    }
}

pub trait ToChars {
    fn to_chars(&self, v: &mut Vec<u8>);
}

macro_rules! to_chars {
    ($t : ty) => {
        impl ToChars for $t {
            fn to_chars(&self, v: &mut Vec<u8>) {
                v.extend(self.to_string().as_bytes());
                v.push(b'L');
            }
        }
    }
}

to_chars!(i8);
to_chars!(i16);
to_chars!(i64);
to_chars!(u8);
to_chars!(u16);
to_chars!(u32);
to_chars!(u64);
to_chars!(f32);

impl ToChars for i32 {
    fn to_chars(&self, v: &mut Vec<u8>) {
        if self == &NA_INTEGER {
            v.extend(b"NA");
        } else {
            // TODO: use itoa
            v.extend(self.to_string().as_bytes());
            v.push(b'L');
        }
    }
}

impl ToChars for f64 {
    fn to_chars(&self, v: &mut Vec<u8>) {
        match self.to_bits() {
            0x7ff00000000007a2 => {
                v.extend(b"NA");
            }
            0x7ff0000000000001 | 0x7ff8000000000000 => {
                v.extend(b"Nan");
            }
            0x7ff0000000000000 => {
                v.extend(b"Inf");
            }
            0xfff0000000000000 => {
                v.extend(b"-Inf");
            }
            _ => {
                v.extend(self.to_string().as_bytes());
            }
        }
    }
}

impl ToChars for String {
    fn to_chars(&self, v: &mut Vec<u8>) {
        v.push(b'\"');
        for ch in self.bytes() {
            // TODO: do escapes
            v.push(ch);
        }
        v.push(b'\"');
    }
}

impl ToChars for Obj {
    fn to_chars(&self, v: &mut Vec<u8>) {
        v.extend(b"list");
    }
}

impl ToChars for bool {
    fn to_chars(&self, v: &mut Vec<u8>) {
        if *self {v.extend(b"TRUE")} else {v.extend(b"FALSE")}
    }
}

impl std::fmt::Debug for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let extras = self.extras();
        if let Some(ref extras) = extras {
            write!(f, "{:?}:", extras)?;
        }
        match self {
            Obj::Sym(_, ref val) => write!(f, "Sym({:?})", val),
            Obj::Env(_, ref val) => write!(f, "Env({:?})", val),
            Obj::PairList(_, ref val) => write!(f, "PairList({:?})", val),
            Obj::Closure(_, ref val) => write!(f, "Closure({:?})", val),
            Obj::Promise(_, ref val) => write!(f, "Promise({:?})", val),
            Obj::Lang(_, ref val) => write!(f, "Lang({:?})", val),
            Obj::Dot(_, ref val) => write!(f, "Dot({:?})", val),
            Obj::Special(_, ref val) => write!(f, "Special({:?})", val),
            Obj::Builtin(_, ref val) => write!(f, "Builtin({:?})", val),
            Obj::Ary(_, ref val) => write!(f, "Ary({:?})", val),
            Obj::Char(_, ref val) => write!(f, "Char({:?})", val),
            Obj::Str(_, ref val) => write!(f, "Str({:?})", val),
            Obj::List(_, ref val) => write!(f, "Obj({:?})", val),
            Obj::Expr(_, ref val) => write!(f, "Expr({:?})", val),
            Obj::Nil(_) => write!(f, "Nil()"),
            Obj::Global(_) => write!(f, "Global()"),
            Obj::Unbound(_) => write!(f, "Unbound()"),
            Obj::MissingArg(_) => write!(f, "MissingArg()"),
            Obj::BaseNamespace(_) => write!(f, "BaseNamespace()"),
            Obj::EmptyEnv(_) => write!(f, "EmptyEnv()"),
            Obj::BaseEnv(_) => write!(f, "BaseEnv()"),
        }
    }
}

impl Obj {
    pub fn named_list(names: Vec<&str>, objects: Vec<Obj>) -> Obj {
        let mut root = Obj::null();
        for (n, o) in names.into_iter().zip(objects.into_iter()) {
            root.append_to_list(n, o);
        }
        root
    }

    pub fn append_to_list(&mut self, name: &str, object: Obj) {
        match self {
            Obj::PairList(_, ref mut list)
            | Obj::Closure(_, ref mut list)
            | Obj::Promise(_, ref mut list)
            | Obj::Lang(_, ref mut list)
            | Obj::Dot(_, ref mut list) => {
                list.push((Obj::sym(name), object))
            }
            _ => ()
        }
    }

    pub fn is_null(&self) -> bool {
        match self {
            Obj::Nil(_) => true,
            _ => false,
        }
    }

    pub fn null() -> Self {
        Obj::Nil(None)
    }

    pub fn chars(chrs: &str) -> Self {
        Obj::Char(None, chrs.to_string())
    }

    pub fn sym(chrs: &str) -> Self {
        Obj::Sym(None, Arc::new(Symbol { name: chrs.to_string() }))
    }

    pub fn lang(vals: Vec<Obj>) -> Self {
        Obj::Lang(None, vals.into_iter().map(|x| (Obj::null(), x)).collect())
    }

    pub fn expr(vals: Vec<Obj>) -> Self {
        Obj::Expr(None, vals)
    }

    pub fn env(
        locked: bool,
        enclos: Obj,
        frame: Obj,
        keyvals: Vec<(Obj, Obj)>
    ) -> Obj {
        let env = Env {
            locked,
            enclos,
            frame,
            keyvals
        };

        Obj::Env(None, Arc::new(env))
    }

    pub fn extras_mut(&mut self) -> &mut Obe {
        match self {
            Obj::Sym(ref mut obe, _)
            | Obj::Env(ref mut obe, _)
            | Obj::PairList(ref mut obe, _)
            | Obj::Closure(ref mut obe, _)
            | Obj::Promise(ref mut obe, _)
            | Obj::Lang(ref mut obe, _)
            | Obj::Dot(ref mut obe, _)
            | Obj::Special(ref mut obe, _)
            | Obj::Builtin(ref mut obe, _)
            | Obj::Char(ref mut obe, _)
            | Obj::Ary(ref mut obe, _)
            | Obj::Str(ref mut obe, _)
            | Obj::List(ref mut obe, _)
            | Obj::Expr(ref mut obe, _)
            | Obj::Nil(ref mut obe)
            | Obj::Global(ref mut obe)
            | Obj::Unbound(ref mut obe)
            | Obj::MissingArg(ref mut obe)
            | Obj::BaseNamespace(ref mut obe)
            | Obj::EmptyEnv(ref mut obe)
            | Obj::BaseEnv(ref mut obe) => obe,
        }
    }

    pub fn extras(&self) -> &Obe {
        match self {
            Obj::Sym(ref obe, _)
            | Obj::Env(ref obe, _)
            | Obj::PairList(ref obe, _)
            | Obj::Closure(ref obe, _)
            | Obj::Promise(ref obe, _)
            | Obj::Lang(ref obe, _)
            | Obj::Dot(ref obe, _)
            | Obj::Special(ref obe, _)
            | Obj::Builtin(ref obe, _)
            | Obj::Char(ref obe, _)
            | Obj::Ary(ref obe, _)
            | Obj::Str(ref obe, _)
            | Obj::List(ref obe, _)
            | Obj::Expr(ref obe, _)
            | Obj::Nil(ref obe)
            | Obj::Global(ref obe)
            | Obj::Unbound(ref obe)
            | Obj::MissingArg(ref obe)
            | Obj::BaseNamespace(ref obe)
            | Obj::EmptyEnv(ref obe)
            | Obj::BaseEnv(ref obe) => obe,
        }
    }

    pub fn names(mut self, val: Vec<String>) -> Self {
        self.add_attr("names", Obj::Str(None, val));
        self
    }

    pub fn add_attr<T : Into<Obj>>(&mut self, name: &str, object: T) {
        let extras = self.extras_mut();
        if extras.is_none() {
            *extras = Extras::obe();
        }

        if let Some(ref mut extras) = extras {
            if extras.attr.is_null() {
                extras.attr = Obj::PairList(None, Vec::new());
            }
            extras.attr.append_to_list(name, object.into());
        }
    }

    pub fn set_is_obj(&mut self, is_obj: bool) {
        let extras = self.extras_mut();
        if extras.is_none() {
            *extras = Extras::obe();
        }
        if let Some(ref mut extras) = self.extras_mut() {
            extras.is_obj = is_obj;
        }
    }

    pub fn data_frame(columns: Vec<Obj>, names: Vec<&str>) -> Self {
        let cmax = columns.iter().map(|c| c.len()).max().unwrap_or(1);
        let n: i32 = i32::from_usize(cmax).unwrap_or(1);
        let mut res = Obj::List(None, columns);
        res.add_attr("names", Obj::from(names));
        res.add_attr("row.names", Obj::from(vec![-2147483648, -(n as i32)]));
        res.add_attr("class", Obj::from(vec!["data.frame"]));
        res.set_is_obj(true);
        res
    }

    pub fn len(&self) -> usize {
        match self {
            Obj::Ary(_, ary) => ary.len(),
            Obj::Str(_, vec) => vec.len(),
            Obj::List(_, vec) => vec.len(),
            Obj::Expr(_, vec) => vec.len(),
            _ => 0,
        }
    }

    pub fn tag(&self) -> &Obj {
        match self.extras() {
            Some(ref extra) => &extra.tag,
            None => &Obj::Nil(None)
        }
    }

    // TODO: implment the c! macro flattening for nested vectors.
    pub fn flatten(self) -> Self {
        self
    }
}

impl Extras {
    pub fn new() -> Self {
        Extras {
            attr: Obj::null(),
            tag: Obj::null(),
            levels: 0,
            is_obj: false,
        }
    }

    pub fn obe() -> Option<Box<Self>> {
        Some(Box::new(Extras::new()))
    }
}


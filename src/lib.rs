use num_traits::FromPrimitive;
use std::rc::Rc;

mod reader;

pub use reader::Reader;

// see https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h
// http://www.maths.lth.se/matstat/staff/nader/stint/R_Manuals/R-ints.pdf
// https://github.com/wch/r-source/blob/trunk/src/main/serialize.c


pub type Error = Box<dyn std::error::Error>;
pub type Result<T> = std::result::Result<T, Error>;

#[derive(PartialEq, Clone)]
pub struct Extras {
    // Symbol eg. "x"
    tag: Obj,

    // List of attributes eg. {"x": 1, "y": 2}
    attr: Obj,

    //
    levels: i32,

    //
    is_obj: bool,
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
    name: String,
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", &self.name)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Env {
    locked: bool,
    enclos: Obj,
    frame: Obj,
    keyvals: Vec<(Obj, Obj)>
}

type Obe = Option<Box<Extras>>;

/// An idiomatic representation of an R object.
#[derive(PartialEq, Clone)]
pub enum Obj {
    // Sym and Env can have muliple referencs to the same object.
    Sym(Obe, Rc<Symbol>),
    Env(Obe, Rc<Env>),

    // Lists are lisp-style car/cdr pairs.
    List(Obe, Vec<(Obj, Obj)>),
    Closure(Obe, Vec<(Obj, Obj)>),
    Promise(Obe, Vec<(Obj, Obj)>),
    Lang(Obe, Vec<(Obj, Obj)>),
    Dot(Obe, Vec<(Obj, Obj)>),

    // These are vectors.
    Char(Obe, String),
    Logical(Obe, Vec<bool>),
    Int(Obe, Vec<i32>),
    Real(Obe, Vec<f64>),
    Cplx(Obe, Vec<(f64, f64)>),
    Str(Obe, Vec<Obj>),
    Obj(Obe, Vec<Obj>),
    Expr(Obe, Vec<Obj>),
    Raw(Obe, Vec<u8>),

    // Special functions.
    Special(Obe, String),
    Builtin(Obe, String),

    // Yet to be done.
    Bytecode(Obe),
    ExtPtr(Obe),
    WeakRef(Obe),
    S4(Obe),
    New(Obe),
    Free(Obe),

    // Special values.
    Nil(Obe),
    Global(Obe),
    Unbound(Obe),
    MissingArg(Obe),
    BaseNamespace(Obe),
    EmptyEnv(Obe),
    BaseEnv(Obe),
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
            Obj::List(_, ref val) => write!(f, "List({:?})", val),
            Obj::Closure(_, ref val) => write!(f, "Closure({:?})", val),
            Obj::Promise(_, ref val) => write!(f, "Promise({:?})", val),
            Obj::Lang(_, ref val) => write!(f, "Lang({:?})", val),
            Obj::Dot(_, ref val) => write!(f, "Dot({:?})", val),
            Obj::Special(_, ref val) => write!(f, "Special({:?})", val),
            Obj::Builtin(_, ref val) => write!(f, "Builtin({:?})", val),
            Obj::Char(_, ref val) => write!(f, "Char({:?})", val),
            Obj::Logical(_, ref val) => write!(f, "Logical({:?})", val),
            Obj::Int(_, ref val) => write!(f, "Int({:?})", val),
            Obj::Real(_, ref val) => write!(f, "Real({:?})", val),
            Obj::Cplx(_, ref val) => write!(f, "Cplx({:?})", val),
            Obj::Str(_, ref val) => write!(f, "Str({:?})", val),
            Obj::Obj(_, ref val) => write!(f, "Obj({:?})", val),
            Obj::Expr(_, ref val) => write!(f, "Expr({:?})", val),
            Obj::Raw(_, ref val) => write!(f, "Raw({:?})", val),
            Obj::Bytecode(_) => write!(f, "Bytecode()"),
            Obj::ExtPtr(_) => write!(f, "ExtPtr()"),
            Obj::WeakRef(_) => write!(f, "WeakRef()"),
            Obj::S4(_) => write!(f, "S4()"),
            Obj::New(_) => write!(f, "New()"),
            Obj::Free(_) => write!(f, "Free()"),
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
            Obj::List(_, ref mut list)
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

    pub fn strings(strs: Vec<&str>) -> Self {
        Obj::Str(
            None,
            strs.into_iter()
                .map(|s| Obj::chars(s))
                .collect::<Vec<Obj>>(),
        )
    }

    pub fn sym(chrs: &str) -> Self {
        Obj::Sym(None, Rc::new(Symbol { name: chrs.to_string() }))
    }

    pub fn real(vals: Vec<f64>) -> Self {
        Obj::Real(None, vals)
    }

    pub fn integer(vals: Vec<i32>) -> Self {
        Obj::Int(None, vals)
    }

    pub fn vec(vals: Vec<Obj>) -> Self {
        Obj::Obj(None, vals)
    }

    pub fn raw(vals: Vec<u8>) -> Self {
        Obj::Raw(None, vals)
    }

    pub fn func() -> Self {
        Obj::null()
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

        Obj::Env(None, Rc::new(env))
    }

    pub fn extras_mut(&mut self) -> &mut Obe {
        match self {
            Obj::Sym(ref mut obe, _)
            | Obj::Env(ref mut obe, _)
            | Obj::List(ref mut obe, _)
            | Obj::Closure(ref mut obe, _)
            | Obj::Promise(ref mut obe, _)
            | Obj::Lang(ref mut obe, _)
            | Obj::Dot(ref mut obe, _)
            | Obj::Special(ref mut obe, _)
            | Obj::Builtin(ref mut obe, _)
            | Obj::Char(ref mut obe, _)
            | Obj::Logical(ref mut obe, _)
            | Obj::Int(ref mut obe, _)
            | Obj::Real(ref mut obe, _)
            | Obj::Cplx(ref mut obe, _)
            | Obj::Str(ref mut obe, _)
            | Obj::Obj(ref mut obe, _)
            | Obj::Expr(ref mut obe, _)
            | Obj::Bytecode(ref mut obe)
            | Obj::ExtPtr(ref mut obe)
            | Obj::WeakRef(ref mut obe)
            | Obj::Raw(ref mut obe, _)
            | Obj::S4(ref mut obe)
            | Obj::New(ref mut obe)
            | Obj::Free(ref mut obe)
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
            | Obj::List(ref obe, _)
            | Obj::Closure(ref obe, _)
            | Obj::Promise(ref obe, _)
            | Obj::Lang(ref obe, _)
            | Obj::Dot(ref obe, _)
            | Obj::Special(ref obe, _)
            | Obj::Builtin(ref obe, _)
            | Obj::Char(ref obe, _)
            | Obj::Logical(ref obe, _)
            | Obj::Int(ref obe, _)
            | Obj::Real(ref obe, _)
            | Obj::Cplx(ref obe, _)
            | Obj::Str(ref obe, _)
            | Obj::Obj(ref obe, _)
            | Obj::Expr(ref obe, _)
            | Obj::Bytecode(ref obe)
            | Obj::ExtPtr(ref obe)
            | Obj::WeakRef(ref obe)
            | Obj::Raw(ref obe, _)
            | Obj::S4(ref obe)
            | Obj::New(ref obe)
            | Obj::Free(ref obe)
            | Obj::Nil(ref obe)
            | Obj::Global(ref obe)
            | Obj::Unbound(ref obe)
            | Obj::MissingArg(ref obe)
            | Obj::BaseNamespace(ref obe)
            | Obj::EmptyEnv(ref obe)
            | Obj::BaseEnv(ref obe) => obe,
        }
    }

    pub fn add_attr(&mut self, name: &str, object: Obj) {
        let extras = self.extras_mut();
        if extras.is_none() {
            *extras = Extras::obe();
        }

        if let Some(ref mut extras) = extras {
            if extras.attr.is_null() {
                extras.attr = Obj::List(None, Vec::new());
            }
            extras.attr.append_to_list(name, object);
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
        let mut res = Obj::vec(columns);
        res.add_attr("names", Obj::strings(names));
        res.add_attr("row.names", Obj::integer(vec![-2147483648, -(n as i32)]));
        res.add_attr("class", Obj::strings(vec!["data.frame"]));
        res.set_is_obj(true);
        res
    }

    pub fn len(&self) -> usize {
        match self {
            Obj::Logical(_, vec) => vec.len(),
            Obj::Int(_, vec) => vec.len(),
            Obj::Real(_, vec) => vec.len(),
            Obj::Cplx(_, vec) => vec.len(),
            Obj::Str(_, vec) => vec.len(),
            Obj::Obj(_, vec) => vec.len(),
            Obj::Expr(_, vec) => vec.len(),
            Obj::Raw(_, vec) => vec.len(),
            _ => 0,
        }
    }

    pub fn tag(&self) -> &Obj {
        match self.extras() {
            Some(ref extra) => &extra.tag,
            None => &Obj::Nil(None)
        }
    }
}

impl Extras {
    fn new() -> Self {
        Extras {
            attr: Obj::null(),
            tag: Obj::null(),
            levels: 0,
            is_obj: false,
        }
    }

    fn obe() -> Option<Box<Self>> {
        Some(Box::new(Extras::new()))
    }
}


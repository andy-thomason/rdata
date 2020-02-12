use num_traits::FromPrimitive;
use std::io::Read;
use std::rc::Rc;

// see https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h
// http://www.maths.lth.se/matstat/staff/nader/stint/R_Manuals/R-ints.pdf
// https://github.com/wch/r-source/blob/trunk/src/main/serialize.c

pub struct Reader<R: Read> {
    buf: String,
    src: R,
    refs: Vec<Object>,
    is_ascii: bool,
}

pub type Error = Box<dyn std::error::Error>;
pub type Result<T> = std::result::Result<T, Error>;

#[derive(PartialEq, Debug, Clone)]
pub struct Extras {
    // Symbol eg. "x"
    tag: Object,

    // List of attributes eg. {"x": 1, "y": 2}
    attr: Object,

    //
    levels: i32,

    //
    is_obj: bool,
}

#[derive(PartialEq, Debug, Clone)]
/// See https://en.wikipedia.org/wiki/CAR_and_CDR
/// (could we use a vector here instead?)
pub struct List {
    // Contents of a list node
    car: Object,

    // Rest of the list.
    cdr: Object,
}

impl List {
    pub fn from_slice(slice: &[Object]) -> Self {
        let next = if slice.len() <= 1 {
            Object::null()
        } else {
            Object::List(None, Rc::new(List::from_slice(&slice[1..])))
        };
        List {
            car: slice[0].clone(),
            cdr: next,
        }
    }

    // Call cb for each element of a list.
    /*pub fn for_each<T : Fn(&Object)>(&self, cb: T) {
        cb(&self.car);
        self.cdr.for_each(cb);
    }*/
}

fn _str_hash(s: &str) -> i32 {
    s.as_bytes().iter().fold(0, |h, p| {
        let h = h * 16 + (*p as i8 as i32);
        let g = h & -0x10000000;
        h ^ (g >> 24) ^ g
    })
}

#[derive(PartialEq, Debug, Clone)]
pub struct Symbol {
    name: String,
}

#[derive(PartialEq, Debug, Clone)]
pub struct Env {
    locked: bool,
    enclos: Object,
    frame: Object,
    keyvals: Vec<(Object, Object)>
}

type Obe = Option<Box<Extras>>;

/// An idiomatic representation of an R object.
#[derive(PartialEq, Debug, Clone)]
pub enum Object {
    // Sym and Env can have muliple referencs to the same object.
    Sym(Obe, Rc<Symbol>),
    Env(Obe, Rc<Env>),

    // Lists are lisp-style car/cdr pairs.
    List(Obe, Rc<List>),
    Closure(Obe, Rc<List>),
    Promise(Obe, Rc<List>),
    Lang(Obe, Rc<List>),
    Dot(Obe, Rc<List>),

    // These are vectors.
    Char(Obe, String),
    Logical(Obe, Vec<bool>),
    Int(Obe, Vec<i32>),
    Real(Obe, Vec<f64>),
    Cplx(Obe, Vec<(f64, f64)>),
    Str(Obe, Vec<Object>),
    Obj(Obe, Vec<Object>),
    Expr(Obe, Vec<Object>),
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

impl Object {
    pub fn named_list(names: Vec<&str>, objects: Vec<Object>) -> Object {
        let mut root = Object::null();
        for (n, o) in names.into_iter().zip(objects.into_iter()) {
            root.append_to_list(n, o);
        }
        root
    }

    pub fn append_to_list(&mut self, name: &str, object: Object) {
        let mut new_list = List {
            car: object,
            cdr: Object::Nil(None),
        };
        let mut e = Extras::new();
        e.tag = Object::sym(name);
        std::mem::swap(&mut new_list.cdr, self);
        *self = Object::List(Some(Box::new(e)), Rc::new(new_list))
    }

    pub fn is_null(&self) -> bool {
        match self {
            Object::Nil(_) => true,
            _ => false,
        }
    }

    pub fn null() -> Self {
        Object::Nil(None)
    }

    pub fn chars(chrs: &str) -> Self {
        Object::Char(None, chrs.to_string())
    }

    pub fn strings(strs: Vec<&str>) -> Self {
        Object::Str(
            None,
            strs.into_iter()
                .map(|s| Object::chars(s))
                .collect::<Vec<Object>>(),
        )
    }

    pub fn sym(chrs: &str) -> Self {
        Object::Sym(None, Rc::new(Symbol { name: chrs.to_string() }))
    }

    pub fn real(vals: Vec<f64>) -> Self {
        Object::Real(None, vals)
    }

    pub fn integer(vals: Vec<i32>) -> Self {
        Object::Int(None, vals)
    }

    pub fn vec(vals: Vec<Object>) -> Self {
        Object::Obj(None, vals)
    }

    pub fn raw(vals: Vec<u8>) -> Self {
        Object::Raw(None, vals)
    }

    pub fn func() -> Self {
        Object::null()
    }

    pub fn lang(vals: Vec<Object>) -> Self {
        Object::Lang(None, Rc::new(List::from_slice(vals.as_slice())))
    }

    pub fn expr(vals: Vec<Object>) -> Self {
        Object::Expr(None, vals)
    }

    pub fn env(
        locked: bool,
        enclos: Object,
        frame: Object,
        keyvals: Vec<(Object, Object)>
    ) -> Object {
        let env = Env {
            locked,
            enclos,
            frame,
            keyvals
        };

        Object::Env(None, Rc::new(env))
    }

    pub fn extras_mut(&mut self) -> &mut Obe {
        match self {
            Object::Sym(ref mut obe, _)
            | Object::Env(ref mut obe, _)
            | Object::List(ref mut obe, _)
            | Object::Closure(ref mut obe, _)
            | Object::Promise(ref mut obe, _)
            | Object::Lang(ref mut obe, _)
            | Object::Dot(ref mut obe, _)
            | Object::Special(ref mut obe, _)
            | Object::Builtin(ref mut obe, _)
            | Object::Char(ref mut obe, _)
            | Object::Logical(ref mut obe, _)
            | Object::Int(ref mut obe, _)
            | Object::Real(ref mut obe, _)
            | Object::Cplx(ref mut obe, _)
            | Object::Str(ref mut obe, _)
            | Object::Obj(ref mut obe, _)
            | Object::Expr(ref mut obe, _)
            | Object::Bytecode(ref mut obe)
            | Object::ExtPtr(ref mut obe)
            | Object::WeakRef(ref mut obe)
            | Object::Raw(ref mut obe, _)
            | Object::S4(ref mut obe)
            | Object::New(ref mut obe)
            | Object::Free(ref mut obe)
            | Object::Nil(ref mut obe)
            | Object::Global(ref mut obe)
            | Object::Unbound(ref mut obe)
            | Object::MissingArg(ref mut obe)
            | Object::BaseNamespace(ref mut obe)
            | Object::EmptyEnv(ref mut obe)
            | Object::BaseEnv(ref mut obe) => obe,
        }
    }

    pub fn extras(&self) -> &Obe {
        match self {
            Object::Sym(ref obe, _)
            | Object::Env(ref obe, _)
            | Object::List(ref obe, _)
            | Object::Closure(ref obe, _)
            | Object::Promise(ref obe, _)
            | Object::Lang(ref obe, _)
            | Object::Dot(ref obe, _)
            | Object::Special(ref obe, _)
            | Object::Builtin(ref obe, _)
            | Object::Char(ref obe, _)
            | Object::Logical(ref obe, _)
            | Object::Int(ref obe, _)
            | Object::Real(ref obe, _)
            | Object::Cplx(ref obe, _)
            | Object::Str(ref obe, _)
            | Object::Obj(ref obe, _)
            | Object::Expr(ref obe, _)
            | Object::Bytecode(ref obe)
            | Object::ExtPtr(ref obe)
            | Object::WeakRef(ref obe)
            | Object::Raw(ref obe, _)
            | Object::S4(ref obe)
            | Object::New(ref obe)
            | Object::Free(ref obe)
            | Object::Nil(ref obe)
            | Object::Global(ref obe)
            | Object::Unbound(ref obe)
            | Object::MissingArg(ref obe)
            | Object::BaseNamespace(ref obe)
            | Object::EmptyEnv(ref obe)
            | Object::BaseEnv(ref obe) => obe,
        }
    }

    pub fn add_attr(&mut self, name: &str, object: Object) {
        let extras = self.extras_mut();
        if extras.is_none() {
            *extras = Extras::obe();
        }

        if let Some(ref mut extras) = extras {
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

    pub fn data_frame(columns: Vec<Object>, names: Vec<&str>) -> Self {
        let cmax = columns.iter().map(|c| c.len()).max().unwrap_or(1);
        let n: i32 = i32::from_usize(cmax).unwrap_or(1);
        let mut res = Object::vec(columns);
        res.add_attr("class", Object::strings(vec!["data.frame"]));
        res.add_attr("row.names", Object::integer(vec![-2147483648, -(n as i32)]));
        res.add_attr("names", Object::strings(names));
        res.set_is_obj(true);
        res
    }

    pub fn len(&self) -> usize {
        match self {
            Object::Logical(_, vec) => vec.len(),
            Object::Int(_, vec) => vec.len(),
            Object::Real(_, vec) => vec.len(),
            Object::Cplx(_, vec) => vec.len(),
            Object::Str(_, vec) => vec.len(),
            Object::Obj(_, vec) => vec.len(),
            Object::Expr(_, vec) => vec.len(),
            Object::Raw(_, vec) => vec.len(),
            _ => 0,
        }
    }
}

impl Extras {
    fn new() -> Self {
        Extras {
            attr: Object::null(),
            tag: Object::null(),
            levels: 0,
            is_obj: false,
        }
    }

    fn obe() -> Option<Box<Self>> {
        Some(Box::new(Extras::new()))
    }
}

impl<R: Read> Reader<R> {
    pub fn try_new(src: R) -> Result<Self> {
        let mut res = Self {
            buf: String::new(),
            src,
            refs: Vec::new(),
            is_ascii: false,
        };
        let buf = &mut [0; 2];
        res.src.read_exact(&mut buf[..])?;

        if buf == b"RD" {
            let buf3 = &mut [0; 3];
            res.src.read_exact(&mut buf3[..])?;
            if buf3 != b"A2 " && buf3 != b"A2\n" {
                return Err(Error::from("not an R file"));
            }
            res.src.read_exact(&mut buf[..])?;
        }

        if buf == b"A\n" || buf == b"A " {
            res.is_ascii = true;
        } else if buf == b"B\n" || buf == b"X\n" {
            res.is_ascii = false;
        } else {
            return Err(Error::from("not an R file"));
        }

        let version = res.integer()?;
        let _writer_version = res.integer()?;
        let _min_reader_version = res.integer()?;

        if version != 2 {
            return Err(Error::from("only version 2 supported"));
        }

        Ok(res)
    }

    pub fn inner(&mut self) -> &mut R {
        &mut self.src
    }

    fn byte(&mut self) -> Result<u8> {
        let mut buf = [0; 1];
        self.src.read(&mut buf)?;
        Ok(buf[0])
    }

    fn word(&mut self) -> Result<()> {
        self.buf.clear();
        let mut ch = self.byte()?;
        loop {
            if ch > b' ' {
                break;
            }
            ch = self.byte()?;
        }
        loop {
            if ch <= b' ' {
                break;
            }
            self.buf.push(ch as char);
            ch = self.byte()?;
        }
        //println!("w={}", self.buf);
        Ok(())
    }

    fn integer(&mut self) -> Result<i32> {
        if self.is_ascii {
            self.word()?;
            if self.buf == "NA" {
                Ok(-0x80000000)
            } else {
                Ok(self.buf.parse::<i32>()?)
            }
        } else {
            let mut buf = [0; 4];
            self.src.read_exact(&mut buf[..])?;
            Ok(i32::from_be_bytes(buf))
        }
    }

    fn real(&mut self) -> Result<f64> {
        if self.is_ascii {
            self.word()?;
            if self.buf == "NA" {
                // Ross's birthday?
                Ok(f64::from_bits(0x7ff0000000000000 + 1954))
            } else if self.buf == "Nan" {
                Ok(std::f64::NAN)
            } else if self.buf == "Inf" {
                Ok(std::f64::INFINITY)
            } else if self.buf == "-Inf" {
                Ok(std::f64::NEG_INFINITY)
            } else {
                Ok(self.buf.parse::<f64>()?)
            }
        } else {
            let mut buf = [0; 8];
            self.src.read_exact(&mut buf[..])?;
            Ok(f64::from_bits(u64::from_be_bytes(buf)))
        }
    }

    fn string(&mut self, length: usize) -> Result<String> {
        self.buf.clear();
        self.buf.reserve_exact(length);
        if self.is_ascii {
            if length != 0 {
                let mut ch = self.byte()?;
                loop {
                    if ch > b' ' {
                        break;
                    }
                    ch = self.byte()?;
                }
                for _ in 0..length {
                    if ch == b'\\' {
                        ch = self.byte()?;
                        let chr = match ch {
                            b'n' => '\n',
                            b't' => '\t',
                            b'v' => 0x0b as char,
                            b'b' => 0x08 as char,
                            b'r' => '\r',
                            b'f' => 0x0c as char,
                            b'a' => 0x07 as char,
                            b'0'..=b'7' => {
                                let mut val = 0;
                                for i in 0..3 {
                                    match ch {
                                        b'0'..=b'7' => {
                                            val = val * 8 + ch - b'0';
                                            if i != 2 {
                                                ch = self.byte()?;
                                            }
                                        }
                                        _ => break,
                                    }
                                }
                                val as char
                            }
                            _ => ch as char,
                        };
                        //println!("chr={:03o}", chr as i32);
                        self.buf.push(chr);
                    } else {
                        //println!("ch={}", ch as char);
                        self.buf.push(ch as char);
                    }
                    ch = self.byte()?;
                }
            }
        } else {
            // Only way to resize a string up?
            for _ in 0..length {
                self.buf.push(0 as char)
            }
            self.src.read_exact(unsafe { self.buf.as_bytes_mut() })?;
        }
        Ok(self.buf.clone())
    }

    fn extras(&mut self, has_attr: bool, has_tag: bool, is_obj: bool, levels: i32) -> Result<Obe> {
        if !has_attr && !has_tag && !is_obj && levels == 0 {
            return Ok(None);
        }
        let mut extras = Extras::new();
        if has_attr {
            extras.attr = self.read_object()?;
        }
        if has_tag {
            extras.tag = self.read_object()?;
        }
        extras.is_obj = is_obj;
        extras.levels = levels;
        Ok(Some(Box::new(extras)))
    }

    // LISP-style linked list types.
    fn list_extras(
        &mut self,
        has_attr: bool,
        has_tag: bool,
        is_obj: bool,
        levels: i32,
    ) -> Result<Obe> {
        if !has_attr && !has_tag && !is_obj && levels == 0 {
            return Ok(None);
        }
        let mut extras = Extras::new();
        if has_attr {
            extras.attr = self.read_object()?;
        }
        if has_tag {
            extras.tag = self.read_object()?;
        }
        extras.is_obj = is_obj;
        extras.levels = levels;
        Ok(Some(Box::new(extras)))
    }

    // LISP-style linked list types.
    fn dotted_list(&mut self) -> Result<Rc<List>> {
        Ok(Rc::new(List {
            car: self.read_object()?,
            cdr: self.read_object()?,
        }))
    }


    fn read_ref(&mut self, flags: i32) -> Result<Object> {
        let ref_idx = if (flags >> 8) == 0 {
            self.integer()?
        } else {
            flags >> 8
        };
        //println!("ref={} {:?}", ref_idx, &self.refs[(ref_idx-1) as usize]);
        Ok(self.refs[(ref_idx - 1) as usize].clone())
    }

    pub fn read_object(&mut self) -> Result<Object> {
        let flags = self.integer()?;
        let objtype = flags & 0xff;
        let levels = flags >> 12;
        let is_obj = (flags & 0x100) != 0;
        let has_attr = (flags & 0x200) != 0;
        let has_tag = (flags & 0x400) != 0;
        //println!("t={} lev={} obj={} attr={} tag={}", objtype, levels, is_obj, has_attr, has_tag);

        Ok(match objtype {
            //0 => /*NILSXP*/ Object::NILSXP(None),
            1 =>
            /*Sym*/
            {
                let obj = self.read_object()?;
                let res = match obj {
                    Object::Char(_, s) => Object::sym(s.as_str()),
                    _ => return Err(Error::from("symbol not a string"))
                };
                self.refs.push(res.clone());
                res
            }

            2 =>
            /*List*/
            {
                let extras = self.list_extras(has_attr, has_tag, is_obj, 0)?;
                let list = self.dotted_list()?;
                Object::List(extras, list)
            }
            3 =>
            /*Closure*/
            {
                let extras = self.list_extras(has_attr, has_tag, is_obj, 0)?;
                let list = self.dotted_list()?;
                Object::Closure(extras, list)
            }
            5 =>
            /*Promise*/
            {
                let extras = self.list_extras(has_attr, has_tag, is_obj, 0)?;
                let list = self.dotted_list()?;
                Object::Promise(extras, list)
            }
            6 =>
            /*Lang*/
            {
                let extras = self.list_extras(has_attr, has_tag, is_obj, 0)?;
                let list = self.dotted_list()?;
                Object::Lang(extras, list)
            }
            17 =>
            /*Dot*/
            {
                Object::Dot(
                    self.list_extras(has_attr, has_tag, is_obj, 0)?,
                    self.dotted_list()?,
                )
            }
            4 =>
            /*Env*/
            {
                let locked = self.integer()? != 0;
                let enclos = self.read_object()?;
                let frame = self.read_object()?;
                let _hashtab = self.read_object()?;
                let attr = self.read_object()?;
                let keyvals = Vec::new();
                /*match hashtab {
                    Object::Obj(_, list) => {
                        for obj in list {
                            match obj {
                                Object::List(_, list) => {
                                    list.for_each(|t, v| keyvals.push((t.clone(), v.clone())));
                                }
                            }
                        }
                    }
                };*/
                let res = Object::env(locked, enclos, frame, keyvals);
                if !attr.is_null() {
                    //res.set_attr(attr);
                }
                self.refs.push(res.clone());
                res
            }
            7 =>
            /*Special*/
            {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                Object::Special(None, instr)
            }
            8 =>
            /*Builtin*/
            {
                let length = self.integer()? as usize;
                println!("len={}", length);
                let instr = self.string(length)?;
                println!("instr={}", instr);
                Object::Builtin(None, instr)
            }
            9 =>
            /*CHARSXP*/
            {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                // ignore the levels field for now.
                Object::Char(self.extras(has_attr, has_tag, is_obj, 0)?, instr)
            }
            10 =>
            /*Logical*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()? != 0);
                }
                Object::Logical(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            13 =>
            /*Int*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()?);
                }
                Object::Int(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            14 =>
            /*Real*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.real()?);
                }
                Object::Real(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            15 =>
            /*Cplx*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    let re = self.real()?;
                    let im = self.real()?;
                    data.push((re, im));
                }
                Object::Cplx(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            16 =>
            /*Str*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Object::Str(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            // 18 => /*ANYSXP*/ Object::ANYSXP(),
            19 =>
            /*Vec*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Object::Obj(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            20 =>
            /*Expr*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Object::Expr(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            // 21 => /*Bytecode*/ Object::Bytecode(),
            // 22 => /*ExtPtr*/ Object::ExtPtr(),
            // 23 => /*WeakRef*/ Object::WeakRef(),
            24 =>
            /*Raw*/
            {
                let length = self.integer()? as usize;
                if self.is_ascii {
                    let data: Result<Vec<_>> = (0..length)
                        .map(|_| {
                            self.word()?;
                            Ok(u8::from_str_radix(self.buf.as_str(), 16).unwrap_or(0))
                        })
                        .collect();
                    Object::Raw(self.extras(has_attr, has_tag, is_obj, levels)?, data?)
                } else {
                    let mut data = Vec::with_capacity(length);
                    data.resize(length, 0);
                    self.src.read_exact(data.as_mut_slice())?;
                    Object::Raw(self.extras(has_attr, has_tag, is_obj, levels)?, data)
                }
            }
            // 25 => /*S4*/ Object::S4(),
            // 30 => /*NEWSXP*/ Object::NEWSXP(),
            // 31 => /*FREESXP*/ Object::FREESXP(),
            255 =>
            /*REFSXP*/
            {
                self.read_ref(flags)?
            }
            254 =>
            /*NILVALUE_SXP*/
            {
                Object::Nil(None)
            }
            253 =>
            /*GLOBALENV_SXP*/
            {
                Object::Global(None)
            }
            252 =>
            /*UNBOUNDVALUE_SXP*/
            {
                Object::Unbound(None)
            }
            251 =>
            /*MISSINGARG_SXP*/
            {
                Object::MissingArg(None)
            }
            250 =>
            /*BASENAMESPACE_SXP*/
            {
                Object::BaseNamespace(None)
            }
            // 249 => /*NAMESPACESXP*/ Object::NILSXP,
            // 248 => /*PACKAGESXP*/ Object::NILSXP,
            // 247 => /*PERSISTSXP*/ Object::NILSXP,
            // 246 => /*CLASSREFSXP*/ Object::NILSXP,
            // 245 => /*GENERICREFSXP*/ Object::NILSXP,
            // 244 => /*BCREPDEF*/ Object::NILSXP,
            // 243 => /*BCREPREF*/ Object::NILSXP,
            242 =>
            /*EMPTYENV_SXP*/
            {
                Object::EmptyEnv(None)
            }
            241 =>
            /*BASEENV_SXP*/
            {
                Object::BaseEnv(None)
            }
            _ => Err(Error::from(format!("unsupported R data type {}", objtype)))?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Object;
    use super::Object::*;
    use super::Reader;
    //use std::rc::Rc;

    fn read_ascii(s: &str) -> Object {
        let mut src = Reader::try_new(std::io::Cursor::new(s)).unwrap();
        let res = src.read_object().unwrap();
        assert_eq!(src.inner().position(), src.inner().get_ref().len() as u64);
        res
    }

    fn read_bin(b: &str) -> Object {
        let s: Vec<_> = b
            .as_bytes()
            .chunks_exact(2)
            .map(|b| u8::from_str_radix(unsafe { std::str::from_utf8_unchecked(b) }, 16).unwrap())
            .collect();
        let mut src = Reader::try_new(std::io::Cursor::new(s)).unwrap();
        let res = src.read_object().unwrap();
        assert_eq!(src.inner().position(), src.inner().get_ref().len() as u64);
        res
    }

    #[test]
    fn size() {
        assert_eq!(std::mem::size_of::<Object>(), 40);
        assert_eq!(std::mem::size_of::<super::Obe>(), 8);
    }

    #[test]
    fn int_val() {
        let obj = read_ascii("A 2 197636 131840 13 1 1");
        assert_eq!(obj, Object::Int(None, vec![1]));
    }

    #[test]
    fn real_val() {
        let obj = read_ascii("A 2 197636 131840 14 1 1");
        assert_eq!(obj, Object::Real(None, vec![1.]));
    }

    #[test]
    fn complex_val() {
        let obj = read_ascii("A 2 197636 131840 15 1 1 2");
        assert_eq!(obj, Object::Cplx(None, vec![(1., 2.)]));
    }

    #[test]
    fn null_val() {
        let obj = read_ascii("A 2 197636 131840 254");
        assert_eq!(obj, Object::Nil(None));
    }

    #[test]
    fn bool_val() {
        let obj = read_ascii("A 2 197636 131840 10 2 1 0");
        assert_eq!(obj, Object::Logical(None, vec![true, false]));
    }

    #[test]
    fn sym_val() {
        // Actually a sym (1 262153 1 x) and a ref (511)
        let obj = read_ascii("A 2 197636 131840 19 2 1 262153 1 x 511");
        assert_eq!(
            obj,
            Obj(None, vec![Object::sym("x"), Object::sym("x")])
        );
    }

    #[test]
    fn raw() {
        let obj = read_ascii("A 2 197636 131840 24 10 00 00 00 00 00 00 00 00 00 00");
        assert_eq!(obj, Object::raw(vec![0; 10]))
    }

    #[test]
    fn call_val() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 1 + 2 1 262153 1 x 2 14 1 1 254");
        assert_eq!(
            obj,
            Object::lang(vec![
                Object::sym("+"),
                Object::sym("x"),
                Object::real(vec![1.])
            ])
        );
    }

    #[test]
    fn call_sin_pi() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 3 sin 2 1 262153 2 pi 254");
        assert_eq!(
            obj,
            Object::lang(vec![Object::sym("sin"), Object::sym("pi")])
        );
    }

    #[test]
    fn assign() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 2 <- 2 1 262153 1 x 2 14 1 1 254");
        println!("{:?}", obj);
        assert_eq!(
            obj,
            Object::lang(vec![
                Object::sym("<-"),
                Object::sym("x"),
                Object::real(vec![1.])
            ])
        );
    }

    #[test]
    fn list_val() {
        let obj = read_ascii("A 2 197636 131840 19 1 14 1 1");
        assert_eq!(
            obj,
            Object::Obj(None, vec![Object::Real(None, vec![1.])])
        );
    }

    #[test]
    fn named_list_val() {
        let obj =
            read_ascii("A 2 197636 131840 531 1 14 1 1 1026 1 262153 5 names 16 1 262153 1 a 254");
        let names = Object::strings(vec!["a"]);
        let mut cmp = Object::Obj(None, vec![Object::Real(None, vec![1.])]);
        cmp.add_attr("names", names);
        assert_eq!(obj, cmp);
    }

    #[test]
    fn env() {
        let obj = read_ascii("A 2 197636 131840 4 0 253 254 19 29 254 254 254 254 1026 1 262153 1 x 14 1 1 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254");
        //let mut hashvals = vec![Nil(None); 29];
        //hashvals[4] = Object::named_list(vec!["x"], vec![Object::real(vec![1.])]);
        //let hashtab = Object::vec(hashvals);
        let enclos = Global(None);
        let frame = Object::null();
        let keyvals = vec![(Object::sym("x"), Object::real(vec![1.]))];
        let cmp = Object::env(false, enclos, frame, keyvals);
        assert_eq!(obj, cmp);
    }

    #[test]
    fn attr() {
        let obj = read_ascii("A 2 197636 131840 526 1 1 1026 1 262153 6 attr-x 14 1 2 254");
        let mut cmp = Object::real(vec![1.]);
        cmp.add_attr("attr-x", Object::real(vec![2.]));
        assert_eq!(obj, cmp);
    }

    #[test]
    fn func1() {
        //let obj = read_ascii(r"A 2 197636 131840 1539 1026 1 262153 6 srcref 781 8 1 6 1 18 6 18 1 1 1026 1 262153 7 srcfile 4 0 242 1026 1 262153 5 lines 16 1 262153 19 f\040<-\040function()\040{}\n 1026 1 262153 8 filename 16 1 262153 0 254 254 1026 1 262153 5 class 16 2 262153 11 srcfilecopy 262153 7 srcfile 254 1026 1791 16 1 262153 6 srcref 254 254 253 254 518 1026 511 19 1 781 8 1 17 1 17 17 17 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 1026 767 1023 1026 1 262153 11 wholeSrcref 781 8 1 0 1 18 0 18 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 254 1 262153 1 { 254");
        //println!("{:?}", obj);
        //assert!(false);
        //let cmp = Object::func();
        //assert_eq!(obj, cmp);
    }

    #[test]
    fn func2() {
        //let obj = read_ascii(r#"A 2 197636 131840 1539 1026 1 262153 6 srcref 781 8 1 6 1 26 6 26 1 1 1026 1 262153 7 srcfile 4 0 242 1026 1 262153 5 lines 16 1 262153 27 f\040<-\040function(x)\040{\040x\040+\0401\040}\n 1026 1 262153 8 filename 16 1 262153 0 254 254 1026 1 262153 5 class 16 2 262153 11 srcfilecopy 262153 7 srcfile 254 1026 1791 16 1 262153 6 srcref 254 254 253 1026 1 262153 1 x 251 254 518 1026 511 19 2 781 8 1 18 1 18 18 18 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 781 8 1 20 1 24 20 24 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 1026 767 1023 1026 1 262153 11 wholeSrcref 781 8 1 0 1 26 0 26 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 254 1 262153 1 { 2 6 1 262153 1 + 2 2047 2 14 1 1 254 254"#);
        //let cmp = Object::func();
        //assert_eq!(obj, cmp);
        //println!("{:?}", obj);
        //assert!(false);
    }

    #[test]
    fn data_frame() {
        // data.frame(a=1, b=2)
        let obj = read_ascii(
            r#"A 2 197636 131840 787 2 14 1 1 14 1 2 1026 1 262153 5 names 16 2 262153 1 a 262153 1 b 1026 1 262153 9 row.names 13 2 NA -1 1026 1 262153 5 class 16 1 262153 10 data.frame 254"#,
        );
        let cmp = Object::data_frame(
            vec![Object::real(vec![1.]), Object::real(vec![2.])],
            vec!["a", "b"],
        );
        assert_eq!(obj, cmp);
    }

    #[test]
    fn builtin() {
        // c
        let obj = read_ascii("A 2 197636 131840 8 1 c");
        println!("{:?}", obj);
        assert_eq!(obj, Builtin(None, "c".to_string()));
    }

    #[test]
    fn special() {
        // `<-`
        let obj = read_ascii("A 2 197636 131840 7 2 <-");
        println!("{:?}", obj);
        assert_eq!(obj, Special(None, "<-".to_string()));
    }

    #[test]
    fn expression() {
        // expression(1+1)
        let obj = read_ascii("A 2 197636 131840 20 1 6 1 262153 1 + 2 14 1 1 2 14 1 1 254");
        println!("{:?}", obj);
        assert_eq!(
            obj,
            Object::expr(vec![Object::lang(vec![
                Object::sym("+"),
                Object::real(vec![1.]),
                Object::real(vec![1.])
            ])])
        );
    }

    // #[test]
    // fn rda2() {
    //     let obj = read_ascii(
    //         r"RDA2 A 2 197636 131840 1026 1 262153 2 df 787 2 14 1 1 14 1 2 1026 1 262153 5 names 16 2 262153 1 a 262153 1 b 1026 1 262153 9 row.names 13 2 NA -1 1026 1 262153 5 class 16 1 262153 10 data.frame 254 254",
    //     );
    //     println!("rda2={:?}", obj);
    //     assert_eq!(obj, Nil(None));
    // }

    #[test]
    fn bin() {
        let obj = read_bin("580a0000000200030404000203000000000e000000013ff0000000000000");
        println!("bin={:?}", obj);
        assert_eq!(obj, Real(None, vec![1.0]));
    }
}

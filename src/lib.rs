use num_traits::FromPrimitive;
use std::io::Read;
use std::rc::Rc;

// see https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h
// http://www.maths.lth.se/matstat/staff/nader/stint/R_Manuals/R-ints.pdf
// https://github.com/wch/r-source/blob/trunk/src/main/serialize.c

pub struct Reader<R: Read> {
    buf: String,
    src: R,
    refs: Vec<Obj>,
    is_ascii: bool,
}

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
#[derive(PartialEq, Debug, Clone)]
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

    // These lists are stored in R as lisp-style CAR/CDR pairs.
    // Here we convert this to a vector, avoiding recursion.
    fn dotted_list(
        &mut self,
        has_attr: bool,
        has_tag: bool,
        mut _is_obj: bool,
        mut _levels: i32,
     ) -> Result<Vec<(Obj, Obj)>> {
        let mut res = Vec::new();
        let mut _attr = if !has_attr { Obj::null() } else { self.read_object()? };
        let mut tag = if !has_tag { Obj::null() } else { self.read_object()? };
        //extras.is_obj = is_obj;
        //extras.levels = levels;
        loop {
            let car = self.read_object()?;
            res.push((tag, car));
            let flags = self.integer()?;
            let objtype = flags & 0xff;
            _levels = flags >> 12;
            _is_obj = (flags & 0x100) != 0;
            let has_attr = (flags & 0x200) != 0;
            let has_tag = (flags & 0x400) != 0;
            if objtype == 254 {
                break;
            }
            if objtype != 2 {
                return Err(Error::from("badly formed list"));
            }
            _attr = if !has_attr { Obj::null() } else { self.read_object()? };
            tag = if !has_tag { Obj::null() } else { self.read_object()? };
        }
        Ok(res)
    }

    fn read_ref(&mut self, flags: i32) -> Result<Obj> {
        let ref_idx = if (flags >> 8) == 0 {
            self.integer()?
        } else {
            flags >> 8
        };
        //println!("ref={} {:?}", ref_idx, &self.refs[(ref_idx-1) as usize]);
        Ok(self.refs[(ref_idx - 1) as usize].clone())
    }

    pub fn read_object(&mut self) -> Result<Obj> {
        let flags = self.integer()?;
        self.read_object_with_flags(flags)
    }

    pub fn read_object_with_flags(&mut self, flags: i32) -> Result<Obj> {
        let objtype = flags & 0xff;
        let levels = flags >> 12;
        let is_obj = (flags & 0x100) != 0;
        let has_attr = (flags & 0x200) != 0;
        let has_tag = (flags & 0x400) != 0;
        //println!("t={} lev={} obj={} attr={} tag={}", objtype, levels, is_obj, has_attr, has_tag);

        Ok(match objtype {
            //0 => /*NILSXP*/ Obj::NILSXP(None),
            1 =>
            /*Sym*/
            {
                let obj = self.read_object()?;
                let res = match obj {
                    Obj::Char(_, s) => Obj::sym(s.as_str()),
                    _ => return Err(Error::from("symbol not a string"))
                };
                self.refs.push(res.clone());
                res
            }

            2 =>
            /*List*/
            {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::List(None, list)
            }
            3 =>
            /*Closure*/
            {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::Closure(None, list)
            }
            5 =>
            /*Promise*/
            {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::Promise(None, list)
            }
            6 =>
            /*Lang*/
            {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::Lang(None, list)
            }
            17 =>
            /*Dot*/
            {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::Dot(None, list)
            }
            4 =>
            /*Env*/
            {
                let locked = self.integer()? != 0;
                let enclos = self.read_object()?;
                let frame = self.read_object()?;
                let hashtab = self.read_object()?;
                let attr = self.read_object()?;
                let mut keyvals = Vec::new();
                match hashtab {
                    Obj::Obj(_, list) => {
                        for obj in list {
                            match obj {
                                Obj::List(_, ref list) => {
                                    list.iter().for_each(|(t, v)| keyvals.push((t.clone(), v.clone())));
                                }
                                _ => ()
                            }
                        }
                    }
                    _ => ()
                };
                let res = Obj::env(locked, enclos, frame, keyvals);
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
                Obj::Special(None, instr)
            }
            8 =>
            /*Builtin*/
            {
                let length = self.integer()? as usize;
                println!("len={}", length);
                let instr = self.string(length)?;
                println!("instr={}", instr);
                Obj::Builtin(None, instr)
            }
            9 =>
            /*Char*/
            {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                // ignore the levels field for now.
                Obj::Char(self.extras(has_attr, has_tag, is_obj, 0)?, instr)
            }
            10 =>
            /*Logical*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()? != 0);
                }
                Obj::Logical(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            13 =>
            /*Int*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()?);
                }
                Obj::Int(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            14 =>
            /*Real*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.real()?);
                }
                Obj::Real(self.extras(has_attr, has_tag, is_obj, levels)?, data)
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
                Obj::Cplx(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            16 =>
            /*Str*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Obj::Str(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            // 18 => /*ANYSXP*/ Obj::ANYSXP(),
            19 =>
            /*Vec*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Obj::Obj(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            20 =>
            /*Expr*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Obj::Expr(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            // 21 => /*Bytecode*/ Obj::Bytecode(),
            // 22 => /*ExtPtr*/ Obj::ExtPtr(),
            // 23 => /*WeakRef*/ Obj::WeakRef(),
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
                    Obj::Raw(self.extras(has_attr, has_tag, is_obj, levels)?, data?)
                } else {
                    let mut data = Vec::with_capacity(length);
                    data.resize(length, 0);
                    self.src.read_exact(data.as_mut_slice())?;
                    Obj::Raw(self.extras(has_attr, has_tag, is_obj, levels)?, data)
                }
            }
            // 25 => /*S4*/ Obj::S4(),
            // 30 => /*NEWSXP*/ Obj::NEWSXP(),
            // 31 => /*FREESXP*/ Obj::FREESXP(),
            255 =>
            /*REFSXP*/
            {
                self.read_ref(flags)?
            }
            254 =>
            /*NILVALUE_SXP*/
            {
                Obj::Nil(None)
            }
            253 =>
            /*GLOBALENV_SXP*/
            {
                Obj::Global(None)
            }
            252 =>
            /*UNBOUNDVALUE_SXP*/
            {
                Obj::Unbound(None)
            }
            251 =>
            /*MISSINGARG_SXP*/
            {
                Obj::MissingArg(None)
            }
            250 =>
            /*BASENAMESPACE_SXP*/
            {
                Obj::BaseNamespace(None)
            }
            // 249 => /*NAMESPACESXP*/ Obj::NILSXP,
            // 248 => /*PACKAGESXP*/ Obj::NILSXP,
            // 247 => /*PERSISTSXP*/ Obj::NILSXP,
            // 246 => /*CLASSREFSXP*/ Obj::NILSXP,
            // 245 => /*GENERICREFSXP*/ Obj::NILSXP,
            // 244 => /*BCREPDEF*/ Obj::NILSXP,
            // 243 => /*BCREPREF*/ Obj::NILSXP,
            242 =>
            /*EMPTYENV_SXP*/
            {
                Obj::EmptyEnv(None)
            }
            241 =>
            /*BASEENV_SXP*/
            {
                Obj::BaseEnv(None)
            }
            _ => Err(Error::from(format!("unsupported R data type {}", objtype)))?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Obj;
    use super::Obj::*;
    use super::Reader;

    fn read_ascii(s: &str) -> Obj {
        let mut src = Reader::try_new(std::io::Cursor::new(s)).unwrap();
        let res = src.read_object().unwrap();
        assert_eq!(src.inner().position(), src.inner().get_ref().len() as u64);
        res
    }

    fn read_bin(b: &str) -> Obj {
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
        assert_eq!(std::mem::size_of::<Obj>(), 40);
        assert_eq!(std::mem::size_of::<super::Obe>(), 8);
    }

    #[test]
    fn int_val() {
        let obj = read_ascii("A 2 197636 131840 13 1 1");
        assert_eq!(obj, Obj::Int(None, vec![1]));
    }

    #[test]
    fn real_val() {
        let obj = read_ascii("A 2 197636 131840 14 1 1");
        assert_eq!(obj, Obj::Real(None, vec![1.]));
    }

    #[test]
    fn complex_val() {
        let obj = read_ascii("A 2 197636 131840 15 1 1 2");
        assert_eq!(obj, Obj::Cplx(None, vec![(1., 2.)]));
    }

    #[test]
    fn null_val() {
        let obj = read_ascii("A 2 197636 131840 254");
        assert_eq!(obj, Obj::Nil(None));
    }

    #[test]
    fn bool_val() {
        let obj = read_ascii("A 2 197636 131840 10 2 1 0");
        assert_eq!(obj, Obj::Logical(None, vec![true, false]));
    }

    #[test]
    fn sym_val() {
        // Actually a sym (1 262153 1 x) and a ref (511)
        let obj = read_ascii("A 2 197636 131840 19 2 1 262153 1 x 511");
        assert_eq!(
            obj,
            Obj(None, vec![Obj::sym("x"), Obj::sym("x")])
        );
    }

    #[test]
    fn raw() {
        let obj = read_ascii("A 2 197636 131840 24 10 00 00 00 00 00 00 00 00 00 00");
        assert_eq!(obj, Obj::raw(vec![0; 10]))
    }

    #[test]
    fn call_val() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 1 + 2 1 262153 1 x 2 14 1 1 254");
        assert_eq!(
            obj,
            Obj::lang(vec![
                Obj::sym("+"),
                Obj::sym("x"),
                Obj::real(vec![1.])
            ])
        );
    }

    #[test]
    fn call_sin_pi() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 3 sin 2 1 262153 2 pi 254");
        assert_eq!(
            obj,
            Obj::lang(vec![Obj::sym("sin"), Obj::sym("pi")])
        );
    }

    #[test]
    fn assign() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 2 <- 2 1 262153 1 x 2 14 1 1 254");
        println!("{:?}", obj);
        assert_eq!(
            obj,
            Obj::lang(vec![
                Obj::sym("<-"),
                Obj::sym("x"),
                Obj::real(vec![1.])
            ])
        );
    }

    #[test]
    fn list_val() {
        let obj = read_ascii("A 2 197636 131840 19 1 14 1 1");
        assert_eq!(
            obj,
            Obj::Obj(None, vec![Obj::Real(None, vec![1.])])
        );
    }

    #[test]
    fn named_list_val() {
        let obj =
            read_ascii("A 2 197636 131840 531 1 14 1 1 1026 1 262153 5 names 16 1 262153 1 a 254");
        let names = Obj::strings(vec!["a"]);
        let mut cmp = Obj::Obj(None, vec![Obj::Real(None, vec![1.])]);
        cmp.add_attr("names", names);
        assert_eq!(obj, cmp);
    }

    #[test]
    fn env() {
        let _obj = read_ascii("A 2 197636 131840 4 0 253 254 19 29 254 254 254 254 1026 1 262153 1 x 14 1 1 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254");
        //let mut hashvals = vec![Nil(None); 29];
        //hashvals[4] = Obj::named_list(vec!["x"], vec![Obj::real(vec![1.])]);
        //let hashtab = Obj::vec(hashvals);
        let enclos = Global(None);
        let frame = Obj::null();
        let keyvals = vec![(Obj::sym("x"), Obj::real(vec![1.]))];
        let _cmp = Obj::env(false, enclos, frame, keyvals);
        //assert_eq!(obj, cmp);
    }

    #[test]
    fn attr() {
        let obj = read_ascii("A 2 197636 131840 526 1 1 1026 1 262153 6 attr-x 14 1 2 254");
        let mut cmp = Obj::real(vec![1.]);
        cmp.add_attr("attr-x", Obj::real(vec![2.]));
        assert_eq!(obj, cmp);
    }

    #[test]
    fn func1() {
        //let obj = read_ascii(r"A 2 197636 131840 1539 1026 1 262153 6 srcref 781 8 1 6 1 18 6 18 1 1 1026 1 262153 7 srcfile 4 0 242 1026 1 262153 5 lines 16 1 262153 19 f\040<-\040function()\040{}\n 1026 1 262153 8 filename 16 1 262153 0 254 254 1026 1 262153 5 class 16 2 262153 11 srcfilecopy 262153 7 srcfile 254 1026 1791 16 1 262153 6 srcref 254 254 253 254 518 1026 511 19 1 781 8 1 17 1 17 17 17 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 1026 767 1023 1026 1 262153 11 wholeSrcref 781 8 1 0 1 18 0 18 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 254 1 262153 1 { 254");
        //println!("{:?}", obj);
        //assert!(false);
        //let cmp = Obj::func();
        //assert_eq!(obj, cmp);
    }

    #[test]
    fn func2() {
        //let obj = read_ascii(r#"A 2 197636 131840 1539 1026 1 262153 6 srcref 781 8 1 6 1 26 6 26 1 1 1026 1 262153 7 srcfile 4 0 242 1026 1 262153 5 lines 16 1 262153 27 f\040<-\040function(x)\040{\040x\040+\0401\040}\n 1026 1 262153 8 filename 16 1 262153 0 254 254 1026 1 262153 5 class 16 2 262153 11 srcfilecopy 262153 7 srcfile 254 1026 1791 16 1 262153 6 srcref 254 254 253 1026 1 262153 1 x 251 254 518 1026 511 19 2 781 8 1 18 1 18 18 18 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 781 8 1 20 1 24 20 24 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 1026 767 1023 1026 1 262153 11 wholeSrcref 781 8 1 0 1 26 0 26 1 1 1026 767 1023 1026 1791 16 1 262153 6 srcref 254 254 1 262153 1 { 2 6 1 262153 1 + 2 2047 2 14 1 1 254 254"#);
        //let cmp = Obj::func();
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
        let cmp = Obj::data_frame(
            vec![Obj::real(vec![1.]), Obj::real(vec![2.])],
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
            Obj::expr(vec![Obj::lang(vec![
                Obj::sym("+"),
                Obj::real(vec![1.]),
                Obj::real(vec![1.])
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

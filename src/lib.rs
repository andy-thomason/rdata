use std::io::Read;
use std::rc::Rc;
use num_traits::FromPrimitive;

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
    // Symbol "x"
    tag: Object,

    // List of attributes
    attr: Object,

    //
    levels: i32,

    //
    is_obj: bool,
}

#[derive(PartialEq, Debug, Clone)]
/// See https://en.wikipedia.org/wiki/CAR_and_CDR
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
            Object::LISTSXP(None, Rc::new(List::from_slice(&slice[1..])))
        };
        List {
            car: slice[0].clone(),
            cdr: next,
        }
    }
}

type Obe = Option<Box<Extras>>;

/// An idiomatic representation of an R object.
#[derive(PartialEq, Debug, Clone)]
pub enum Object {
    // Sym and Env can have muliple referencs to the same object.
    SYMSXP(Obe, Rc<Object>),
    ENVSXP(Obe, Rc<Object>),

    // Lists are lisp-style car/cdr pairs.
    LISTSXP(Obe, Rc<List>),
    CLOSXP(Obe, Rc<List>),
    PROMSXP(Obe, Rc<List>),
    LANGSXP(Obe, Rc<List>),
    DOTSXP(Obe, Rc<List>),

    // These are vectors.
    CHARSXP(Obe, String),
    LGLSXP(Obe, Vec<bool>),
    INTSXP(Obe, Vec<i32>),
    REALSXP(Obe, Vec<f64>),
    CPLXSXP(Obe, Vec<(f64, f64)>),
    STRSXP(Obe, Vec<Object>),
    VECSXP(Obe, Vec<Object>),
    EXPRSXP(Obe, Vec<Object>),
    RAWSXP(Obe, Vec<u8>),

    // Special functions.
    SPECIALSXP(Obe, String),
    BUILTINSXP(Obe, String),

    // Yet to be done.
    BCODESXP(Obe),
    EXTPTRSXP(Obe),
    WEAKREFSXP(Obe),
    S4SXP(Obe),
    NEWSXP(Obe),
    FREESXP(Obe),

    // Special values.
    NILVALUE(Obe),
    GLOBALENV(Obe),
    UNBOUNDVALUE(Obe),
    MISSINGARG(Obe),
    BASENAMESPACE(Obe),
    EMPTYENV(Obe),
    BASEENV(Obe),
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
            cdr: Object::NILVALUE(None),
        };
        let mut e = Extras::new();
        e.tag = Object::SYMSXP(None, Rc::new(Object::chars(name)));
        std::mem::swap(&mut new_list.cdr, self);
        *self = Object::LISTSXP(Some(Box::new(e)), Rc::new(new_list))
    }

    pub fn is_null(&self) -> bool {
        match self {
            Object::NILVALUE(_) => true,
            _ => false,
        }
    }

    pub fn null() -> Self {
        Object::NILVALUE(None)
    }

    pub fn chars(chrs: &str) -> Self {
        Object::CHARSXP(None, chrs.to_string())
    }

    pub fn strings(strs: Vec<&str>) -> Self {
        Object::STRSXP(
            None,
            strs.into_iter()
                .map(|s| Object::chars(s))
                .collect::<Vec<Object>>(),
        )
    }

    pub fn sym(chrs: &str) -> Self {
        Object::SYMSXP(None, Rc::new(Object::CHARSXP(None, chrs.to_string())))
    }

    pub fn real(vals: Vec<f64>) -> Self {
        Object::REALSXP(None, vals)
    }

    pub fn integer(vals: Vec<i32>) -> Self {
        Object::INTSXP(None, vals)
    }

    pub fn vec(vals: Vec<Object>) -> Self {
        Object::VECSXP(None, vals)
    }

    pub fn func() -> Self {
        Object::null()
    }

    pub fn extras_mut(&mut self) -> &mut Obe {
        match self {
            Object::SYMSXP(ref mut obe, _)
            | Object::ENVSXP(ref mut obe, _)
            | Object::LISTSXP(ref mut obe, _)
            | Object::CLOSXP(ref mut obe, _)
            | Object::PROMSXP(ref mut obe, _)
            | Object::LANGSXP(ref mut obe, _)
            | Object::DOTSXP(ref mut obe, _)
            | Object::SPECIALSXP(ref mut obe, _)
            | Object::BUILTINSXP(ref mut obe, _)
            | Object::CHARSXP(ref mut obe, _)
            | Object::LGLSXP(ref mut obe, _)
            | Object::INTSXP(ref mut obe, _)
            | Object::REALSXP(ref mut obe, _)
            | Object::CPLXSXP(ref mut obe, _)
            | Object::STRSXP(ref mut obe, _)
            | Object::VECSXP(ref mut obe, _)
            | Object::EXPRSXP(ref mut obe, _)
            | Object::BCODESXP(ref mut obe)
            | Object::EXTPTRSXP(ref mut obe)
            | Object::WEAKREFSXP(ref mut obe)
            | Object::RAWSXP(ref mut obe, _)
            | Object::S4SXP(ref mut obe)
            | Object::NEWSXP(ref mut obe)
            | Object::FREESXP(ref mut obe)
            | Object::NILVALUE(ref mut obe)
            | Object::GLOBALENV(ref mut obe)
            | Object::UNBOUNDVALUE(ref mut obe)
            | Object::MISSINGARG(ref mut obe)
            | Object::BASENAMESPACE(ref mut obe)
            | Object::EMPTYENV(ref mut obe)
            | Object::BASEENV(ref mut obe) => obe,
        }
    }

    pub fn extras(&self) -> &Obe {
        match self {
            Object::SYMSXP(ref obe, _)
            | Object::ENVSXP(ref obe, _)
            | Object::LISTSXP(ref obe, _)
            | Object::CLOSXP(ref obe, _)
            | Object::PROMSXP(ref obe, _)
            | Object::LANGSXP(ref obe, _)
            | Object::DOTSXP(ref obe, _)
            | Object::SPECIALSXP(ref obe, _)
            | Object::BUILTINSXP(ref obe, _)
            | Object::CHARSXP(ref obe, _)
            | Object::LGLSXP(ref obe, _)
            | Object::INTSXP(ref obe, _)
            | Object::REALSXP(ref obe, _)
            | Object::CPLXSXP(ref obe, _)
            | Object::STRSXP(ref obe, _)
            | Object::VECSXP(ref obe, _)
            | Object::EXPRSXP(ref obe, _)
            | Object::BCODESXP(ref obe)
            | Object::EXTPTRSXP(ref obe)
            | Object::WEAKREFSXP(ref obe)
            | Object::RAWSXP(ref obe, _)
            | Object::S4SXP(ref obe)
            | Object::NEWSXP(ref obe)
            | Object::FREESXP(ref obe)
            | Object::NILVALUE(ref obe)
            | Object::GLOBALENV(ref obe)
            | Object::UNBOUNDVALUE(ref obe)
            | Object::MISSINGARG(ref obe)
            | Object::BASENAMESPACE(ref obe)
            | Object::EMPTYENV(ref obe)
            | Object::BASEENV(ref obe) => obe,
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
        let n : i32 = i32::from_usize(cmax).unwrap_or(1);
        let mut res = Object::vec(columns);
        res.add_attr("class", Object::strings(vec!["data.frame"]));
        res.add_attr("row.names", Object::integer(vec![-2147483648, -(n as i32)]));
        res.add_attr("names", Object::strings(names));
        res.set_is_obj(true);
        res
    }

    pub fn len(&self) -> usize {
        match self {
            Object::LGLSXP(_, vec) => vec.len(),
            Object::INTSXP(_, vec) => vec.len(),
            Object::REALSXP(_, vec) => vec.len(),
            Object::CPLXSXP(_, vec) => vec.len(),
            Object::STRSXP(_, vec) => vec.len(),
            Object::VECSXP(_, vec) => vec.len(),
            Object::EXPRSXP(_, vec) => vec.len(),
            Object::RAWSXP(_, vec) => vec.len(),
            _ => 0
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
                Ok(f64::from_bits(0x7ff0000000000000 + 1954))
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
                            // todo, support octal encoded - maybe...
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
    fn dotted_list(
        &mut self,
        _has_attr: bool,
        _has_tag: bool,
        _is_obj: bool,
        _levels: i32,
    ) -> Result<Rc<List>> {
        Ok(Rc::new(List {
            car: self.read_object()?,
            cdr: self.read_object()?,
        }))
    }

    pub fn env(
        &mut self,
        _locked: bool,
        enclos: Object,
        frame: Object,
        hashtab: Object,
        attr: Object,
    ) -> Object {
        let data = Rc::new(Object::vec(vec![enclos, frame, hashtab]));
        if !attr.is_null() {
            let mut e = Extras::new();
            e.attr = attr;
            Object::ENVSXP(Some(Box::new(e)), data)
        } else {
            Object::ENVSXP(None, data)
        }
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
            /*SYMSXP*/
            {
                let obj = self.read_object()?;
                let res = Object::SYMSXP(None, Rc::new(obj));
                self.refs.push(res.clone());
                res
            }

            2 =>
            /*LISTSXP*/
            {
                Object::LISTSXP(
                    self.list_extras(has_attr, has_tag, is_obj, 0)?,
                    self.dotted_list(has_attr, has_tag, is_obj, levels)?,
                )
            }
            3 =>
            /*CLOSXP*/
            {
                Object::CLOSXP(
                    self.list_extras(has_attr, has_tag, is_obj, 0)?,
                    self.dotted_list(has_attr, has_tag, is_obj, levels)?,
                )
            }
            5 =>
            /*PROMSXP*/
            {
                Object::PROMSXP(
                    self.list_extras(has_attr, has_tag, is_obj, 0)?,
                    self.dotted_list(has_attr, has_tag, is_obj, levels)?,
                )
            }
            6 =>
            /*LANGSXP*/
            {
                Object::LANGSXP(
                    self.list_extras(has_attr, has_tag, is_obj, 0)?,
                    self.dotted_list(has_attr, has_tag, is_obj, levels)?,
                )
            }
            17 =>
            /*DOTSXP*/
            {
                Object::DOTSXP(
                    self.list_extras(has_attr, has_tag, is_obj, 0)?,
                    self.dotted_list(has_attr, has_tag, is_obj, levels)?,
                )
            }
            4 =>
            /*ENVSXP*/
            {
                let locked = self.integer()? != 0;
                let enclos = self.read_object()?;
                let frame = self.read_object()?;
                let hashtab = self.read_object()?;
                let attr = self.read_object()?;
                let res = self.env(locked, enclos, frame, hashtab, attr);
                self.refs.push(res.clone());
                res
            }
            7 =>
            /*SPECIALSXP*/
            {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                Object::SPECIALSXP(None, instr)
            }
            8 =>
            /*BUILTINSXP*/
            {
                let length = self.integer()? as usize;
                println!("len={}", length);
                let instr = self.string(length)?;
                println!("instr={}", instr);
                Object::BUILTINSXP(None, instr)
            }
            9 =>
            /*CHARSXP*/
            {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                // ignore the levels field for now.
                Object::CHARSXP(self.extras(has_attr, has_tag, is_obj, 0)?, instr)
            }
            10 =>
            /*LGLSXP*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()? != 0);
                }
                Object::LGLSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            13 =>
            /*INTSXP*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()?);
                }
                Object::INTSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            14 =>
            /*REALSXP*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.real()?);
                }
                Object::REALSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            15 =>
            /*CPLXSXP*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    let re = self.real()?;
                    let im = self.real()?;
                    data.push((re, im));
                }
                Object::CPLXSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            16 =>
            /*STRSXP*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Object::STRSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            // 18 => /*ANYSXP*/ Object::ANYSXP(),
            19 =>
            /*VECSXP*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Object::VECSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            20 =>
            /*EXPRSXP*/
            {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Object::EXPRSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            // 21 => /*BCODESXP*/ Object::BCODESXP(),
            // 22 => /*EXTPTRSXP*/ Object::EXTPTRSXP(),
            // 23 => /*WEAKREFSXP*/ Object::WEAKREFSXP(),
            // 24 => /*RAWSXP*/ Object::RAWSXP(),
            // 25 => /*S4SXP*/ Object::S4SXP(),
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
                Object::NILVALUE(None)
            }
            253 =>
            /*GLOBALENV_SXP*/
            {
                Object::GLOBALENV(None)
            }
            252 =>
            /*UNBOUNDVALUE_SXP*/
            {
                Object::UNBOUNDVALUE(None)
            }
            251 =>
            /*MISSINGARG_SXP*/
            {
                Object::MISSINGARG(None)
            }
            250 =>
            /*BASENAMESPACE_SXP*/
            {
                Object::BASENAMESPACE(None)
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
                Object::EMPTYENV(None)
            }
            241 =>
            /*BASEENV_SXP*/
            {
                Object::BASEENV(None)
            }
            _ => Err(Error::from(format!("unsupported R data type {}", objtype)))?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::List;
    use super::Object;
    use super::Object::*;
    use super::Reader;
    use std::rc::Rc;

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
        assert_eq!(obj, Object::INTSXP(None, vec![1]));
    }

    #[test]
    fn real_val() {
        let obj = read_ascii("A 2 197636 131840 14 1 1");
        assert_eq!(obj, Object::REALSXP(None, vec![1.]));
    }

    #[test]
    fn complex_val() {
        let obj = read_ascii("A 2 197636 131840 15 1 1 2");
        assert_eq!(obj, Object::CPLXSXP(None, vec![(1., 2.)]));
    }

    #[test]
    fn null_val() {
        let obj = read_ascii("A 2 197636 131840 254");
        assert_eq!(obj, Object::NILVALUE(None));
    }

    #[test]
    fn bool_val() {
        let obj = read_ascii("A 2 197636 131840 10 2 1 0");
        assert_eq!(obj, Object::LGLSXP(None, vec![true, false]));
    }

    #[test]
    fn sym_val() {
        // Actually a sym (1 262153 1 x) and a ref (511)
        let obj = read_ascii("A 2 197636 131840 19 2 1 262153 1 x 511");
        let x = Rc::new(CHARSXP(None, "x".to_string()));
        assert_eq!(
            obj,
            VECSXP(None, vec![SYMSXP(None, x.clone()), SYMSXP(None, x.clone())])
        );
    }

    #[test]
    fn call_val() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 1 + 2 1 262153 1 x 2 14 1 1 254");
        assert_eq!(
            obj,
            LANGSXP(
                None,
                Rc::new(List::from_slice(&[
                    Object::sym("+"),
                    Object::sym("x"),
                    Object::real(vec![1.])
                ]))
            )
        );
    }

    #[test]
    fn list_val() {
        let obj = read_ascii("A 2 197636 131840 19 1 14 1 1");
        assert_eq!(
            obj,
            Object::VECSXP(None, vec![Object::REALSXP(None, vec![1.])])
        );
    }

    #[test]
    fn named_list_val() {
        let obj =
            read_ascii("A 2 197636 131840 531 1 14 1 1 1026 1 262153 5 names 16 1 262153 1 a 254");
        let names = Object::strings(vec!["a"]);
        let mut cmp = Object::VECSXP(None, vec![Object::REALSXP(None, vec![1.])]);
        cmp.add_attr("names", names);
        assert_eq!(obj, cmp);
    }

    #[test]
    fn env() {
        let obj = read_ascii("A 2 197636 131840 4 0 253 254 19 29 254 254 254 254 1026 1 262153 1 x 14 1 1 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254");
        let mut hashvals = vec![NILVALUE(None); 29];
        hashvals[4] = Object::named_list(vec!["x"], vec![Object::real(vec![1.])]);
        let hashtab = Object::vec(hashvals);
        let enclos = GLOBALENV(None);
        let frame = Object::null();
        let cmp = Object::ENVSXP(None, Rc::new(Object::vec(vec![enclos, frame, hashtab])));
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
        let obj = read_ascii(
            r#"A 2 197636 131840 787 2 14 1 1 14 1 2 1026 1 262153 5 names 16 2 262153 1 a 262153 1 b 1026 1 262153 9 row.names 13 2 NA -1 1026 1 262153 5 class 16 1 262153 10 data.frame 254"#,
        );
        let cmp = Object::data_frame(
            vec![Object::real(vec![1.]), Object::real(vec![2.])],
            vec!["a", "b"]
        );
        assert_eq!(obj, cmp);
    }

    #[test]
    fn builtin() {
        let obj = read_ascii(r#"A 2 197636 131840 8 1 c"#);
        println!("{:?}", obj);
        assert_eq!(obj, BUILTINSXP(None, "c".to_string()));
    }

    // #[test]
    // fn rda2() {
    //     let obj = read_ascii(
    //         r"RDA2 A 2 197636 131840 1026 1 262153 2 df 787 2 14 1 1 14 1 2 1026 1 262153 5 names 16 2 262153 1 a 262153 1 b 1026 1 262153 9 row.names 13 2 NA -1 1026 1 262153 5 class 16 1 262153 10 data.frame 254 254",
    //     );
    //     println!("rda2={:?}", obj);
    //     assert_eq!(obj, NILVALUE(None));
    // }

    #[test]
    fn bin() {
        let obj = read_bin("580a0000000200030404000203000000000e000000013ff0000000000000");
        println!("bin={:?}", obj);
        assert_eq!(obj, REALSXP(None, vec![1.0]));
    }
}

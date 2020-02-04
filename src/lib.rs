use std::io::Read;

// see https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h
// http://www.maths.lth.se/matstat/staff/nader/stint/R_Manuals/R-ints.pdf
// https://github.com/wch/r-source/blob/trunk/src/main/serialize.c


pub struct AsciiReader<R: Read> {
    buf: String,
    src: R
}

pub type Error = Box<dyn std::error::Error>;
pub type Result<T> = std::result::Result<T, Error>;

#[derive(PartialEq, Debug, Clone)]
pub struct Extras {
    attr: Object,
    tag: Object,
    car: Object,
    cdr: Object,
    levels: i32,
    is_obj: bool,
}


type Obe = Option<Box<Extras>>;

/// An idiomatic representation of an R object.
#[derive(PartialEq, Debug, Clone)]
pub enum Object {
    NILSXP(Obe),
    SYMSXP(Obe, Box<Object>),
    LISTSXP(Obe),
    CLOSXP(Obe),
    ENVSXP(Obe),
    PROMSXP(Obe),
    LANGSXP(Obe),
    SPECIALSXP(Obe),
    BUILTINSXP(Obe),
    CHARSXP(Obe, String),
    LGLSXP(Obe, Vec<bool>),
    INTSXP(Obe, Vec<i32>),
    REALSXP(Obe, Vec<f64>),
    CPLXSXP(Obe, Vec<(f64,f64)>),
    STRSXP(Obe, Vec<Object>),
    DOTSXP(Obe),
    ANYSXP(Obe),
    VECSXP(Obe, Vec<Object>),
    EXPRSXP(Obe),
    BCODESXP(Obe),
    EXTPTRSXP(Obe),
    WEAKREFSXP(Obe),
    RAWSXP(Obe, Vec<u8>),
    S4SXP(Obe),
    NEWSXP(Obe),
    FREESXP(Obe),
}

impl Object {
    /*fn named_list(names: Vec<&str>, objects: Vec<Object>) {
        let mut root = Box::new(Object::null());
        for (n, o) in names.into_iter().zip(objects.into_iter()) {
            root = Object::list_node(n, o, root);
        }
    }*/

    pub fn append_to_list(&mut self, name: &str, object: Object) {
        let mut e = Extras::new();
        e.tag = Object::SYMSXP(None, Box::new(Object::chars(name)));
        e.car = object;
        std::mem::swap(&mut e.cdr, self);
        *self = Object::LISTSXP(Some(Box::new(e)))
    }

    pub fn null() -> Self {
        Object::NILSXP(None)
    }

    pub fn chars(chrs: &str) -> Self {
        Object::CHARSXP(None, chrs.to_string())
    }

    pub fn strings(strs: Vec<&str>) -> Self {
        Object::STRSXP(None, strs.into_iter().map(|s| Object::chars(s)).collect::<Vec<Object>>())
    }

    pub fn extras(&mut self) -> &mut Obe {
        match self {
            Object::NILSXP(ref mut obe) => obe,
            Object::SYMSXP(ref mut obe, _) => obe,
            Object::LISTSXP(ref mut obe) => obe,
            Object::CLOSXP(ref mut obe) => obe,
            Object::ENVSXP(ref mut obe) => obe,
            Object::PROMSXP(ref mut obe) => obe,
            Object::LANGSXP(ref mut obe) => obe,
            Object::SPECIALSXP(ref mut obe) => obe,
            Object::BUILTINSXP(ref mut obe) => obe,
            Object::CHARSXP(ref mut obe, _) => obe,
            Object::LGLSXP(ref mut obe, _) => obe,
            Object::INTSXP(ref mut obe, _) => obe,
            Object::REALSXP(ref mut obe, _) => obe,
            Object::CPLXSXP(ref mut obe, _) => obe,
            Object::STRSXP(ref mut obe, _) => obe,
            Object::DOTSXP(ref mut obe) => obe,
            Object::ANYSXP(ref mut obe) => obe,
            Object::VECSXP(ref mut obe, _) => obe,
            Object::EXPRSXP(ref mut obe) => obe,
            Object::BCODESXP(ref mut obe) => obe,
            Object::EXTPTRSXP(ref mut obe) => obe,
            Object::WEAKREFSXP(ref mut obe) => obe,
            Object::RAWSXP(ref mut obe, _) => obe,
            Object::S4SXP(ref mut obe) => obe,
            Object::NEWSXP(ref mut obe) => obe,
            Object::FREESXP(ref mut obe) => obe,
        }
    }

    pub fn add_attr(&mut self, name: &str, object: Object) {
        let extras = self.extras();
        if extras.is_none() {
            *extras = Extras::obe();
        }

        if let Some(ref mut extras) = extras {
            extras.attr.append_to_list(name, object);
        }
    }
}

impl Extras {
    fn new() -> Self {
        Extras { attr: Object::null(), tag: Object::null(), car: Object::null(), cdr: Object::null(), levels: 0, is_obj: false }
    }

    fn obe() -> Option<Box<Self>> {
        Some(Box::new(Extras::new()))
    }

}


impl<R: Read> AsciiReader<R> {
    pub fn try_new(src: R) -> Result<Self> {
        let mut res = Self { buf: String::new(), src };
        res.word()?;
        if res.buf != "A" { return Err(Error::from("not an R file")); }

        let version = res.integer()?;
        let _writer_version = res.integer()?;
        let _min_reader_version = res.integer()?;

        if version != 2 { return Err(Error::from("only version 2 supported")); }

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
            if ch > b' ' { break; }
            ch = self.byte()?;
        }
        loop {
            if ch <= b' ' { break; }
            self.buf.push(ch as char);
            ch = self.byte()?;
        }
        //println!("w={}", self.buf);
        Ok(())
    }

    fn integer(&mut self) -> Result<i32> {
        self.word()?;
        Ok(self.buf.parse::<i32>()?)
    }

    fn real(&mut self) -> Result<f64> {
        self.word()?;
        Ok(self.buf.parse::<f64>()?)
    }

    fn string(&mut self, length: usize) -> Result<String> {
        self.buf.clear();
        let mut ch = self.byte()?;
        loop {
            if ch > b' ' { break; }
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
                    // todo, support octal encoded - maybe...
                    _ => ch as char
                };
                self.buf.push(chr);
            } else {
                self.buf.push(ch as char);
            }
            ch = self.byte()?;
        }
        //println!("s={}", self.buf);
        Ok(self.buf.clone())
    }

    fn extras(&mut self, has_attr: bool, has_tag: bool, is_obj: bool, levels: i32) -> Result<Obe> {
        if !has_attr && !has_tag && !is_obj && levels == 0 {
            return Ok(None)
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
    fn dotted_list(&mut self, has_attr: bool, has_tag: bool, is_obj: bool, levels: i32) -> Result<Obe> {
        let mut extras = Extras::new();
        if has_attr {
            extras.attr = self.read_object()?;
        }
        if has_tag {
            extras.tag = self.read_object()?;
        }
        extras.is_obj = is_obj;
        extras.levels = levels;
        extras.car = self.read_object()?;
        extras.cdr = self.read_object()?;
        Ok(Some(Box::new(extras)))
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
            0 => /*NILSXP*/ Object::NILSXP(None),
            1 => /*SYMSXP*/ Object::SYMSXP(None, Box::new(self.read_object()?)),

            2 => /*LISTSXP*/ Object::LISTSXP(self.dotted_list(has_attr, has_tag, is_obj, levels)?),
            3 => /*CLOSXP*/ Object::CLOSXP(self.dotted_list(has_attr, has_tag, is_obj, levels)?),
            5 => /*PROMSXP*/ Object::PROMSXP(self.dotted_list(has_attr, has_tag, is_obj, levels)?),
            6 => /*LANGSXP*/ Object::LANGSXP(self.dotted_list(has_attr, has_tag, is_obj, levels)?),
            17 => /*DOTSXP*/ Object::DOTSXP(self.dotted_list(has_attr, has_tag, is_obj, levels)?),
            4 => /*ENVSXP*/ {
                Object::ENVSXP(self.extras(has_attr, has_tag, is_obj, levels)?)
            }
            // 7 => /*SPECIALSXP*/ Object::SPECIALSXP(),
            // 8 => /*BUILTINSXP*/ Object::BUILTINSXP(),
            9 => /*CHARSXP*/ {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                // ignore the levels field for now.
                Object::CHARSXP(self.extras(has_attr, has_tag, is_obj, 0)?, instr)
            }
            10 => /*LGLSXP*/ {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()? != 0);
                }
                Object::LGLSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            13 => /*INTSXP*/ {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()?);
                }
                Object::INTSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            14 => /*REALSXP*/ {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.real()?);
                }
                Object::REALSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            15 => /*CPLXSXP*/ {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    let re = self.real()?;
                    let im = self.real()?;
                    data.push((re, im));
                }
                Object::CPLXSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            16 => /*STRSXP*/ {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                
                Object::STRSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            // 18 => /*ANYSXP*/ Object::ANYSXP(),
            19 => /*VECSXP*/ {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                
                Object::VECSXP(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            // 20 => /*EXPRSXP*/ Object::EXPRSXP(),
            // 21 => /*BCODESXP*/ Object::BCODESXP(),
            // 22 => /*EXTPTRSXP*/ Object::EXTPTRSXP(),
            // 23 => /*WEAKREFSXP*/ Object::WEAKREFSXP(),
            // 24 => /*RAWSXP*/ Object::RAWSXP(),
            // 25 => /*S4SXP*/ Object::S4SXP(),
            // 30 => /*NEWSXP*/ Object::NEWSXP(),
            // 31 => /*FREESXP*/ Object::FREESXP(),

            // 255 => /*REFSXP*/ Object::NILSXP,
            254 => /*NILVALUE_SXP*/ Object::NILSXP(None),
            // 253 => /*GLOBALENV_SXP*/ Object::NILSXP,
            // 252 => /*UNBOUNDVALUE_SXP*/ Object::NILSXP,
            // 251 => /*MISSINGARG_SXP*/ Object::NILSXP,
            // 250 => /*BASENAMESPACE_SXP*/ Object::NILSXP,
            // 249 => /*NAMESPACESXP*/ Object::NILSXP,
            // 248 => /*PACKAGESXP*/ Object::NILSXP,
            // 247 => /*PERSISTSXP*/ Object::NILSXP,
            // 246 => /*CLASSREFSXP*/ Object::NILSXP,
            // 245 => /*GENERICREFSXP*/ Object::NILSXP,
            // 244 => /*BCREPDEF*/ Object::NILSXP,
            // 243 => /*BCREPREF*/ Object::NILSXP,
            // 242 => /*EMPTYENV_SXP*/ Object::NILSXP,
            // 241 => /*BASEENV_SXP*/ Object::NILSXP,
            _ => Err(Error::from(format!("unsupported R data type {}", objtype)))?
        })
    }
    
}

#[cfg(test)]
mod tests {
    use super::AsciiReader;
    use super::Object;
    //use super::Extras;

    #[test]
    fn int_val() {
        let mut src = AsciiReader::try_new(std::io::Cursor::new(
            "A 2 197636 131840 13 1 1"
        )).unwrap();
        let obj = src.read_object().unwrap();
        assert!(src.inner().position() == src.inner().get_ref().len() as u64);
        assert_eq!(obj, Object::INTSXP(None, vec![1]));
    }

    #[test]
    fn real_val() {
        let mut src = AsciiReader::try_new(std::io::Cursor::new(
            "A 2 197636 131840 14 1 1"
        )).unwrap();
        let obj = src.read_object().unwrap();
        assert!(src.inner().position() == src.inner().get_ref().len() as u64);
        assert_eq!(obj, Object::REALSXP(None, vec![1.]));
    }

    #[test]
    fn complex_val() {
        let mut src = AsciiReader::try_new(std::io::Cursor::new(
            "A 2 197636 131840 15 1 1 2"
        )).unwrap();
        let obj = src.read_object().unwrap();
        assert!(src.inner().position() == src.inner().get_ref().len() as u64);
        assert_eq!(obj, Object::CPLXSXP(None, vec![(1.,2.)]));
    }

    #[test]
    fn null_val() {
        let mut src = AsciiReader::try_new(std::io::Cursor::new(
            "A 2 197636 131840 254"
        )).unwrap();
        let obj = src.read_object().unwrap();
        assert!(src.inner().position() == src.inner().get_ref().len() as u64);
        assert_eq!(obj, Object::NILSXP(None));
    }

    #[test]
    fn bool_val() {
        let mut src = AsciiReader::try_new(std::io::Cursor::new(
            "A 2 197636 131840 10 2 1 0"
        )).unwrap();
        let obj = src.read_object().unwrap();
        assert!(src.inner().position() == src.inner().get_ref().len() as u64);
        assert_eq!(obj, Object::LGLSXP(None, vec![true, false]));
    }

    #[test]
    fn list_val() {
        let mut src = AsciiReader::try_new(std::io::Cursor::new(
            "A 2 197636 131840 19 1 14 1 1"
        )).unwrap();
        let obj = src.read_object().unwrap();
        assert!(src.inner().position() == src.inner().get_ref().len() as u64);
        assert_eq!(obj, Object::VECSXP(None, vec![Object::REALSXP(None, vec![1.])]));
    }

    #[test]
    fn named_list_val() {
        let mut src = AsciiReader::try_new(std::io::Cursor::new(
            "A 2 197636 131840 531 1 14 1 1 1026 1 262153 5 names 16 1 262153 1 a 254"
        )).unwrap();
        let obj = src.read_object().unwrap();
        assert!(src.inner().position() == src.inner().get_ref().len() as u64);
        let names = Object::strings(vec!["a"]);
        let mut cmp = Object::VECSXP(None, vec![Object::REALSXP(None, vec![1.])]);
        cmp.add_attr("names", names);
        assert_eq!(obj, cmp);
    }
}

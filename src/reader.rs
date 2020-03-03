use std::io::Read;

use crate::{Error, Extras, Obe, Obj, Result};
use crate::obj::{NA_INTEGER};

// see https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h
// http://www.maths.lth.se/matstat/staff/nader/stint/R_Manuals/R-ints.pdf
// https://github.com/wch/r-source/blob/trunk/src/main/serialize.c

pub struct Reader<R: Read> {
    buf: String,
    src: R,
    refs: Vec<Obj>,
    is_ascii: bool,
    is_xdr: bool,
}

impl<R: Read> Reader<R> {
    pub fn try_new(src: R) -> Result<Self> {
        let mut res = Self {
            buf: String::new(),
            src,
            refs: Vec::new(),
            is_ascii: false,
            is_xdr: false,
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
        } else if buf == b"B\n" {
            res.is_ascii = false;
            res.is_xdr = false;
        } else if buf == b"X\n" {
            res.is_ascii = false;
            res.is_xdr = true;
            // https://tools.ietf.org/html/rfc4506
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
                Ok(NA_INTEGER)
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
        let mut _attr = if !has_attr {
            Obj::null()
        } else {
            self.read_object()?
        };
        let mut tag = if !has_tag {
            Obj::null()
        } else {
            self.read_object()?
        };
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
            _attr = if !has_attr {
                Obj::null()
            } else {
                self.read_object()?
            };
            tag = if !has_tag {
                Obj::null()
            } else {
                self.read_object()?
            };
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
        let objtype = flags & 0xff;
        let levels = flags >> 12;
        let is_obj = (flags & 0x100) != 0;
        let has_attr = (flags & 0x200) != 0;
        let has_tag = (flags & 0x400) != 0;
        //println!("t={} lev={} obj={} attr={} tag={}", objtype, levels, is_obj, has_attr, has_tag);

        Ok(match objtype {
            1 => {
                let obj = self.read_object()?;
                let res = match obj {
                    Obj::Char(_, s) => Obj::sym(s.as_str()),
                    _ => return Err(Error::from("symbol not a string")),
                };
                self.refs.push(res.clone());
                res
            }

            2 => {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::PairList(None, list)
            }
            3 => {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::Closure(None, list)
            }
            5 => {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::Promise(None, list)
            }
            6 => {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::Lang(None, list)
            }
            17 => {
                let list = self.dotted_list(has_attr, has_tag, is_obj, 0)?;
                Obj::Dot(None, list)
            }
            4 => {
                let locked = self.integer()? != 0;
                let enclos = self.read_object()?;
                let frame = self.read_object()?;
                let hashtab = self.read_object()?;
                let attr = self.read_object()?;
                let mut keyvals = Vec::new();
                match hashtab {
                    Obj::List(_, list) => {
                        for obj in list {
                            match obj {
                                Obj::PairList(_, ref list) => {
                                    list.iter()
                                        .for_each(|(t, v)| keyvals.push((t.clone(), v.clone())));
                                }
                                _ => (),
                            }
                        }
                    }
                    _ => (),
                };
                let res = Obj::env(locked, enclos, frame, keyvals);
                if !attr.is_null() {
                    //res.set_attr(attr);
                }
                self.refs.push(res.clone());
                res
            }
            7 => {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                Obj::Special(None, instr)
            }
            8 => {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                Obj::Builtin(None, instr)
            }
            9 => {
                let length = self.integer()? as usize;
                let instr = self.string(length)?;
                // ignore the levels field for now.
                Obj::Char(self.extras(has_attr, has_tag, is_obj, 0)?, instr)
            }
            10 => {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()? != 0);
                }
                Obj::Logical(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            13 => {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.integer()?);
                }
                Obj::Int(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            14 => {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.real()?);
                }
                Obj::Real(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            15 => {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    let re = self.real()?;
                    let im = self.real()?;
                    data.push((re, im));
                }
                Obj::Cplx(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            16 => {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    let obj = self.read_object()?;
                    if let Obj::Char(_, s) = obj {
                        data.push(s);
                    } else {
                        return Err(Error::from("string object does not contain chars."));
                    }
                }
                Obj::Str(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            19 => {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Obj::List(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            20 => {
                let length = self.integer()? as usize;
                let mut data = Vec::with_capacity(length);
                for _ in 0..length {
                    data.push(self.read_object()?);
                }
                Obj::Expr(self.extras(has_attr, has_tag, is_obj, levels)?, data)
            }
            24 => {
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
            //25 => Obj::S4(self.extras(has_attr, has_tag, is_obj, levels)?),
            255 => self.read_ref(flags)?,
            254 => Obj::Nil(None),
            253 => Obj::Global(None),
            252 => Obj::Unbound(None),
            251 => Obj::MissingArg(None),
            250 => Obj::BaseNamespace(None),
            242 => Obj::EmptyEnv(None),
            241 => Obj::BaseEnv(None),
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
        assert_eq!(obj, List(None, vec![Obj::sym("x"), Obj::sym("x")]));
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
            Obj::lang(vec![Obj::sym("+"), Obj::sym("x"), Obj::real(vec![1.])])
        );
    }

    #[test]
    fn call_sin_pi() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 3 sin 2 1 262153 2 pi 254");
        assert_eq!(obj, Obj::lang(vec![Obj::sym("sin"), Obj::sym("pi")]));
    }

    #[test]
    fn assign() {
        let obj = read_ascii("A 2 197636 131840 6 1 262153 2 <- 2 1 262153 1 x 2 14 1 1 254");
        println!("{:?}", obj);
        assert_eq!(
            obj,
            Obj::lang(vec![Obj::sym("<-"), Obj::sym("x"), Obj::real(vec![1.])])
        );
    }

    #[test]
    fn list_val() {
        // list(1)
        let obj = read_ascii("A 2 197636 131840 19 1 14 1 1");
        assert_eq!(obj, Obj::List(None, vec![Obj::Real(None, vec![1.])]));
    }

    #[test]
    fn named_list_val() {
        // list(a=1)
        // list of objects with a "names" attribute.
        let obj =
            read_ascii("A 2 197636 131840 531 1 14 1 1 1026 1 262153 5 names 16 1 262153 1 a 254");
        let names = Obj::strings(vec!["a"]);
        let mut cmp = Obj::List(None, vec![Obj::Real(None, vec![1.])]);
        cmp.add_attr("names", names);
        assert_eq!(obj, cmp);
    }

    #[test]
    fn env() {
        let obj = read_ascii("A 2 197636 131840 4 0 253 254 19 29 254 254 254 254 1026 1 262153 1 x 14 1 1 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254 254");
        let enclos = Global(None);
        let frame = Obj::null();
        let keyvals = vec![(Obj::sym("x"), Obj::real(vec![1.]))];
        let cmp = Obj::env(false, enclos, frame, keyvals);
        assert_eq!(obj, cmp);
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

    /*#[test]
    fn s4() {
        let obj = read_ascii("A 2 197636 131840 66329 1026 1 262153 4 name 16 1 262153 6 Hadley 1026 1 262153 3 age 14 1 31 1026 1 262153 5 class 528 1 262153 6 Person 1026 1 262153 7 package 16 1 262153 10 .GlobalEnv 254 254");
        let mut exp = Obj::S4(None);
        exp.add_attr("name", "Hadley");
        exp.add_attr("age", 31.);
        exp.add_attr("class", "Person");
        assert_eq!(obj, exp);
    }*/

    #[test]
    fn bin() {
        let obj = read_bin("580a0000000200030404000203000000000e000000013ff0000000000000");
        println!("bin={:?}", obj);
        assert_eq!(obj, Real(None, vec![1.0]));
    }
}

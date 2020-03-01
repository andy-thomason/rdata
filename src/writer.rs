
use std::io::Write;

use crate::{Obj, Result, Obe, Extras, Error, Symbol, Env};

pub struct WriteOptions {
    is_ascii: bool,
    is_ascii_stream: bool,
}

impl WriteOptions {
    pub fn new() -> Self {
        Self {
            is_ascii: false,
            is_ascii_stream: false,
        }
    }

}

trait ToI32 {
    fn to_i32(&self) -> i32;
}

impl ToI32 for i32 {
    fn to_i32(&self) -> i32 {
        *self
    }
}

impl ToI32 for bool {
    fn to_i32(&self) -> i32 {
        if *self {1} else {0}
    }
}

/// Writer for R data.
/// 
/// Example:
/// ```
/// use rdata::{Writer, WriteOptions};
/// let buf = Vec::new();
/// let mut opt = WriteOptions::new();
/// let mut dest = Writer::try_new(buf, opt).unwrap();
/// assert_eq!(dest.into_inner(), [88, 10, 0, 0, 0, 2, 0, 3, 4, 4, 0, 2, 3, 0])
/// ```
pub struct Writer<W> {
    dest: W,
    opt: WriteOptions,
}

impl<W : Write> Writer<W> {
    /// Start writing to a buffer or file.
    /// 
    /// Example:
    /// ```
    /// use rdata::{Writer, WriteOptions};
    /// let buf = Vec::new();
    /// let mut opt = WriteOptions::new();
    /// let mut dest = Writer::try_new(buf, opt).unwrap();
    /// assert_eq!(dest.into_inner(), [88, 10, 0, 0, 0, 2, 0, 3, 4, 4, 0, 2, 3, 0])
    /// ```
    pub fn try_new(dest: W, opt: WriteOptions) -> Result<Self> {
        let mut w = Self {
            dest, opt
        };

        if w.opt.is_ascii {
            w.dest.write(&[b'A', b'\n'])?;
        } else {
            w.dest.write(&[b'X', b'\n'])?;
        }
        w.integer(2)?;
        w.integer(197636)?;
        w.integer(131840)?;
        Ok(w)
    }

    /// Extract the writable object from the writer.
    /// 
    /// Example:
    /// ```
    /// use rdata::{Writer, WriteOptions};
    /// let buf = Vec::new();
    /// let mut opt = WriteOptions::new();
    /// let mut dest = Writer::try_new(buf, opt).unwrap();
    /// assert_eq!(dest.into_inner(), [88, 10, 0, 0, 0, 2, 0, 3, 4, 4, 0, 2, 3, 0])
    /// ```
    pub fn into_inner(self) -> W {
        self.dest
    }

    // Write an integer to the file or buffer 
    fn integer(&mut self, val: i32) -> Result<()> {
        if self.opt.is_ascii {
            if val == -0x80000000 {
                write!(self.dest, "NA\n")?;
            } else {
                write!(self.dest, "{}\n", val)?;
            }
        } else {
            self.dest.write(&i32::to_be_bytes(val))?;
        }
        Ok(())
    }

    // Write a floating point number to the file or buffer 
    fn real(&mut self, val: f64) -> Result<()> {
        if self.opt.is_ascii {
            match val.to_bits() {
                0x7ff00000000007a2 => {
                    self.dest.write(b"NA\n")?;
                }
                0x7ff0000000000001 | 0x7ff8000000000000 => {
                    self.dest.write(b"Nan\n")?;
                }
                0x7ff0000000000000 => {
                    self.dest.write(b"Inf\n")?;
                }
                0xfff0000000000000 => {
                    self.dest.write(b"-Inf\n")?;
                }
                _ => {
                    write!(self.dest, "{}\n", val)?;
                }
            }
        } else {
            self.dest.write(&f64::to_bits(val).to_be_bytes())?;
        }
        Ok(())
    }

    // Write a string to the file or buffer 
    fn string(&mut self, s: &str) -> Result<()> {
        let bytes = s.as_bytes();
        self.integer(bytes.len() as i32)?;
        if self.opt.is_ascii {
            for &ch in bytes {
                if ch >= b' ' && ch <= b'~' && ch != b'\\' {
                    self.dest.write(&[ch])?;
                } else {
                    self.dest.write(&format!("\\{:03o}", ch).as_bytes())?;
                }
            }
            self.dest.write(b"\n")?;
        } else {
            self.dest.write(bytes)?;
        }
        Ok(())
    }

    // Write the start of an object.
    fn write_flags(&mut self, obe: &Obe, t: i32) -> Result<()> {
        if let Some(ref extras) = obe {
            self.write_bits(t, &extras.tag, &extras)
        } else {
            self.integer(t)
        }
    }

    fn write_bits(&mut self, t: i32, tag: &Obj, extras: &Extras) -> Result<()> {
        let mut bits = extras.levels << 12;
        if extras.is_obj {
            bits |= 0x100;
        }
        if !extras.attr.is_null() {
            bits |= 0x200;
        }
        if !tag.is_null() {
            bits |= 0x400;
        }
        self.integer(bits | t)
    }

    fn write_attr(&mut self, obe: &Obe) -> Result<()> {
        if let Some(ref extras) = obe {
            if !extras.attr.is_null() {
                self.write_object(&extras.attr)?;
            }
            if !extras.tag.is_null() {
                self.write_object(&extras.tag)?;
            }
        }
        Ok(())
    }

    // Write a symbol.
    fn write_sym(&mut self, obe: &Obe, val: &Symbol) -> Result<()> {
        // TODO: handle refs.
        self.write_flags(&obe, 1)?;
        self.write_flags(&obe, Self::get_char_flags(&val.name))?;
        self.string(&val.name)?;
        Ok(())
    }

    // Write an environment (stack frame etc).
    fn write_env(&mut self, _obe: &Obe, val: &Env) -> Result<()> {
        // This is quite complex as the hash table must match the algorithm in the
        // R source code.
        //panic!("not implemented");
        self.integer(4)?;
        self.integer(if val.locked {1} else {0})?;
        self.write_object(&val.enclos)?;
        self.write_object(&val.frame)?;
        self.write_object(&Obj::PairList(None, vec![(Obj::null(), Obj::null()); 29]))?;
        self.write_object(&Obj::null())
    }

    // Write a linked list.
    // For convenience, we don't store the linked lists as such but as vectors
    // of tags and objects.
    fn write_list(&mut self, obe: &Obe, val: &Vec<(Obj, Obj)>, t: i32) -> Result<()> {
        println!("wl={:?}", val);
        if !val.is_empty() {
            // First attr comes from the object itself, but the tag comes
            // from the list.
            if let Some(ref extras) = obe {
                self.write_bits(t, &val[0].0, &extras)?;
            } else {
                self.integer(t | 0x400)?;
            }
            self.write_object(&val[0].0)?;
            self.write_object(&val[0].1)?;

            let e = Extras::new();
            for (tag, o) in val.iter().skip(1) {
                // write a LISTSXP element
                self.write_bits(2, tag, &e)?;
                // write the tag
                self.write_object(&tag)?;
                // write the CAR
                self.write_object(&o)?;
            }
        }
        // write a null element.
        self.integer(254)
    }

    fn get_char_flags(val: &str) -> i32 {
        if val.as_bytes().iter().any(|&x| x >= 0x80) {
            // UTF8
            9 | (0x08<<12)
        } else {
            // ASCII
            9 | (0x40<<12)
        }
    }

    // Write a single string.
    fn write_char(&mut self, obe: &Obe, val: &str, t: i32) -> Result<()> {
        self.write_flags(&obe, t)?;
        self.string(val)
    }

    // Write an integer or logical vector.
    fn write_int<T>(&mut self, obe: &Obe, val: &Vec<T>, t: i32) -> Result<()>
    where T: ToI32
    {
        self.write_flags(&obe, t)?;
        let len32 = val.len() as i32;
        if len32 as usize != val.len() { return Err(Error::from("vector too long for R format")); }
        self.integer(len32)?;
        for i in val {
            self.integer(i.to_i32())?;
        }
        self.write_attr(&obe)
    }

    // Write a floating point vector.
    fn write_real(&mut self, obe: &Obe, val: &Vec<f64>) -> Result<()> {
        self.write_flags(&obe, 14)?;
        let len32 = val.len() as i32;
        if len32 as usize != val.len() { return Err(Error::from("vector too long for R format")); }
        self.integer(len32)?;
        // TODO: write more directly for binary
        for &i in val {
            self.real(i)?;
        }
        self.write_attr(&obe)
    }

    // Write a complex vector.
    fn write_cplx(&mut self, obe: &Obe, val: &Vec<(f64, f64)>) -> Result<()> {
        self.write_flags(&obe, 15)?;
        let len32 = val.len() as i32;
        if len32 as usize != val.len() { return Err(Error::from("vector too long for R format")); }
        self.integer(len32)?;
        for &i in val {
            self.real(i.0)?;
            self.real(i.1)?;
        }
        self.write_attr(&obe)
    }

    // Write a vector of objects.
    fn write_obj(&mut self, obe: &Obe, val: &Vec<Obj>, t: i32) -> Result<()> {
        self.write_flags(&obe, t)?;
        let len32 = val.len() as i32;
        if len32 as usize != val.len() { return Err(Error::from("vector too long for R format")); }
        self.integer(len32)?;
        for obj in val {
            self.write_object(obj)?;
        }
        self.write_attr(&obe)
    }

    // Write a vector of objects.
    fn write_str(&mut self, obe: &Obe, val: &Vec<String>, t: i32) -> Result<()> {
        self.write_flags(&obe, t)?;
        let len32 = val.len() as i32;
        if len32 as usize != val.len() { return Err(Error::from("vector too long for R format")); }
        self.integer(len32)?;
        for s in val {
            self.integer(Self::get_char_flags(s))?;
            self.string(s)?;
        }
        self.write_attr(&obe)
    }

    // Write a raw object.
    fn write_raw(&mut self, obe: &Obe, val: &Vec<u8>) -> Result<()> {
        self.write_flags(&obe, 24)?;
        let len32 = val.len() as i32;
        if len32 as usize != val.len() { return Err(Error::from("vector too long for R format")); }
        self.integer(len32)?;
        if self.opt.is_ascii_stream {
            for byte in val {
                self.dest.write(&format!("{:02x}\n", byte).as_bytes())?;
            }
        } else {
            self.dest.write(val.as_slice())?;
        }
        Ok(())
    }

    // Write any object.
    pub fn write_object(&mut self, obj: &Obj) -> Result<()> {
        match obj {
            Obj::Sym(ref obe, ref val) => self.write_sym(obe, val),
            Obj::Env(ref obe, ref val) => self.write_env(obe, val),
            Obj::PairList(ref obe, ref val) => self.write_list(obe, val, 2),
            Obj::Closure(ref obe, ref val) => self.write_list(obe, val, 3),
            Obj::Promise(ref obe, ref val) => self.write_list(obe, val, 5),
            Obj::Lang(ref obe, ref val) => self.write_list(obe, val, 6),
            Obj::Dot(ref obe, ref val) => self.write_list(obe, val, 17),
            Obj::Special(ref obe, ref val) => self.write_char(obe, val, 7),
            Obj::Builtin(ref obe, ref val) => self.write_char(obe, val, 8),
            Obj::Char(ref obe, ref val) => self.write_char(obe, val, Self::get_char_flags(val)),
            Obj::Logical(ref obe, ref val) => self.write_int(obe, val, 10),
            Obj::Int(ref obe, ref val) => self.write_int(obe, val, 13),
            Obj::Real(ref obe, ref val) => self.write_real(obe, val),
            Obj::Cplx(ref obe, ref val) => self.write_cplx(obe, val),
            Obj::Str(ref obe, ref val) => self.write_str(obe, val, 16),
            Obj::List(ref obe, ref val) => self.write_obj(obe, val, 19),
            Obj::Expr(ref obe, ref val) => self.write_obj(obe, val, 20),
            Obj::Bytecode(ref _obe) => Err(Error::from("Bytecode not supported yet.")),
            Obj::ExtPtr(ref _obe) => Err(Error::from("ExtPtr not supported yet.")),
            Obj::WeakRef(ref _obe) => Err(Error::from("WeakRef not supported yet.")),
            Obj::Raw(ref obe, ref val) => self.write_raw(obe, val),
            Obj::S4(ref _obe) => Err(Error::from("S4 not supported yet.")),
            Obj::New(ref _obe) => Err(Error::from("New not supported yet.")),
            Obj::Free(ref _obe) => Err(Error::from("Free not supported yet.")),
            Obj::Nil(ref obe) => self.write_flags(&obe, 254),
            Obj::Global(ref obe) => self.write_flags(&obe, 253),
            Obj::Unbound(ref obe) => self.write_flags(&obe, 252),
            Obj::MissingArg(ref obe) => self.write_flags(&obe, 251),
            Obj::BaseNamespace(ref obe) => self.write_flags(&obe, 250),
            Obj::EmptyEnv(ref obe) => self.write_flags(&obe, 242),
            Obj::BaseEnv(ref obe) => self.write_flags(&obe, 241),
        }?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Obj;
    use super::{Writer, WriteOptions};
    use std::process::{Command, Stdio};
    use std::io::Write;
    use crate::api::*;
    use crate::{c, structure, Result};
    use std::convert::Into;

    // Make an RPC call to R
    // This is a polymorphic call.
    fn call_r<T : Into<Obj>>(obj: T, s: &str) {
        let obj = obj.into();
        call_ascii(&obj, s);
        call_binary(&obj, s);
    }
    
    fn call_ascii(obj: &Obj, s: &str) {
        let mut child = Command::new("Rscript")
            .arg("-")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Is Rscript in the path? Try installing R.");
        {
            let stdin = child.stdin.as_mut().expect("failed to get stdin");
            let val = write_ascii(&obj, false);
            //eprintln!("{}", val);
            write!(stdin, "cat(deparse(readRDS(stdin())))\n{}", val).unwrap();
        }
        let output = child
            .wait_with_output()
            .expect("R probably crashed");
        assert_eq!(String::from_utf8_lossy(output.stdout.as_slice()), s);
    }

    fn call_binary(obj: &Obj, s: &str) {
        let mut child = Command::new("R")
            .arg("--slave")
            .arg("-e")
            .arg("cat(deparse(readRDS(file(\"stdin\", \"rb\"))))")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Is Rscript in the path?");
        {
            let stdin = child.stdin.as_mut().expect("failed to get stdin");
            let mut binvec = Vec::new();
            binvec.write(write_binary(&obj).as_slice()).unwrap();
            stdin.write_all(binvec.as_slice()).unwrap();
        }
        let output = child
            .wait_with_output()
            .expect("R probably crashed");
        assert_eq!(String::from_utf8_lossy(output.stdout.as_slice()), s);
    }

    #[test]
    fn test_rpc() -> Result<()> {
        // Call R and deparse the result. Compare this with the expected value.
        call_r(NULL, "NULL");
        call_r(TRUE, "TRUE");
        call_r(FALSE, "FALSE");
        call_r((), "NULL");
        call_r(1., "1");
        call_r(1, "1L");
        call_r("xyz", "\"xyz\"");
        call_r(c!("abc", "xyz"), "c(\"abc\", \"xyz\")");
        //call_r(c!(c!("abc", "xyz"), c!("def", "ghi")), "c(\"abc\", \"xyz\")");
        call_r(c!(1., 2.), "c(1, 2)");
        call_r(c!(1, 2), "1:2");
        call_r(true, "TRUE");
        call_r(false, "FALSE");
        call_r(b"hello" as &[u8], "as.raw(c(0x68, 0x65, 0x6c, 0x6c, 0x6f))");
        call_r(as_raw(&c!(0x68, 0x65, 0x6c, 0x6c, 0x6f))?, "as.raw(c(0x68, 0x65, 0x6c, 0x6c, 0x6f))");
        call_r(structure!(c!(1., 2., 3.), x=4., y="y"), "structure(c(1, 2, 3), x = 4, y = \"y\")");
        Ok(())
    }

    fn write_ascii(obj: &Obj, is_ascii_stream: bool) -> String {
        let buf = Vec::new();
        let mut opt = WriteOptions::new();
        opt.is_ascii = true;
        opt.is_ascii_stream = is_ascii_stream;
        let mut dest = Writer::try_new(buf, opt).unwrap();
        dest.write_object(&obj).unwrap();
        String::from_utf8(dest.into_inner()).unwrap()
    }

    fn write_binary(obj: &Obj) -> Vec<u8> {
        let buf = Vec::new();
        let mut opt = WriteOptions::new();
        opt.is_ascii = false;
        let mut dest = Writer::try_new(buf, opt).unwrap();
        dest.write_object(&obj).unwrap();
        let res = dest.into_inner();
        //println!("res={:02x?}", res);
        res
    }

    #[test]
    fn sym() {
        // saveRDS(as.symbol("x"), stdout(), ascii=TRUE)
        let obj = Obj::sym("x");
        let s = write_ascii(&obj, false);
        assert_eq!(s, "A\n2\n197636\n131840\n1\n262153\n1\nx\n");
    }

    /*#[test]
    fn env() {
        // saveRDS(new.env(), stdout(), ascii=TRUE)
        let locked = false;
        let enclos = Obj::Global(None);
        let frame = Obj::null();
        let keyvals = Vec::new();
        let obj = Obj::env(locked, enclos, frame, keyvals);
        let s = write_ascii(&obj, false);
        assert_eq!(s, "A\n2\n197636\n131840\n4\n0\n253\n254\n19\n29\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n254\n");
    }*/

    #[test]
    fn int() {
        // saveRDS(c(1L, 2L, 3L), stdout(), ascii=TRUE)
        let obj = Obj::integer(vec![1, 2, 3]);
        let s = write_ascii(&obj, false);
        assert_eq!(s, "A\n2\n197636\n131840\n13\n3\n1\n2\n3\n");
    }

    #[test]
    fn real() {
        // saveRDS(c(1, 2, 3), stdout(), ascii=TRUE)
        let obj = Obj::real(vec![1., 2., 3.]);
        let s = write_ascii(&obj, false);
        assert_eq!(s, "A\n2\n197636\n131840\n14\n3\n1\n2\n3\n");
    }

    #[test]
    fn attr() {
        // saveRDS(structure(c(1, 2, 3), x=4), stdout(), ascii=TRUE)
        let mut obj = Obj::real(vec![1., 2., 3.]);
        obj.add_attr("x", 4.);
        let s = write_ascii(&obj, false);
        assert_eq!(s, "A\n2\n197636\n131840\n526\n3\n1\n2\n3\n1026\n1\n262153\n1\nx\n14\n1\n4\n254\n");
    }

    #[test]
    fn attrx2() {
        //saveRDS(structure(c(1, 2, 3), x=4, y=5), stdout(), ascii=TRUE)
        let mut obj = Obj::real(vec![1., 2., 3.]);
        obj.add_attr("x", 4.);
        obj.add_attr("y", 5.);
        let s = write_ascii(&obj, false);
        assert_eq!(s, "A\n2\n197636\n131840\n526\n3\n1\n2\n3\n1026\n1\n262153\n1\nx\n14\n1\n4\n1026\n1\n262153\n1\ny\n14\n1\n5\n254\n");
    }

    #[test]
    fn attr_nested() {
        //saveRDS(structure(c(1, 2, 3), x=4, y=structure(5, z=6)), stdout(), ascii=TRUE)
        let mut obj = Obj::real(vec![1., 2., 3.]);
        obj.add_attr("x", 4.);
        let mut y = Obj::real(vec![5.]);
        y.add_attr("z", 6.);
        obj.add_attr("y", y);
        let s = write_ascii(&obj, false);
        assert_eq!(s, "A\n2\n197636\n131840\n526\n3\n1\n2\n3\n1026\n1\n262153\n1\nx\n14\n1\n4\n1026\n1\n262153\n1\ny\n526\n1\n5\n1026\n1\n262153\n1\nz\n14\n1\n6\n254\n254\n");
    }

    #[test]
    fn unicode() {
        // saveRDS("😀", stdout(), ascii=TRUE)
        let s = write_ascii(&Obj::from("😀"), false);
        // note: needs 0x8009 (UTF8), not 0x40009 (ASCII)
        assert_eq!(s, "A\n2\n197636\n131840\n16\n1\n32777\n4\n\\360\\237\\230\\200\n");
    }

    #[test]
    fn data_frame() {
        //saveRDS(data.frame(a = c(1, 2)), stdout(), ascii = TRUE)
        let obj = Obj::data_frame(
            vec![Obj::real(vec![1., 2.])],
            vec!["a"],
        );
        eprintln!("{:?}", &obj);
        let s = write_ascii(&obj, false);
        assert_eq!(s, "A\n2\n197636\n131840\n787\n1\n14\n2\n1\n2\n1026\n1\n262153\n5\nnames\n16\n1\n262153\n1\na\n1026\n1\n262153\n9\nrow.names\n13\n2\nNA\n-2\n1026\n1\n262153\n5\nclass\n16\n1\n262153\n10\ndata.frame\n254\n");
    }

}

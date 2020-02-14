
use std::io::Write;

use crate::{Obj, Result, Obe, Error, Symbol, Env};

pub struct WriteOptions {
    is_ascii: bool,
}

impl WriteOptions {
    pub fn new() -> Self {
        Self {
            is_ascii: false,
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
/// assert_eq!(dest.into_inner(), [66, 10, 0, 0, 0, 2, 0, 3, 4, 4, 0, 2, 3, 0])
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
    /// assert_eq!(dest.into_inner(), [66, 10, 0, 0, 0, 2, 0, 3, 4, 4, 0, 2, 3, 0])
    /// ```
    pub fn try_new(dest: W, opt: WriteOptions) -> Result<Self> {
        let mut w = Self {
            dest, opt
        };

        if w.opt.is_ascii {
            w.dest.write(&[b'A', b'\n'])?;
        } else {
            w.dest.write(&[b'B', b'\n'])?;
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
    /// assert_eq!(dest.into_inner(), [66, 10, 0, 0, 0, 2, 0, 3, 4, 4, 0, 2, 3, 0])
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
        } else {
            self.dest.write(bytes)?;
        }
        Ok(())
    }

    // Write the start of an object.
    fn write_flags(&mut self, obe: &Obe, t: i32) -> Result<()> {
        self.integer(t | match obe {
            &Some(ref extras) => {
                let mut bits = extras.levels << 12;
                if extras.is_obj {
                    bits |= 0x100;
                }
                if !extras.attr.is_null() {
                    bits |= 0x200;
                }
                if !extras.tag.is_null() {
                    bits |= 0x400;
                }
                bits
            }
            _ => 0
        })?;
        match obe {
            &Some(ref extras) => {
                if !extras.attr.is_null() {
                    self.write_object(&extras.attr)?;
                }
                if !extras.tag.is_null() {
                    self.write_object(&extras.tag)?;
                }
                Ok(())
            }
            _ => Ok(())
        }
    }

    // Write a symbol.
    fn write_sym(&mut self, obe: &Obe, val: &Symbol) -> Result<()> {
        // TODO: handle refs.
        self.write_flags(&obe, 1)?;
        self.write_object(&Obj::from(&val.name))
    }

    // Write an environment (stack frame etc).
    fn write_env(&mut self, _obe: &Obe, _val: &Env) -> Result<()> {
        // This is quite complex as the hash table must match the algorithm in the
        // R source code.
        //panic!("not implemented");
        self.integer(4)
        //self.write_object(&Obj::from(val.name))
    }

    // Write a linked list.
    fn write_list(&mut self, _obe: &Obe, _val: &Vec<(Obj, Obj)>, t: i32) -> Result<()> {
        self.integer(t | 0x200)?;
        /*for (t, o) in val {
            if !t.is_null() {

            }
        }*/
        Ok(())
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
        Ok(())
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
        Ok(())
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
        Ok(())
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
        Ok(())
    }

    // Write a raw object.
    fn write_raw(&mut self, obe: &Obe, val: &Vec<u8>) -> Result<()> {
        self.write_flags(&obe, 24)?;
        let len32 = val.len() as i32;
        if len32 as usize != val.len() { return Err(Error::from("vector too long for R format")); }
        self.integer(len32)?;
        if self.opt.is_ascii {
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
            Obj::List(ref obe, ref val) => self.write_list(obe, val, 2),
            Obj::Closure(ref obe, ref val) => self.write_list(obe, val, 3),
            Obj::Promise(ref obe, ref val) => self.write_list(obe, val, 5),
            Obj::Lang(ref obe, ref val) => self.write_list(obe, val, 6),
            Obj::Dot(ref obe, ref val) => self.write_list(obe, val, 17),
            Obj::Special(ref obe, ref val) => self.write_char(obe, val, 7),
            Obj::Builtin(ref obe, ref val) => self.write_char(obe, val, 8),
            Obj::Char(ref obe, ref val) => self.write_char(obe, val, 9),
            Obj::Logical(ref obe, ref val) => self.write_int(obe, val, 10),
            Obj::Int(ref obe, ref val) => self.write_int(obe, val, 13),
            Obj::Real(ref obe, ref val) => self.write_real(obe, val),
            Obj::Cplx(ref obe, ref val) => self.write_cplx(obe, val),
            Obj::Str(ref obe, ref val) => self.write_obj(obe, val, 16),
            Obj::Obj(ref obe, ref val) => self.write_obj(obe, val, 19),
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

    fn write_ascii(obj: &Obj) -> String {
        let buf = Vec::new();
        let mut opt = WriteOptions::new();
        opt.is_ascii = true;
        let mut dest = Writer::try_new(buf, opt).unwrap();
        dest.write_object(&obj).unwrap();
        String::from_utf8(dest.into_inner()).unwrap()
    }

    #[test]
    fn int() {
        let obj = Obj::integer(vec![1, 2, 3]);
        let s = write_ascii(&obj);
        assert_eq!(s, "A\n2\n197636\n131840\n13\n3\n1\n2\n3\n");
    }

    #[test]
    fn real() {
        let obj = Obj::real(vec![1., 2., 3.]);
        let s = write_ascii(&obj);
        assert_eq!(s, "A\n2\n197636\n131840\n14\n3\n1\n2\n3\n");
    }

}

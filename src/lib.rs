
mod obj;
mod reader;
mod writer;
mod api;

pub use api::*;

pub use reader::Reader;
pub use writer::{Writer, WriteOptions};

pub type Error = Box<dyn std::error::Error>;
pub type Result<T> = std::result::Result<T, Error>;

pub use obj::{Obj, Obe, Extras, Symbol, Env};

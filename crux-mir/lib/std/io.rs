use core::cmp;
use core::result;

pub use self::cursor::Cursor;

#[derive(Debug)]
pub struct Error {
}

pub type Result<T> = result::Result<T, Error>;

pub trait Read {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize>;

    #[cfg(off)] fn read_vectored(&mut self, bufs: &mut [IoSliceMut]) -> Result<usize> {
        unimplemented!()
    }

    #[cfg(off)] unsafe fn initializer(&self) -> Initializer {
        unimplemented!()
    }

    #[cfg(off)] fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize> {
        unimplemented!()
    }

    #[cfg(off)] fn read_to_string(&mut self, buf: &mut String) -> Result<usize> {
        unimplemented!()
    }

    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        let len = self.read(buf)?;
        assert!(len == buf.len());
        Ok(())
    }

    fn by_ref(&mut self) -> &mut Self where Self: Sized { self }

    #[cfg(off)] fn bytes(self) -> Bytes<Self> where Self: Sized {
        unimplemented!()
    }

    #[cfg(off)] fn chain<R: Read>(self, next: R) -> Chain<Self, R> where Self: Sized {
        unimplemented!()
    }

    #[cfg(off)] fn take(self, limit: u64) -> Take<Self> where Self: Sized {
        unimplemented!()
    }
}

pub trait Write {
    fn write(&mut self, buf: &[u8]) -> Result<usize>;
    fn flush(&mut self) -> Result<()>;

    #[cfg(off)] fn write_vectored(&mut self, bufs: &[IoSlice]) -> Result<usize> {
        unimplemented!()
    }

    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        let len = self.write(buf)?;
        assert!(len == buf.len());
        Ok(())
    }

    #[cfg(off)] fn write_fmt(&mut self, fmt: Arguments) -> Result<()> {
        unimplemented!()
    }

    fn by_ref(&mut self) -> &mut Self where Self: Sized { self }
}


mod cursor {
    use super::*;

    pub struct Cursor<T> {
        buf: T,
        pos: usize,
    }

    impl<T> Cursor<T> {
        pub fn new(buf: T) -> Cursor<T> {
            Cursor {
                buf,
                pos: 0,
            }
        }

        pub fn into_inner(self) -> T {
            self.buf
        }

        pub fn get_ref(&self) -> &T {
            &self.buf
        }

        pub fn get_mut(&mut self) -> &mut T {
            &mut self.buf
        }

        pub fn position(&self) -> u64 {
            self.pos as u64
        }
    }

    impl<T: AsRef<[u8]>> Read for Cursor<T> {
        fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
            let self_buf = self.buf.as_ref();
            let end = cmp::min(self_buf.len(), self.pos + buf.len());
            let len = end - self.pos;
            buf[..len].copy_from_slice(&self_buf[self.pos .. end]);
            self.pos += len;
            Ok(len)
        }
    }

    impl Write for Cursor<&mut [u8]> {
        fn write(&mut self, buf: &[u8]) -> Result<usize> {
            let end = cmp::min(self.buf.len(), self.pos + buf.len());
            let len = end - self.pos;
            self.buf[self.pos .. end].copy_from_slice(&buf[..len]);
            self.pos += len;
            Ok(len)
        }

        fn flush(&mut self) -> Result<()> {
            Ok(())
        }
    }
}


#[derive(Debug)]
pub struct Sink;

impl Write for Sink {
    fn write(&mut self, buf: &[u8]) -> Result<usize> { Ok(buf.len()) }
    fn flush(&mut self) -> Result<()> { Ok(()) }
}

use crate::cmp;
use crate::io::{self, SeekFrom, Read, Initializer, Write, Seek, BufRead, Error, ErrorKind,
        IoSliceMut, IoSlice};
use crate::fmt;
use crate::mem;

// =============================================================================
// Forwarding implementations

#[stable(feature = "rust1", since = "1.0.0")]
impl<R: Read + ?Sized> Read for &mut R {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        (**self).read(buf)
    }

    #[inline]
    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        (**self).read_vectored(bufs)
    }

    #[inline]
    unsafe fn initializer(&self) -> Initializer {
        (**self).initializer()
    }

    #[inline]
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        (**self).read_to_end(buf)
    }

    #[inline]
    fn read_to_string(&mut self, buf: &mut String) -> io::Result<usize> {
        (**self).read_to_string(buf)
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
        (**self).read_exact(buf)
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<W: Write + ?Sized> Write for &mut W {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> { (**self).write(buf) }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        (**self).write_vectored(bufs)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> { (**self).flush() }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        (**self).write_all(buf)
    }

    #[inline]
    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> io::Result<()> {
        (**self).write_fmt(fmt)
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<S: Seek + ?Sized> Seek for &mut S {
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> { (**self).seek(pos) }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<B: BufRead + ?Sized> BufRead for &mut B {
    #[inline]
    fn fill_buf(&mut self) -> io::Result<&[u8]> { (**self).fill_buf() }

    #[inline]
    fn consume(&mut self, amt: usize) { (**self).consume(amt) }

    #[inline]
    fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> io::Result<usize> {
        (**self).read_until(byte, buf)
    }

    #[inline]
    fn read_line(&mut self, buf: &mut String) -> io::Result<usize> {
        (**self).read_line(buf)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<R: Read + ?Sized> Read for Box<R> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        (**self).read(buf)
    }

    #[inline]
    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        (**self).read_vectored(bufs)
    }

    #[inline]
    unsafe fn initializer(&self) -> Initializer {
        (**self).initializer()
    }

    #[inline]
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        (**self).read_to_end(buf)
    }

    #[inline]
    fn read_to_string(&mut self, buf: &mut String) -> io::Result<usize> {
        (**self).read_to_string(buf)
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
        (**self).read_exact(buf)
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<W: Write + ?Sized> Write for Box<W> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> { (**self).write(buf) }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        (**self).write_vectored(bufs)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> { (**self).flush() }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        (**self).write_all(buf)
    }

    #[inline]
    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> io::Result<()> {
        (**self).write_fmt(fmt)
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<S: Seek + ?Sized> Seek for Box<S> {
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> { (**self).seek(pos) }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<B: BufRead + ?Sized> BufRead for Box<B> {
    #[inline]
    fn fill_buf(&mut self) -> io::Result<&[u8]> { (**self).fill_buf() }

    #[inline]
    fn consume(&mut self, amt: usize) { (**self).consume(amt) }

    #[inline]
    fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> io::Result<usize> {
        (**self).read_until(byte, buf)
    }

    #[inline]
    fn read_line(&mut self, buf: &mut String) -> io::Result<usize> {
        (**self).read_line(buf)
    }
}

// Used by panicking::default_hook
#[cfg(test)]
/// This impl is only used by printing logic, so any error returned is always
/// of kind `Other`, and should be ignored.
impl Write for Box<dyn (::realstd::io::Write) + Send> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        (**self).write(buf).map_err(|_| ErrorKind::Other.into())
    }

    fn flush(&mut self) -> io::Result<()> {
        (**self).flush().map_err(|_| ErrorKind::Other.into())
    }
}

// =============================================================================
// In-memory buffer implementations

/// Read is implemented for `&[u8]` by copying from the slice.
///
/// Note that reading updates the slice to point to the yet unread part.
/// The slice will be empty when EOF is reached.
#[stable(feature = "rust1", since = "1.0.0")]
impl Read for &[u8] {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let amt = cmp::min(buf.len(), self.len());
        let (a, b) = self.split_at(amt);

        // First check if the amount of bytes we want to read is small:
        // `copy_from_slice` will generally expand to a call to `memcpy`, and
        // for a single byte the overhead is significant.
        if amt == 1 {
            buf[0] = a[0];
        } else {
            buf[..amt].copy_from_slice(a);
        }

        *self = b;
        Ok(amt)
    }

    #[inline]
    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        let mut nread = 0;
        for buf in bufs {
            nread += self.read(buf)?;
            if self.is_empty() {
                break;
            }
        }

        Ok(nread)
    }

    #[inline]
    unsafe fn initializer(&self) -> Initializer {
        Initializer::nop()
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
        if buf.len() > self.len() {
            return Err(Error::new(ErrorKind::UnexpectedEof,
                                  "failed to fill whole buffer"));
        }
        let (a, b) = self.split_at(buf.len());

        // First check if the amount of bytes we want to read is small:
        // `copy_from_slice` will generally expand to a call to `memcpy`, and
        // for a single byte the overhead is significant.
        if buf.len() == 1 {
            buf[0] = a[0];
        } else {
            buf.copy_from_slice(a);
        }

        *self = b;
        Ok(())
    }

    #[inline]
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        buf.extend_from_slice(*self);
        let len = self.len();
        *self = &self[len..];
        Ok(len)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl BufRead for &[u8] {
    #[inline]
    fn fill_buf(&mut self) -> io::Result<&[u8]> { Ok(*self) }

    #[inline]
    fn consume(&mut self, amt: usize) { *self = &self[amt..]; }
}

/// Write is implemented for `&mut [u8]` by copying into the slice, overwriting
/// its data.
///
/// Note that writing updates the slice to point to the yet unwritten part.
/// The slice will be empty when it has been completely overwritten.
#[stable(feature = "rust1", since = "1.0.0")]
impl Write for &mut [u8] {
    #[inline]
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        let amt = cmp::min(data.len(), self.len());
        let (a, b) = mem::replace(self, &mut []).split_at_mut(amt);
        a.copy_from_slice(&data[..amt]);
        *self = b;
        Ok(amt)
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        let mut nwritten = 0;
        for buf in bufs {
            nwritten += self.write(buf)?;
            if self.is_empty() {
                break;
            }
        }

        Ok(nwritten)
    }

    #[inline]
    fn write_all(&mut self, data: &[u8]) -> io::Result<()> {
        if self.write(data)? == data.len() {
            Ok(())
        } else {
            Err(Error::new(ErrorKind::WriteZero, "failed to write whole buffer"))
        }
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

/// Write is implemented for `Vec<u8>` by appending to the vector.
/// The vector will grow as needed.
#[stable(feature = "rust1", since = "1.0.0")]
impl Write for Vec<u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.extend_from_slice(buf);
        Ok(buf.len())
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        let len = bufs.iter().map(|b| b.len()).sum();
        self.reserve(len);
        for buf in bufs {
            self.extend_from_slice(buf);
        }
        Ok(len)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.extend_from_slice(buf);
        Ok(())
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

#[cfg(test)]
mod tests {
    use crate::io::prelude::*;

    #[bench]
    fn bench_read_slice(b: &mut test::Bencher) {
        let buf = [5; 1024];
        let mut dst = [0; 128];

        b.iter(|| {
            let mut rd = &buf[..];
            for _ in 0..8 {
                let _ = rd.read(&mut dst);
                test::black_box(&dst);
            }
        })
    }

    #[bench]
    fn bench_write_slice(b: &mut test::Bencher) {
        let mut buf = [0; 1024];
        let src = [5; 128];

        b.iter(|| {
            let mut wr = &mut buf[..];
            for _ in 0..8 {
                let _ = wr.write_all(&src);
                test::black_box(&wr);
            }
        })
    }

    #[bench]
    fn bench_read_vec(b: &mut test::Bencher) {
        let buf = vec![5; 1024];
        let mut dst = [0; 128];

        b.iter(|| {
            let mut rd = &buf[..];
            for _ in 0..8 {
                let _ = rd.read(&mut dst);
                test::black_box(&dst);
            }
        })
    }

    #[bench]
    fn bench_write_vec(b: &mut test::Bencher) {
        let mut buf = Vec::with_capacity(1024);
        let src = [5; 128];

        b.iter(|| {
            let mut wr = &mut buf[..];
            for _ in 0..8 {
                let _ = wr.write_all(&src);
                test::black_box(&wr);
            }
        })
    }
}

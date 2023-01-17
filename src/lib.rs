use std::{string::FromUtf8Error, cmp};

#[derive(Clone)]
pub struct Binary<'a> {
    pub buffer: &'a [u8],
    cursor: usize,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidUTF8(FromUtf8Error),
    NotNullTerminated,
    BufferOverrun(usize, usize),
}

pub enum ParsingLength {
    Unlimited,
    Fixed(usize),
    Max(usize),
}

macro_rules! parse_impl {
    (le => $func:ident, $typ:tt) => {
        pub fn $func(&mut self) -> Result<$typ, Error> {
            if self.cursor+std::mem::size_of::<$typ>() > self.buffer.len() {
                return Err(Error::BufferOverrun(self.cursor, self.buffer.len()));
            }
            let buf = &self.buffer[self.cursor..self.cursor+std::mem::size_of::<$typ>()];
            let x = $typ::from_le_bytes(buf.try_into().unwrap());
            self.cursor += std::mem::size_of::<$typ>();
            Ok(x)
        }
    };
    (be => $func:ident, $typ:tt) => {
        pub fn $func(&mut self) -> Result<$typ, Error> {
            if self.cursor+std::mem::size_of::<$typ>() > self.buffer.len() {
                return Err(Error::BufferOverrun(self.cursor, self.buffer.len()));
            }
            let buf = &self.buffer[self.cursor..self.cursor+std::mem::size_of::<$typ>()];
            let x = $typ::from_be_bytes(buf.try_into().unwrap());
            self.cursor += std::mem::size_of::<$typ>();
            Ok(x)
        }
    };
}

impl<'a> Binary<'a> { 
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            buffer: buf,
            cursor: 0,
        }
    }

    pub fn slice(&self, len: usize) -> Result<Binary<'a>, Error> {
        if self.cursor+len > self.buffer.len() {
            return Err(Error::BufferOverrun(self.cursor, self.buffer.len()));
        }
        Ok(Binary {
            buffer: &self.buffer[self.cursor..self.cursor+len],
            cursor: 0,
        })
    }

    pub fn length(&self) -> usize {
        self.buffer.len()
    }

    pub fn remaining(&self) -> usize {
        self.buffer.len() - self.cursor
    }

    pub fn seek(&mut self, pos: usize) {
        assert!(pos < self.buffer.len());
        self.cursor = pos;
    }

    pub fn skip(&mut self, n: usize) {
        assert!(self.cursor+n <= self.buffer.len());
        self.cursor += n;
    }

    pub fn position(&self) -> usize {
        self.cursor
    }

    pub fn parse_bytes<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        if self.cursor+N > self.buffer.len() {
            return Err(Error::BufferOverrun(self.cursor, self.buffer.len()));
        }
        let mut buf = [0u8; N];
        buf.copy_from_slice(&self.buffer[self.cursor..self.cursor+N]);
        self.cursor += N;
        Ok(buf)
    }

    pub fn parse_buffer(&mut self, length: usize) -> Result<&'a [u8], Error> {
        if self.cursor+length > self.buffer.len() {
            return Err(Error::BufferOverrun(self.cursor, self.buffer.len()));
        }
        let buf = &self.buffer[self.cursor..self.cursor+length];
        self.cursor += length;
        Ok(buf)
    }

    pub fn get_buffer(&self, start: usize, length: usize) -> Result<&'a [u8], Error> {
        if start+length > self.buffer.len() {
            return Err(Error::BufferOverrun(start, self.buffer.len()));
        }
        Ok(&self.buffer[start..start+length])
    }

    pub fn parse_string(&mut self, length: usize) -> Result<String, Error> {
        if self.cursor+length > self.buffer.len() {
            return Err(Error::BufferOverrun(self.cursor, self.buffer.len()));
        }
        match String::from_utf8(self.buffer[self.cursor..self.cursor+length].to_vec()) {
            Ok(s) => {
                self.cursor += length;
                Ok(s)
            }
            Err(e) => Err(Error::InvalidUTF8(e)),
        }
    }

    pub fn parse_null_terminated_string(&mut self, length: ParsingLength) -> Result<String, Error> {
        let end_pos = self.buffer.iter().skip(self.cursor).position(|&x| x == b'\0');
        match end_pos {
            None => Err(Error::NotNullTerminated),
            Some(end_pos) => {
                let max_pos = match length {
                    ParsingLength::Unlimited => end_pos,
                    ParsingLength::Fixed(length) => cmp::min(length, end_pos),
                    ParsingLength::Max(length) => cmp::min(length, end_pos),
                };
                let str = String::from_utf8(self.buffer[self.cursor..self.cursor+max_pos].to_vec());
                match (str, length) {
                    (Ok(s), ParsingLength::Fixed(length)) => {
                        self.cursor += length;
                        Ok(s)
                    }
                    (Ok(s), ParsingLength::Max(length)) => {
                        self.cursor += cmp::min(length, max_pos + 1);
                        Ok(s)
                    }
                    (Ok(s), ParsingLength::Unlimited) => {
                        self.cursor += max_pos + 1;
                        Ok(s)
                    }
                    (Err(e), _) => Err(Error::InvalidUTF8(e)),
                }
            }
        }
    }

    pub fn parse_u8(&mut self) -> Result<u8, Error> {
        if self.cursor+1 > self.buffer.len() {
            return Err(Error::BufferOverrun(self.cursor, self.buffer.len()));
        }
        let x = self.buffer[self.cursor];
        self.cursor += 1;
        Ok(x)
    }

    parse_impl!(le => parse_u16_le, u16);
    parse_impl!(le => parse_u32_le, u32);
    parse_impl!(le => parse_u64_le, u64);
    parse_impl!(le => parse_u128_le, u128);
    parse_impl!(le => parse_i16_le, i16);
    parse_impl!(le => parse_i32_le, i32);
    parse_impl!(le => parse_i64_le, i64);
    parse_impl!(le => parse_i128_le, i128);

    parse_impl!(be => parse_u16_be, u16);
    parse_impl!(be => parse_u32_be, u32);
    parse_impl!(be => parse_u64_be, u64);
    parse_impl!(be => parse_u128_be, u128);
    parse_impl!(be => parse_i16_be, i16);
    parse_impl!(be => parse_i32_be, i32);
    parse_impl!(be => parse_i64_be, i64);
    parse_impl!(be => parse_i128_be, i128);
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! binary {
        ($vector:expr) => {
            Binary::new($vector.as_ref())
        };
    }

    #[test]
    fn seeking() {
        let mut bin = binary!([0x4d, 0x45, 0x54, 0x41]);
        bin.seek(3);
    }

    #[test]
    #[should_panic]
    fn seeking_fail() {
        let mut bin = binary!([0x4d, 0x45, 0x54, 0x41]);
        bin.seek(9);
    }

    #[test]
    fn parsing_bytes() {
        let mut bin = binary!([0x4d, 0x45, 0x54, 0x41]);
        assert_eq!(bin.parse_bytes::<2>(), Ok([0x4d, 0x45]));
        assert_eq!(bin.parse_bytes::<2>(), Ok([0x54, 0x41]));
    }

    #[test]
    fn parse_string() {
        let mut bin = binary!(b"META");
        assert_eq!(bin.parse_string(4).unwrap(), "META");
    }

    #[test]
    fn parse_u8() {
        let mut bin = binary!([0x4d, 0x45, 0x54, 0x41]);
        assert_eq!(bin.parse_u8(), Ok(0x4d));
        assert_eq!(bin.parse_u8(), Ok(0x45));
        assert_eq!(bin.parse_u8(), Ok(0x54));
        assert_eq!(bin.parse_u8(), Ok(0x41));
    }

    #[test]
    fn parse_null_terminated_string() {
        let mut bin = binary!(b"META\0");
        assert_eq!(bin.parse_null_terminated_string(ParsingLength::Unlimited).unwrap(), "META");
        let mut bin2 = binary!(b"META\0\0MORESTUYFULL\0\0");
        assert_eq!(bin2.parse_null_terminated_string(ParsingLength::Unlimited).unwrap(), "META");
        assert_eq!(bin2.parse_null_terminated_string(ParsingLength::Unlimited).unwrap(), "");
        assert_eq!(bin2.parse_null_terminated_string(ParsingLength::Unlimited).unwrap(), "MORESTUYFULL");
        let mut bin3 = binary!(b"\0\0\0META\0\0MORESTUYFULL\0\0");
        assert_eq!(bin3.parse_null_terminated_string(ParsingLength::Unlimited).unwrap(), "");
    }

}
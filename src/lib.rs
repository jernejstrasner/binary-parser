use std::string::FromUtf8Error;

#[derive(Clone)]
pub struct Binary<'a> {
    pub buffer: &'a [u8],
    cursor: usize,
}

#[derive(Debug)]
pub enum Error {
    InvalidUTF8,
    NotNullTerminated,
}

macro_rules! parse_impl {
    (le => $func:ident, $typ:tt) => {
        pub fn $func(&mut self) -> $typ {
            assert!(self.cursor+std::mem::size_of::<$typ>() <= self.buffer.len());
            let buf = &self.buffer[self.cursor..self.cursor+std::mem::size_of::<$typ>()];
            let x = $typ::from_le_bytes(buf.try_into().unwrap());
            self.cursor += std::mem::size_of::<$typ>();
            x
        }
    };
    (be => $func:ident, $typ:tt) => {
        pub fn $func(&mut self) -> $typ {
            assert!(self.cursor+std::mem::size_of::<$typ>() <= self.buffer.len());
            let buf = &self.buffer[self.cursor..self.cursor+std::mem::size_of::<$typ>()];
            let x = $typ::from_be_bytes(buf.try_into().unwrap());
            self.cursor += std::mem::size_of::<$typ>();
            x
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

    pub fn parse_bytes<const N: usize>(&mut self) -> [u8; N] {
        assert!(self.cursor+N <= self.buffer.len());
        let mut buf = [0u8; N];
        buf.copy_from_slice(&self.buffer[self.cursor..self.cursor+N]);
        self.cursor += N;
        buf
    }

    pub fn parse_buffer(&mut self, length: usize) -> &'a [u8] {
        assert!(self.cursor+length <= self.buffer.len());
        let buf = &self.buffer[self.cursor..self.cursor+length];
        self.cursor += length;
        buf
    }

    pub fn get_buffer(&self, start: usize, length: usize) -> &'a [u8] {
        assert!(start+length <= self.buffer.len());
        &self.buffer[start..start+length]
    }

    pub fn parse_string(&mut self, length: usize) -> Result<String, FromUtf8Error> {
        assert!(self.cursor+length <= self.buffer.len());
        let s = String::from_utf8(self.buffer[self.cursor..self.cursor+length].to_vec());
        if s.is_ok() {
            self.cursor += length;
        }
        s
    }

    pub fn parse_null_terminated_string(&mut self) -> Result<String, Error> {
        let end_pos = self.buffer.iter().skip(self.cursor).position(|&x| x == b'\0');
        match end_pos {
            None => Err(Error::NotNullTerminated),
            Some(end_pos) => self.parse_string(end_pos-self.cursor).map_err(|_| Error::NotNullTerminated),
        }
    }

    pub fn parse_u8(&mut self) -> u8 {
        assert!(self.cursor+1 <= self.buffer.len());
        let x = self.buffer[self.cursor];
        self.cursor += 1;
        x
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
        assert_eq!(bin.parse_bytes::<2>(), [0x4d, 0x45]);
        assert_eq!(bin.parse_bytes::<2>(), [0x54, 0x41]);
    }

    #[test]
    fn parse_string() {
        let mut bin = binary!(b"META");
        assert_eq!(bin.parse_string(4).unwrap(), "META");
    }

    #[test]
    fn parse_u8() {
        let mut bin = binary!([0x4d, 0x45, 0x54, 0x41]);
        assert_eq!(bin.parse_u8(), 0x4d);
        assert_eq!(bin.parse_u8(), 0x45);
        assert_eq!(bin.parse_u8(), 0x54);
        assert_eq!(bin.parse_u8(), 0x41);
    }

    #[test]
    fn parse_null_terminated_string() {
        let mut bin = binary!(b"META\0");
        assert_eq!(bin.parse_null_terminated_string().unwrap(), "META");
        let mut bin2 = binary!(b"META\0\0MORESTUYFULL\0\0");
        assert_eq!(bin2.parse_null_terminated_string().unwrap(), "META");
        let mut bin3 = binary!(b"\0\0\0META\0\0MORESTUYFULL\0\0");
        assert_eq!(bin3.parse_null_terminated_string().unwrap(), "");
    }

}
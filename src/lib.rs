use std::string::FromUtf8Error;

#[derive(Clone)]
pub struct Binary<'a> {
    pub buffer: &'a [u8],
    cursor: usize,
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

    pub fn parse_string(&mut self, length: usize) -> Result<String, FromUtf8Error> {
        assert!(self.cursor+length <= self.buffer.len());
        let s = String::from_utf8(self.buffer[self.cursor..self.cursor+length].to_vec());
        if s.is_ok() {
            self.cursor += length;
        }
        s
    }

    parse_impl!(le => parse_u8, u8);
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
}
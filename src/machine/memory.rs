use std::collections::HashMap;

pub struct HashMemory(HashMap<u64, u8>);

impl HashMemory {
    #[allow(dead_code)]
    pub fn new() -> HashMemory {
        return HashMemory(HashMap::new())
    }

    pub fn from(map: HashMap<u64, u8>) -> HashMemory {
        return HashMemory(map)
    }
}

impl Memory for HashMemory {
    fn get(&self, index: u64) -> u8 {
        *self.0.get(&index).unwrap_or(&0x00u8)
    }

    fn set(&mut self, index: u64, data: u8) {
        self.0.insert(index, data);
    }
}

macro_rules! create_load_fn {
    (load_byte, u8, 1) => {
        fn load_byte(&self, address: u64) -> u8 {
            self.get(address)
        }
    };
    ($name:ident, $ty:ty, $byte_count:literal) => {
        fn $name(&self, address: u64) -> $ty {
            let k = self.index(address, $byte_count);
            let mut s: $ty = 0;
            for i in 0..$byte_count {
                let b: $ty = self.get(k+i).into();
                s = (s << 8) |b;
            }
            s
        }
    };
}

macro_rules! create_store_fn {
    (store_byte, u8, 1) => {
        fn store_byte(&mut self, address: u64, data: u8) {
            self.set(address, data)
        }
    };
    ($name:ident, $ty:ty, $byte_count:literal) => {
        fn $name(&mut self, address: u64, data: $ty) {
            let k = self.index(address, $byte_count);
            for i in 0..$byte_count {
                self.set(k+i, (data >> (8*($byte_count-1-i))) as u8);
            }
        }
    };
}

pub trait Memory {
    fn get(&self, index: u64) -> u8;
    fn set(&mut self, index: u64, data: u8);

    fn index(&self, address: u64, byte_count: u64) -> u64 {
        address - address % byte_count
    }

    create_load_fn!(load_byte, u8, 1);
    create_load_fn!(load_wyde, u16, 2);
    create_load_fn!(load_tetra, u32, 4);
    create_load_fn!(load_octa, u64, 8);

    create_store_fn!(store_byte, u8, 1);
    create_store_fn!(store_wyde, u16, 2);
    create_store_fn!(store_tetra, u32, 4);
    create_store_fn!(store_octa, u64, 8);
}

#[cfg(test)]
mod tests {
    use super::*;

    // M[1000]M[1001]...M[1007] = 0x0123_4567_89ab_cdef
    fn memory_for_tests() -> HashMemory {
        let mut m = HashMap::new();
        m.insert(1000, 0x01u8);
        m.insert(1001, 0x23u8);
        m.insert(1002, 0x45u8);
        m.insert(1003, 0x67u8);
        m.insert(1004, 0x89u8);
        m.insert(1005, 0xabu8);
        m.insert(1006, 0xcdu8);
        m.insert(1007, 0xefu8);
        return HashMemory(m)
    }

    #[test]
    fn test_memory_load() {
        let m = memory_for_tests();
        assert_eq!(m.load_byte(999), 0x00u8);
        assert_eq!(m.load_byte(1002), 0x45u8);
        assert_eq!(m.load_wyde(1003), 0x45_67u16);
        assert_eq!(m.load_tetra(1005), 0x89_ab_cd_efu32);
        assert_eq!(m.load_octa(1006), 0x01_23_45_67_89_ab_cd_efu64);
    }

    #[test]
    fn test_multibyte_memory_load() {
        let m = memory_for_tests();
        let n = 1000;

        for i in 0..8 {
            let j = i / 2 * 2;
            assert_eq!(
                m.load_wyde(n + i),
                m.load_wyde(n + j),
                "m.load_wyde({:?}) should equal m.wyde({:?})",
                n + i,
                n + j
            );
        }

        for i in 0..8 {
            let j = i / 4 * 4;
            assert_eq!(m.load_tetra(n + i), m.load_tetra(n + j));
        }

        for i in 0..8 {
            assert_eq!(m.load_octa(n), m.load_octa(n + i));
        }
    }

    #[test]
    fn test_memory_store_byte() {
        let mut m = memory_for_tests();
        m.store_byte(1002, 0x00u8);
        assert_eq!(m.load_octa(1002), 0x01_23_00_67_89_ab_cd_efu64);
    }

    #[test]
    fn test_memory_store_wyde() {
        let mut m = memory_for_tests();
        m.store_wyde(1002, 0x00_00u16);
        assert_eq!(m.load_octa(1002), 0x01_23_00_00_89_ab_cd_efu64);
    }

    #[test]
    fn test_memory_store_tetra() {
        let mut m = memory_for_tests();
        let expect = 0xff_ff_00_00_89_ab_cd_efu64;
        m.store_tetra(1002, 0xff_ff_00_00u32);
        assert_eq!(m.load_octa(1002), expect, "should be 0x{:x?}, but is 0x{:x?}", expect, m.load_octa(1002));
    }

    #[test]
    fn test_memory_store_octa() {
        let mut m = memory_for_tests();
        let expect = 0xff_ff_ff_ff_ff_ff_00_00u64; 
        m.store_octa(1002, 0xff_ff_ff_ff_ff_ff_00_00u64);
        assert_eq!(m.load_octa(1002), expect, "should be 0x{:x?}, but is 0x{:x?}", expect, m.load_octa(1002));
    }
}

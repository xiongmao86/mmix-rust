use std::collections::HashMap;

struct HashMemory(HashMap<u64, u8>);

impl HashMemory {
    fn new() -> HashMemory {
        return HashMemory(HashMap::new())
    }

    fn from(map: HashMap<u64, u8>) -> HashMemory {
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

trait Memory {
    fn get(&self, index: u64) -> u8;
    fn set(&mut self, index: u64, data: u8);

    fn index(&self, address: u64, byte_count: u64) -> u64 {
        address - address % byte_count
    }

    fn load_byte(&self, address: u64) -> u8 {
        self.get(address)
    }

    fn store_byte(&mut self, address: u64, data: u8) {
        self.set(address, data)
    }

    fn load_wyde(&self, address: u64) -> u16 {
        let k = self.index(address, 2);
        let mut s = 0u16;
        for i in 0..2 {
            let b: u16 = self.get(k+i).into();
            s = (s << 8) | b;
        }
        s
    }

    fn store_wyde(&mut self, address: u64, data: u16) {
        let BYTE_COUNT = 2;
        let k = self.index(address, BYTE_COUNT);
        for i in 0..BYTE_COUNT {
            self.set(k+i, (data >> (8*(BYTE_COUNT-1-i))) as u8);
        }
    }

    fn load_tetra(&self, address: u64) -> u32 {
        let k = self.index(address, 4);
        let mut s = 0u32;
        for i in 0..4 {
            let b: u32 = self.get(k+i).into();
            s = (s << 8) | b;
        }
        s
    }

    fn store_tetra(&mut self, address: u64, data: u32) {
        let BYTE_COUNT = 4;
        let k = self.index(address, BYTE_COUNT);
        for i in 0..BYTE_COUNT {
            self.set(k+i, (data >> (8*(BYTE_COUNT-1-i))) as u8);
        }
    }

    fn load_octa(&self, address: u64) -> u64 {
        let k = self.index(address, 8);
        let mut s = 0u64;
        for i in 0..8 {
            let b: u64 = self.get(k+i).into();
            s = (s << 8) | b;
        }
        s
    }

    fn store_octa(&mut self, address: u64, data: u64) {
        let BYTE_COUNT = 8;
        let k = self.index(address, BYTE_COUNT);
        for i in 0..BYTE_COUNT {
            self.set(k+i, (data >> (8*(BYTE_COUNT-1-i))) as u8);
        }
    }
}

// Instruction code
#[allow(dead_code)]
fn signed_load_byte(memory: &dyn Memory, address: u64) -> u64 {
    let b = memory.load_byte(address);
    let i: i64 = (b as i8).into();
    i as u64
}

#[allow(dead_code)]
fn signed_load_wyde(memory: &dyn Memory, address: u64) -> u64 {
    let w = memory.load_wyde(address);
    let i: i64 = (w as i16).into();
    i as u64
}

#[allow(dead_code)]
fn signed_load_tetra(memory: &dyn Memory, address: u64) -> u64 {
    let t = memory.load_tetra(address);
    let i: i64 = (t as i32).into();
    i as u64
}

#[allow(dead_code)]
fn signed_load_octa(memory: &dyn Memory, address: u64) -> u64 {
    memory.load_octa(address)
}

#[allow(dead_code)]
fn unsigned_load_byte(memory: &dyn Memory, address: u64) -> u64 {
    memory.load_byte(address).into()
}

#[allow(dead_code)]
fn unsigned_load_wyde(memory: &dyn Memory, address: u64) -> u64 {
    memory.load_wyde(address).into()
}

#[allow(dead_code)]
fn unsigned_load_tetra(memory: &dyn Memory, address: u64) -> u64 {
    memory.load_tetra(address).into()
}

#[allow(dead_code)]
fn unsigned_load_octa(memory: &dyn Memory, address: u64) -> u64 {
    memory.load_octa(address)
}

#[allow(dead_code)]
fn load_high_tetra(memory: &dyn Memory, address: u64) -> u64 {
    let u: u64 = memory.load_tetra(address).into();
    u << 32
}

#[allow(dead_code)]
fn load_address(memory: &dyn Memory, address: u64) -> u64 {
    address
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

    fn signed_setup() {
        // $2 = 1000
        // $3 = 2
    }

    #[test]
    fn test_LDB() {
        signed_setup();

        // LDB $1, $2, $3
        // assert $1 = 0x0000_0000_0000_0045
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
        let EXPECT = 0xff_ff_00_00_89_ab_cd_efu64;
        m.store_tetra(1002, 0xff_ff_00_00u32);
        assert_eq!(m.load_octa(1002), EXPECT, "should be 0x{:x?}, but is 0x{:x?}", EXPECT, m.load_octa(1002));
    }

    #[test]
    fn test_memory_store_octa() {
        let mut m = memory_for_tests();
        let EXPECT = 0xff_ff_ff_ff_ff_ff_00_00u64; 
        m.store_octa(1002, 0xff_ff_ff_ff_ff_ff_00_00u64);
        assert_eq!(m.load_octa(1002), EXPECT, "should be 0x{:x?}, but is 0x{:x?}", EXPECT, m.load_octa(1002));
    }

    #[test]
    fn test_signed_load_byte() {
        let m = memory_for_tests();
        assert_eq!(
            signed_load_byte(&m, 1002),
            0x00_00_00_00_00_00_00_45,
            "should lead with zero."
        );
        assert_eq!(
            signed_load_byte(&m, 1004),
            0xff_ff_ff_ff_ff_ff_ff_89,
            "should lead with one."
        );
    }

    #[test]
    fn test_signed_load_wyde() {
        let m = memory_for_tests();
        assert_eq!(
            signed_load_wyde(&m, 1002),
            0x00_00_00_00_00_00_45_67,
            "should lead with zero."
        );
        assert_eq!(
            signed_load_wyde(&m, 1003),
            0x00_00_00_00_00_00_45_67,
            "should be the same with 1002."
        );
        assert_eq!(
            signed_load_wyde(&m, 1004),
            0xff_ff_ff_ff_ff_ff_89_ab,
            "should lead with one."
        );
        assert_eq!(
            signed_load_wyde(&m, 1005),
            0xff_ff_ff_ff_ff_ff_89_ab,
            "should be the same with 1004."
        );
    }

    #[test]
    fn test_signed_load_tetra() {
        let m = memory_for_tests();
        assert_eq!(
            signed_load_tetra(&m, 1001),
            0x00_00_00_00_01_23_45_67
        );
        assert_eq!(
            signed_load_tetra(&m, 1005),
            0xff_ff_ff_ff_89_ab_cd_ef
        );
    }

    #[test]
    fn test_signed_load_octa() {
        let m = memory_for_tests();
        assert_eq!(
            signed_load_octa(&m, 1006),
            0x01_23_45_67_89_ab_cd_ef
        );
    }

    #[test]
    fn test_unsigned_load() {
        let m = memory_for_tests();
        assert_eq!(
            unsigned_load_byte(&m, 1005),
            0x00_00_00_00_00_00_00_ab
        );

        assert_eq!(
            unsigned_load_wyde(&m, 1007),
            0x00_00_00_00_00_00_cd_ef
        );

        assert_eq!(
            unsigned_load_tetra(&m, 1006),
            0x00_00_00_00_89_ab_cd_ef
        );

        assert_eq!(
            unsigned_load_octa(&m, 1004),
            0x01_23_45_67_89_ab_cd_ef
        );
    }

    #[test]
    fn test_load_high_tetra() {
        let m = memory_for_tests();
        assert_eq!(
            load_high_tetra(&m, 1001),
            0x01_23_45_67_00_00_00_00
        );
    }

    #[test]
    fn test_load_address() {
        let m = memory_for_tests();
        assert_eq!(
            load_address(&m, 2345u64),
            2345u64
        );
        assert_eq!(
            load_address(&m, 13579u64),
            13579u64
        );
    }
}

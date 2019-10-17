use std::collections::HashMap;
use crate::memory::Memory;

// Instruction code
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::HashMemory;

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
        return HashMemory::from(m)
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
}

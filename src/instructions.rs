use std::ops::Index;

struct M;

// M[1000]M[1001]...M[1007] = 0x0123_4567_89ab_cdef
impl Index<u64> for M {
    type Output = u8;

    fn index(&self, i: u64) -> &Self::Output {
        match i {
            1000 => &0x01u8,
            1001 => &0x23u8,
            1002 => &0x45u8,
            1003 => &0x67u8,
            1004 => &0x89u8,
            1005 => &0xabu8,
            1006 => &0xcdu8,
            1007 => &0xefu8,
            _ => &0x00u8,
        }
    }
}

impl M {
    fn load_byte(&self, address: u64) -> u8 {
        self[address]
    }

    fn load_wyde(&self, address: u64) -> u16 {
        let k = address - address % 2;
        let mut s = 0u16;
        for i in 0..2 {
            let b: u16 = self[k + i].into();
            s = (s << 8) | b;
        }
        s
    }

    fn load_tetra(&self, address: u64) -> u32 {
        let k = address - address % 4;
        let mut s = 0u32;
        for i in 0..4 {
            let b: u32 = self[k + i].into();
            s = (s << 8) | b;
        }
        s
    }

    fn load_octa(&self, address: u64) -> u64 {
        let k = address - address % 8;
        let mut s = 0u64;
        for i in 0..8 {
            let b: u64 = self[k + i].into();
            s = (s << 8) | b;
        }
        s
    }
}

// Instruction code
fn signed_load_byte(memory: M, address: u64) -> u64 {
    let b = memory.load_byte(address);
    let i: i64 = (b as i8).into();
    i as u64
}

fn signed_load_wyde(memory: M, address: u64) -> u64 {
    let w = memory.load_wyde(address);
    let i: i64 = (w as i16).into();
    i as u64
}

fn signed_load_tetra(memory: M, address: u64) -> u64 {
    let t = memory.load_tetra(address);
    let i: i64 = (t as i32).into();
    i as u64
}

fn signed_load_octa(memory: M, address: u64) -> u64 {
    memory.load_octa(address)
}

fn unsigned_load_byte(memory: M, address: u64) -> u64 {
    memory.load_byte(address).into()
}

fn unsigned_load_wyde(memory: M, address: u64) -> u64 {
    memory.load_wyde(address).into()
}

fn unsigned_load_tetra(memory: M, address: u64) -> u64 {
    memory.load_tetra(address).into()
}

fn unsigned_load_octa(memory: M, address: u64) -> u64 {
    memory.load_octa(address)
}

fn load_high_tetra(memory: M, address: u64) -> u64 {
    let u: u64 = memory.load_tetra(address).into();
    u << 32
}

fn load_address(memory: M, address: u64) -> u64 {
    address
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_memory_access() {
        assert_eq!(M.load_byte(1002), 0x45u8);
        assert_eq!(M.load_wyde(1003), 0x45_67u16);
        assert_eq!(M.load_tetra(1005), 0x89_ab_cd_efu32);
        assert_eq!(M.load_octa(1006), 0x01_23_45_67_89_ab_cd_efu64);
    }

    #[test]
    fn test_multibyte_memory_acess() {
        let n = 1000;

        for i in 0..8 {
            let j = i / 2 * 2;
            assert_eq!(
                M.load_wyde(n + i),
                M.load_wyde(n + j),
                "M.load_wyde({:?}) should equal M.wyde({:?})",
                n + i,
                n + j
            );
        }

        for i in 0..8 {
            let j = i / 4 * 4;
            assert_eq!(M.load_tetra(n + i), M.load_tetra(n + j));
        }

        for i in 0..8 {
            assert_eq!(M.load_octa(n), M.load_octa(n + i));
        }
    }

    #[test]
    fn test_signed_load_byte() {
        assert_eq!(
            signed_load_byte(M, 1002),
            0x00_00_00_00_00_00_00_45,
            "should lead with zero."
        );
        assert_eq!(
            signed_load_byte(M, 1004),
            0xff_ff_ff_ff_ff_ff_ff_89,
            "should lead with one."
        );
    }

    #[test]
    fn test_signed_load_wyde() {
        assert_eq!(
            signed_load_wyde(M, 1002),
            0x00_00_00_00_00_00_45_67,
            "should lead with zero."
        );
        assert_eq!(
            signed_load_wyde(M, 1003),
            0x00_00_00_00_00_00_45_67,
            "should be the same with 1002."
        );
        assert_eq!(
            signed_load_wyde(M, 1004),
            0xff_ff_ff_ff_ff_ff_89_ab,
            "should lead with one."
        );
        assert_eq!(
            signed_load_wyde(M, 1005),
            0xff_ff_ff_ff_ff_ff_89_ab,
            "should be the same with 1004."
        );
    }

    #[test]
    fn test_signed_load_tetra() {
        assert_eq!(
            signed_load_tetra(M, 1001),
            0x00_00_00_00_01_23_45_67
        );
        assert_eq!(
            signed_load_tetra(M, 1005),
            0xff_ff_ff_ff_89_ab_cd_ef
        );
    }

    #[test]
    fn test_signed_load_octa() {
        assert_eq!(
            signed_load_octa(M, 1006),
            0x01_23_45_67_89_ab_cd_ef
        );
    }

    #[test]
    fn test_unsigned_load() {
        assert_eq!(
            unsigned_load_byte(M, 1005),
            0x00_00_00_00_00_00_00_ab
        );

        assert_eq!(
            unsigned_load_wyde(M, 1007),
            0x00_00_00_00_00_00_cd_ef
        );

        assert_eq!(
            unsigned_load_tetra(M, 1006),
            0x00_00_00_00_89_ab_cd_ef
        );

        assert_eq!(
            unsigned_load_octa(M, 1004),
            0x01_23_45_67_89_ab_cd_ef
        );
    }

    #[test]
    fn test_load_high_tetra() {
        assert_eq!(
            load_high_tetra(M, 1001),
            0x01_23_45_67_00_00_00_00
        );
    }

    #[test]
    fn test_load_address() {
        assert_eq!(
            load_address(M, 2345u64),
            2345u64
        );
        assert_eq!(
            load_address(M, 13579u64),
            13579u64
        );
    }
}

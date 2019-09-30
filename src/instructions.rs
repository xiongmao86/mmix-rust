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
// Instruction code
fn signed_load_byte(memory: M, address: u64) -> u64 {
    let byte: u64 = memory[address].into();
    if byte & 0x80 != 0x00 {
        byte | 0xff_ff_ff_00u64 
    } else {
        byte | 0x00_00_00_00u64
    }
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
    fn test_signed_load_byte() {
        assert_eq!(signed_load_byte(M, 1002), 0x00_00_00_45);
        assert_eq!(signed_load_byte(M, 1004), 0xff_ff_ff_89);
    }
}

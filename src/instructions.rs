// Instruction code

// Instruction test

#[cfg(test)]
mod tests {
    struct M;

    // M[1000]M[1001]...M[1007] = 0x0123_4567_89ab_cdef
    impl std::ops::Index<u64> for M {
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

    fn signed_setup() {
        // $2 = 1000
        // $3 = 2
    }

    #[test]
    fn test_signed_load() {
        signed_setup();

        // LDB $1, $2, $3
        // assert $1 = 0x0000_0000_0000_0045
        assert_eq!(M[1002], 0x45);
    }
}

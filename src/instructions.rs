// Instruction code

// Instruction test

fn signed_setup() {
    // M[1000]M[1001]...M[1007] = 0x0123_4567_89ab_cdef
    // $2 = 1000
    // $3 = 2
}

#[test]
fn test_signed_load() {
    signed_setup();

    // LDB $1, $2, $3
    // assert $1 = 0x0000_0000_0000_0045
}

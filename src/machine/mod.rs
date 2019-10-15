mod memory;
use memory::Memory;

#[allow(dead_code)]
struct Machine<'a> {
    memory: &'a dyn Memory,
    general_register: [u64; 256],
    special_register: [u64; 32]
}

#[cfg(test)]
mod tests {
    fn signed_setup() {
        // $2 = 1000
        // $3 = 2
    }

    //LDB
    #[test]
    fn test_ldb() {
        signed_setup();

        // LDB $1, $2, $3
        // assert $1 = 0x0000_0000_0000_0045
        assert!(true);
    }
}

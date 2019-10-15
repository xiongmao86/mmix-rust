mod memory;
use memory::Memory;

#[allow(dead_code)]
struct Machine<T: Memory> {
    memory: T,
    general_register: [u64; 256],
    special_register: [u64; 32]
}

impl<T> Machine<T> where T: Memory {
    fn new(memory: T) -> Machine<T> {
        Machine {
            memory,
            general_register: [0; 256],
            special_register: [0; 32],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::memory::HashMemory;
    use super::*;

    fn machine_for_tests() -> Machine<HashMemory> {
        // $2 = 1000
        // $3 = 2
        let mut hm = HashMemory::new();
        hm.store_octa(1000, 0x01_23_45_67_89_ab_cd_efu64);
        let mut m = Machine::new(hm);
        m.general_register[1] = 1000;
        m.general_register[2] = 2;
        m
    }

    //LDB
    #[test]
    fn test_ldb() {
        let m = machine_for_tests();

        // LDB $1, $2, $3
        // assert $1 = 0x0000_0000_0000_0045
        assert!(true);
    }
}

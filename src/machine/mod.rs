mod memory;
use memory::{ Memory, HashMemory };

#[allow(dead_code)]
struct Machine<T: Memory> {
    memory: T,
    general_registers: [u64; 256],
    special_registers: [u64; 32],
    instructions: [InstFn<T>; 256],
}

type InstFn<T> = fn(&mut Machine<T>, u32);

impl<T> Machine<T> where T: Memory {
    fn new(memory: T) -> Machine<T> {
        let mut insts = [ Self::dummy_inst as InstFn<T>; 256];
        insts[0x80] = Self::ldb as InstFn<T>;
        
        Machine {
            memory,
            general_registers: [0; 256],
            special_registers: [0; 32],
            instructions: insts,
        }
    }

    fn execute(&mut self, inst: u32) {
        let opcode = ((inst >> 24 ) as u8) as usize;
        self.instructions[opcode](self, inst);
    }

    fn dummy_inst(&mut self, _ops: u32) {}

    fn ldb(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let address = self.general_registers[y] + self.general_registers[z];

        let b = self.memory.load_byte(address);
        let i: i64 = (b as i8).into();
        self.general_registers[x] = i as u64;
    }
}

fn one_operand(inst: u32) -> usize {
    (inst & 0x00_ff_ff_ffu32) as usize
}

fn two_operands(inst: u32) -> (usize, usize) {
    let o1 = ((inst >> 16) as u8) as usize;
    let o2 = (inst & 0x00_00_ff_ff) as usize;
    (o1, o2)
}

fn three_operands(inst: u32) -> (usize, usize, usize) {
    let o1 = ((inst >> 16) as u8) as usize;
    let o2 = ((inst >> 8) as u8) as usize;
    let o3 = (inst as u8) as usize;
    (o1, o2, o3)
}

#[cfg(test)]
mod tests {
    use super::memory::HashMemory;
    use super::*;

    fn machine_for_tests(reg3: u64) -> Machine<HashMemory> {
        // $2 = 1000
        // $3 = reg3
        let mut hm = HashMemory::new();
        hm.store_octa(1000, 0x01_23_45_67_89_ab_cd_efu64);
        let mut m = Machine::new(hm);
        m.general_registers[2] = 1000;
        m.general_registers[3] = reg3;
        m
    }

    macro_rules! test_ld {
        ($inst: expr, $reg3:literal, $expect:literal) => {
            let mut m = machine_for_tests($reg3);
            m.execute($inst);
            assert_eq!(m.general_registers[1], $expect);
        }
    }

    //LDB
    #[test]
    fn test_ldb() {
        let ldb_inst = 0x80010203u32;
        test_ld!(ldb_inst, 2u64, 0x0000_0000_0000_0045u64);
        test_ld!(ldb_inst, 4u64, 0xffff_ffff_ffff_ff89u64);
    }
}

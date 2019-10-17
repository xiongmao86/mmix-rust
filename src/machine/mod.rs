mod memory;
use memory::{ Memory, HashMemory };

#[allow(dead_code)]
struct Machine<T: Memory> {
    memory: T,
    gen_regs: [u64; 256],
    special_registers: [u64; 32],
    instructions: [InstFn<T>; 256],
}

type InstFn<T> = fn(&mut Machine<T>, u32);

macro_rules! load_method {
    ($name:ident, load_octa, u64) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);
            let (x, y, z): (usize, usize, usize) = (x.into(), y.into(), z.into());

            let address = self.gen_regs[y] + self.gen_regs[z];

            let data = self.memory.load_octa(address);
            self.gen_regs[x] = data;
        }
    };
    ($name:ident, $method:ident, $ty:ty) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);
            let (x, y, z): (usize, usize, usize) = (x.into(), y.into(), z.into());

            let address = self.gen_regs[y] + self.gen_regs[z];

            let data = self.memory.$method(address);
            let i: i64 = (data as $ty).into();
            self.gen_regs[x] = i as u64;
        }
    }
}

macro_rules! register_inst {
    ($array:ident, $opcode:literal, $inst:ident) => {
        $array[$opcode] = Self::$inst as InstFn<T>;
    }
}

impl<T> Machine<T> where T: Memory {
    fn new(memory: T) -> Machine<T> {
        let mut insts = [ Self::dummy_inst as InstFn<T>; 256];
        register_inst!(insts, 0x80, ldb);
        register_inst!(insts, 0x84, ldw);
        register_inst!(insts, 0x88, ldt);
        register_inst!(insts, 0x8c, ldo);
        
        Machine {
            memory,
            gen_regs: [0; 256],
            special_registers: [0; 32],
            instructions: insts,
        }
    }

    fn execute(&mut self, inst: u32) {
        let opcode = ((inst >> 24 ) as u8) as usize;
        self.instructions[opcode](self, inst);
    }

    fn dummy_inst(&mut self, _ops: u32) {}

    load_method!(ldb, load_byte, i8);
    load_method!(ldw, load_wyde, i16);
    load_method!(ldt, load_tetra, i32);
    load_method!(ldo, load_octa, i64);
}

fn one_operand(inst: u32) -> usize {
    (inst & 0x00_ff_ff_ffu32) as usize
}

fn two_operands(inst: u32) -> (usize, usize) {
    let o1 = ((inst >> 16) as u8) as usize;
    let o2 = (inst & 0x00_00_ff_ff) as usize;
    (o1, o2)
}

fn three_operands(inst: u32) -> (u8, u8, u8) {
    let o1 = (inst >> 16) as u8;
    let o2 = (inst >> 8) as u8;
    let o3 = inst as u8;
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
        m.gen_regs[2] = 1000;
        m.gen_regs[3] = reg3;
        m
    }

    macro_rules! test_ld {
        ($inst: expr, $reg3:literal, $expect:literal) => {
            let mut m = machine_for_tests($reg3);
            m.execute($inst);
            assert_eq!(
                m.gen_regs[1],
                $expect,
                "Expect 0x{:x?}, found 0x{:x?}",
                $expect,
                m.gen_regs[1]
            );  
        }
    }

    #[test]
    fn test_ldb() {
        let ldb_inst = 0x80010203u32;
        test_ld!(ldb_inst, 2u64, 0x0000_0000_0000_0045u64);
        test_ld!(ldb_inst, 4u64, 0xffff_ffff_ffff_ff89u64);
    }

    #[test]
    fn test_ldw() {
        let ldw_inst = 0x84010203u32;
        test_ld!(ldw_inst, 2u64, 0x0000_0000_0000_4567u64);
        test_ld!(ldw_inst, 3u64, 0x0000_0000_0000_4567u64);
        test_ld!(ldw_inst, 4u64, 0xffff_ffff_ffff_89abu64);
        test_ld!(ldw_inst, 5u64, 0xffff_ffff_ffff_89abu64);
    }

    #[test]
    fn test_ldt() {
        let ldt_inst = 0x88010203u32;
        test_ld!(ldt_inst, 1u64, 0x0000_0000_0123_4567u64);
        test_ld!(ldt_inst, 5u64, 0xffff_ffff_89ab_cdefu64);
    }

    #[test]
    fn test_ldo() {
        let ldo_inst = 0x8c010203u32;
        test_ld!(ldo_inst, 6u64, 0x0123_4567_89ab_cdefu64);
    }
}

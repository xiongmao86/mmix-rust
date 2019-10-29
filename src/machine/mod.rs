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

macro_rules! alias_inst {
    ($alias:ident, $origin:ident) => {
        fn $alias(&mut self, inst: u32) {
            self.$origin(inst);
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
        register_inst!(insts, 0x82, ldbu);
        register_inst!(insts, 0x86, ldwu);
        register_inst!(insts, 0x8a, ldtu);
        register_inst!(insts, 0x8e, ldou);
        register_inst!(insts, 0x92, ldht);

        register_inst!(insts, 0xa0, stb);
        register_inst!(insts, 0xa4, stw);
        register_inst!(insts, 0xa8, stt);
        register_inst!(insts, 0xac, sto);
        register_inst!(insts, 0xa2, stbu);
        register_inst!(insts, 0xa6, stwu);
        register_inst!(insts, 0xaa, sttu);
        register_inst!(insts, 0xae, stou);
        register_inst!(insts, 0xb2, stht);
        register_inst!(insts, 0xb4, stco);

        register_inst!(insts, 0x20, add);

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
}

// load instructions
macro_rules! load_method {
    ($name:ident, load_octa, u64) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_usize(inst);

            let address = self.gen_regs[y] + self.gen_regs[z];

            let data = self.memory.load_octa(address);
            self.gen_regs[x] = data;
        }
    };
    ($name:ident, $method:ident, $ty:ty) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_usize(inst);

            let address = self.gen_regs[y] + self.gen_regs[z];

            let data = self.memory.$method(address);
            let i: i64 = (data as $ty).into();
            self.gen_regs[x] = i as u64;
        }
    }
}

macro_rules! unsigned_load_method {
    ($name:ident, $method:ident) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_usize(inst);

            let address = self.gen_regs[y] + self.gen_regs[z];
            self.gen_regs[x] = self.memory.$method(address).into();
        }
    }
}

impl<T> Machine<T> where T: Memory {
    load_method!(ldb, load_byte, i8);
    load_method!(ldw, load_wyde, i16);
    load_method!(ldt, load_tetra, i32);
    load_method!(ldo, load_octa, i64);

    fn ldht(&mut self, inst: u32) {
        let (x, y, z) = three_usize(inst);
        let address = self.gen_regs[y] + self.gen_regs[z];
        let u: u64 = self.memory.load_tetra(address).into();
        self.gen_regs[x] = u << 32;
    }

//    fn lda(&mut self, inst: u32) {
//        let (x, y, z) = three_usize(inst);
//        let address = self.gen_regs[y] + self.gen_regs[z];
//        self.gen_regs[x] = address;
//    }

    unsigned_load_method!(ldbu, load_byte);
    unsigned_load_method!(ldwu, load_wyde);
    unsigned_load_method!(ldtu, load_tetra);
    unsigned_load_method!(ldou, load_octa);
}

// store instructions
macro_rules! store_method {
    ($name:ident, $ty:ty, $method:ident) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_usize(inst);
            let address = self.gen_regs[y] + self.gen_regs[z];
            let data = self.gen_regs[x] as $ty;
            self.memory.$method(address, data);
        }
    }
}

impl<T> Machine<T> where T: Memory {
    store_method!(stb, u8, store_byte);
    store_method!(stw, u16, store_wyde);
    store_method!(stt, u32, store_tetra);
    store_method!(sto, u64, store_octa);

    alias_inst!(stbu, stb);
    alias_inst!(stwu, stw);
    alias_inst!(sttu, stt);
    alias_inst!(stou, sto);

    fn stht(&mut self, inst: u32) {
        let (x, y, z) = three_usize(inst);
        let address = self.gen_regs[y] + self.gen_regs[z];
        let u = (self.gen_regs[x] >> 32) as u32;
        self.memory.store_tetra(address, u);
    }

    fn stco(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let x: u64 = x.into();
        let (y, z): (usize, usize) = (y.into(), z.into());
        let address = self.gen_regs[y] + self.gen_regs[z];
        self.memory.store_octa(address, x);
    }
}

impl<T> Machine<T> where T: Memory {
    fn add(&mut self, inst: u32) {
        let (x, y, z) = three_usize(inst);
        let o2 = self.gen_regs[y] as i64;
        let o3 = self.gen_regs[z] as i64;
        let r = o2 + o3;
        self.gen_regs[x] = r as u64;
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

fn three_operands(inst: u32) -> (u8, u8, u8) {
    let o1 = (inst >> 16) as u8;
    let o2 = (inst >> 8) as u8;
    let o3 = inst as u8;
    (o1, o2, o3)
}

fn three_usize(inst: u32) -> (usize, usize, usize) {
    let (x, y, z) = three_operands(inst);
    (x.into(), y.into(), z.into())
}

#[cfg(test)]
mod tests {
    use super::memory::HashMemory;
    use super::*;

    fn machine_for_memory_tests(reg3: u64) -> Machine<HashMemory> {
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
            let mut m = machine_for_memory_tests($reg3);
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

    #[test]
    fn test_ldbu() {
        let ldbu_inst = 0x82010203u32;
        test_ld!(ldbu_inst, 5u64, 0x0000_0000_0000_00abu64);
    }

    #[test]
    fn test_ldwu() {
        let ldwu_inst = 0x86010203u32;
        test_ld!(ldwu_inst, 7u64, 0x0000_0000_0000_cdefu64);
    }

    #[test]
    fn test_ldtu() {
        let ldtu_inst = 0x8a010203u32;
        test_ld!(ldtu_inst, 6u64, 0x0000_0000_89_ab_cd_efu64);
    }

    #[test]
    fn test_ldou() {
        let ldou_inst = 0x8e010203u32;
        test_ld!(ldou_inst, 4u64, 0x0123_4567_89ab_cdefu64);
    }
    #[test]
    fn test_ldht() {
        let ldht_inst = 0x92010203u32;
        test_ld!(ldht_inst, 1u64, 0x0123_4567_0000_0000u64);
    }

//    #[test]
//    fn test_lda() {
//        let lda_inst = 0x??010203u32;
//        let mut m = machine_for_test(3u64);
//        m.execute(lda_inst);
//        assert_eq!(m.gen_regs[1], 1003);
//    }

    macro_rules! test_st {
        ($inst:expr, $reg3:expr, $expect:expr) => {
            let mut m = machine_for_memory_tests($reg3);
            m.gen_regs[1] = 0xffff_ffff_ffff_0000u64;
            m.execute($inst);
            let address = m.gen_regs[2] + m.gen_regs[3];
            let data = m.memory.load_octa(address);
            assert_eq!(
                data,
                $expect,
                "Expect 0x{:x?}, found 0x{:x?}.",
                $expect,
                data
            );
        }
    }

    #[test]
    fn test_stb() {
        let stb_inst = 0xa0010203u32;
        test_st!(stb_inst, 2u64, 0x0123_0067_89ab_cdefu64);
    }

    #[test]
    fn test_stw() {
        let stw_inst = 0xa4010203u32;
        test_st!(stw_inst, 2u64, 0x0123_0000_89ab_cdefu64);
    }

    #[test]
    fn test_stt() {
        let stt_inst = 0xa8010203u32;
        test_st!(stt_inst, 2u64, 0xffff_0000_89ab_cdefu64);
    }

    #[test]
    fn test_sto() {
        let sto_inst = 0xac010203u32;
        test_st!(sto_inst, 2u64, 0xffff_ffff_ffff_0000u64);
    }

    #[test]
    fn test_stht() {
        let stht_inst = 0xb2010203u32;
        test_st!(stht_inst, 2u64, 0xffff_ffff_89ab_cdefu64);
    }

    #[test]
    fn test_stco() {
        let stco_inst = 0xb4a00203u32;
        test_st!(stco_inst, 2u64, 0x0000_0000_0000_00a0u64);
    }

    fn machine_for_arithmetic_test(reg2: u64, reg3: u64) -> Machine<HashMemory> {
        let hm = HashMemory::new();
        let mut m = Machine::new(hm);
        
        m.gen_regs[2] = reg2;
        m.gen_regs[3] = reg3;

        m
    }

    fn test_signed_arith(inst: u32, expect: i64, op1: i64, op2: i64) {
        let mut m = machine_for_arithmetic_test(op1 as u64, op2 as u64);
        m.execute(inst);
        let reg1 = m.gen_regs[1] as i64;
        assert_eq!(reg1, expect, "expect {:?}, found {:?}", expect, reg1);
    }

    #[test]
    fn test_add() {
        let add_inst = 0x20010203u32;
        
        test_signed_arith(add_inst, 7i64, 3i64, 4i64);
        test_signed_arith(add_inst, -1i64, 3i64, -4i64);
    }
}

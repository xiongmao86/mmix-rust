mod memory;
use memory::{ Memory, HashMemory };
use std::ops::{ Add, Sub, Mul };

#[allow(dead_code)]
struct Machine<T: Memory> {
    memory: T,
    gen_regs: [Register; 256],
    spcl_regs: [Register; 32],
    instructions: [InstFn<T>; 256],
}

#[derive(Clone, Copy)]
struct Register(u64);

impl Register {
    fn get(&self) -> u64 {
        self.0
    }

    fn set(&mut self, data: u64) {
        self.0 = data;
    }
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
enum SpecialRegister {
    rA, rB, rC, rD, rE, rF, rG, rH, rI, rJ, rK, rL, rM, rN, rO, rP, rQ, rR, rS, rT, rU, rV, rW, rX, rY, rZ,
    rBB, rTT, rWW, rXX, rYY, rZZ
}

fn to_index(sr: SpecialRegister) -> usize {
    match sr {
        rR => 6,
        other => panic!("{:?} index not added.", other)
    }
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
        register_inst!(insts, 0x24, sub);
        register_inst!(insts, 0x18, mul);
        register_inst!(insts, 0x1c, div);

        register_inst!(insts, 0x22, addu);
        register_inst!(insts, 0x26, subu);
        register_inst!(insts, 0x1a, mulu);
        register_inst!(insts, 0x1e, divu);
        register_inst!(insts, 0x28, two_addu);
        register_inst!(insts, 0x2a, four_addu);
        register_inst!(insts, 0x2c, eight_addu);
        register_inst!(insts, 0x2e, sixteen_addu);
        register_inst!(insts, 0x34, neg);
        register_inst!(insts, 0x36, negu);
 
        Machine {
            memory,
            gen_regs: [Register(0u64); 256],
            spcl_regs: [Register(0u64); 32],
            instructions: insts,
        }
    }

    fn execute(&mut self, inst: u32) {
        let opcode = ((inst >> 24 ) as u8) as usize;
        self.instructions[opcode](self, inst);
    }

    fn greg(&mut self, index: u8) -> &mut Register {
        &mut self.gen_regs[index as usize]
    }

    fn spreg(&mut self, sr_name: SpecialRegister) -> &mut Register {
        &mut self.spcl_regs[to_index(sr_name)]
    }

    fn dummy_inst(&mut self, ops: u32) {
        let opcode = ops >> 24;
        panic!("Instruction of 0x{:x?} is not added yet.", opcode);
    }
}

// load instructions
macro_rules! load_method {
    ($name:ident, load_octa, u64) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);

            let address = self.greg(y).get() + self.greg(z).get();

            let data = self.memory.load_octa(address);
            self.greg(x).set(data);
        }
    };
    ($name:ident, $method:ident, $ty:ty) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);

            let address = self.greg(y).get() + self.greg(z).get();

            let data = self.memory.$method(address);
            let i: i64 = (data as $ty).into();
            self.greg(x).set(i as u64);
        }
    }
}

macro_rules! unsigned_load_method {
    ($name:ident, $method:ident) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);

            let address = self.greg(y).get() + self.greg(z).get();
            let data = self.memory.$method(address).into();
            self.greg(x).set(data);
        }
    }
}

impl<T> Machine<T> where T: Memory {
    load_method!(ldb, load_byte, i8);
    load_method!(ldw, load_wyde, i16);
    load_method!(ldt, load_tetra, i32);
    load_method!(ldo, load_octa, i64);

    fn ldht(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let address = self.greg(y).get() + self.greg(z).get();
        let u: u64 = self.memory.load_tetra(address).into();
        self.greg(x).set(u << 32);
    }

    unsigned_load_method!(ldbu, load_byte);
    unsigned_load_method!(ldwu, load_wyde);
    unsigned_load_method!(ldtu, load_tetra);
    unsigned_load_method!(ldou, load_octa);
}

// store instructions
macro_rules! store_method {
    ($name:ident, $ty:ty, $method:ident) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);
            let address = self.greg(y).get() + self.greg(z).get();
            let data = self.greg(x).get() as $ty;
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
        let (x, y, z) = three_operands(inst);
        let address = self.greg(y).get() + self.greg(z).get();
        let u = (self.greg(x).get() >> 32) as u32;
        self.memory.store_tetra(address, u);
    }

    fn stco(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let x: u64 = x.into();
        let address = self.greg(y).get() + self.greg(z).get();
        self.memory.store_octa(address, x);
    }
}

macro_rules! signed_arith_inst {
    ($name:ident, $op:ident) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);
            let o2 = self.greg(y).get() as i64;
            let o3 = self.greg(z).get() as i64;
            let r = o2.$op(o3);
            self.greg(x).set(r as u64);
        }
    }
}

impl<T> Machine<T> where T: Memory {
    signed_arith_inst!(add, add);
    signed_arith_inst!(sub, sub);
    signed_arith_inst!(mul, mul);

    fn div(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let o2 = self.greg(y).get() as i64;
        let o3 = self.greg(z).get() as i64;
        if o3 == 0 {
            self.greg(x).set(o3 as u64);
            self.spreg(SpecialRegister::rR).set(o2 as u64);
        } else if (o3 > 0 && o2 >=0) ||
            (o3 < 0 && o2 < 0 ) {
            let q = o2 / o3;
            self.greg(x).set(q as u64);
            let m  = o2 - o3 * q;
            self.spreg(SpecialRegister::rR).set(m as u64);
        } else {
            let q = o2 / o3 - 1;
            self.greg(x).set(q as u64);
            let m = o2 - o3 * q;
            self.spreg(SpecialRegister::rR).set(m as u64);
        }
    }
}

macro_rules! unsigned_arith_inst {
    ($name:ident, $op:ident) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);
            let o2 = self.greg(y).get();
            let o3 = self.greg(z).get();
            let r = o2.$op(o3);
            self.greg(x).set(r);
        }
    }
}

macro_rules! naddu_inst {
    ($name:ident, $n:literal) => {
        fn $name(&mut self, inst: u32) {
            let (x, y, z) = three_operands(inst);
            let o2 = self.greg(y).get();
            let o3 = self.greg(z).get();
            let r = o2 * $n + o3;
            self.greg(x).set(r);
        }
    }
}

impl<T> Machine<T> where T: Memory {
    unsigned_arith_inst!(addu, add);
    unsigned_arith_inst!(subu, sub);

    fn mulu(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let o2 = self.greg(y).get() as u128;
        let o3 = self.greg(z).get() as u128;
        let r = o2 * o3;
        let r1 = r as u64;
        let r_d = (r >> 64) as u64;
        self.greg(x).set(r1);
        self.spreg(SpecialRegister::rD).set(r_d);
    }

    // My intepretation of mmix doc: if higher 64-bit of divident rD is bigger
    // than divisor, the operation may produce a 16 byte quotient and an 8
    // byte remainder. In this case the machine will estimate and quotient
    // as rD, and the remainder as the lower 64-bit of the divident.
    fn divu(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let op3 = self.greg(z).get();
        let rd = self.spreg(SpecialRegister::rD).get();
        if op3 > rd {
            let h: u128 = rd.into();
            let l: u128 = self.greg(y).get().into();
            let divident = (h << 64) | l;
            let divisor: u128 = op3.into();
            let quotient = divident / divisor;
            let module = divident % divisor;
            self.greg(x).set(quotient as u64);
            self.spreg(SpecialRegister::rR).set(module as u64);
        } else {
            self.greg(x).set(rd);
            let rr = self.greg(y).get();
            self.spreg(SpecialRegister::rR).set(rr);
        }
    }

    naddu_inst!(two_addu, 2);
    naddu_inst!(four_addu, 4);
    naddu_inst!(eight_addu, 8);
    naddu_inst!(sixteen_addu, 16);

    fn neg(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let op3 = self.greg(z).get() as i64;
        let op2 = y as i64;
        let r = op2 - op3;
        self.greg(x).set(r as u64);
    }

    fn negu(&mut self, inst: u32) {
        let (x, y, z) = three_operands(inst);
        let op3 = self.greg(z).get();
        let op2: u64 = y.into();
        let r = op2 - op3;
        self.greg(x).set(r);
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

#[cfg(test)]
mod tests {
    use super::memory::HashMemory;
    use super::*;

    fn machine_for_memory_tests(reg3: u64) -> Machine<HashMemory> {
        let mut hm = HashMemory::new();
        hm.store_octa(1000, 0x01_23_45_67_89_ab_cd_efu64);
        let mut m = Machine::new(hm);
        m.greg(2).set(1000);
        m.greg(3).set(reg3);
        m
    }

    macro_rules! test_ld {
        ($inst: expr, $reg3:literal, $expect:literal) => {
            let mut m = machine_for_memory_tests($reg3);
            m.execute($inst);
            assert_eq!(
                m.greg(1).get(),
                $expect,
                "Expect 0x{:x?}, found 0x{:x?}",
                $expect,
                m.greg(1).get()
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

    macro_rules! test_st {
        ($inst:expr, $reg3:expr, $expect:expr) => {
            let mut m = machine_for_memory_tests($reg3);
            m.greg(1).set(0xffff_ffff_ffff_0000u64);
            m.execute($inst);
            let address = m.greg(2).get() + m.greg(3).get();
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

    fn machine_with_two_reg(reg2: u64, reg3: u64) -> Machine<HashMemory> {
        let hm = HashMemory::new();
        let mut m = Machine::new(hm);
        
        m.greg(2).set(reg2);
        m.greg(3).set(reg3);

        m
    }

    fn machine_with_one_reg(reg3: u64) -> Machine<HashMemory> {
        // reg2 is not important, so set to 0.
        machine_with_two_reg(0, reg3)
    }

    fn test_signed_arith(inst: u32, expect: i64, op1: i64, op2: i64) {
        let mut m = machine_with_two_reg(op1 as u64, op2 as u64);
        m.execute(inst);
        let reg1 = m.greg(1).get() as i64;
        assert_eq!(reg1, expect, "expect {:?}, found {:?}", expect, reg1);
    }

    #[test]
    fn test_add() {
        let add_inst = 0x20010203u32;
        
        test_signed_arith(add_inst, 7i64, 3i64, 4i64);
        test_signed_arith(add_inst, -1i64, 3i64, -4i64);
    }

    #[test]
    fn test_sub() {
        let sub_inst = 0x24010203u32;
        test_signed_arith(sub_inst, -1i64, 3i64, 4i64);
        test_signed_arith(sub_inst, 1i64, 4i64, 3i64);
    }

    #[test]
    fn test_mul() {
        let mul_inst = 0x18010203u32;
        test_signed_arith(mul_inst, 30i64, 5i64, 6i64);
        test_signed_arith(mul_inst, -45i64, 9i64, -5i64);
    }

    fn test_signed_div(inst: u32, expect_quotient: i64, expect_remainder: i64, op1: i64, op2: i64) {
        let mut m = machine_with_two_reg(op1 as u64, op2 as u64);
        m.execute(inst);
        let reg1 = m.greg(1).get() as i64;
        assert_eq!(reg1, expect_quotient, "expect quotient: {:?}, found {:?}", expect_quotient, reg1);
        let reg_r = m.spreg(SpecialRegister::rR).get() as i64;
        assert_eq!(reg_r, expect_remainder, "expect remainder: {:?}, found {:?}", expect_remainder, reg_r);
    }

    #[test]
    fn test_div() {
        let div_inst = 0x1c010203u32;
        test_signed_div(div_inst, 0i64, 3i64, 3i64, 0i64);
        test_signed_div(div_inst, 1i64, 2i64, 6i64, 4i64);
        test_signed_div(div_inst, -2i64, -2i64, 6i64, -4i64);
    }

    fn test_unsigned_add_substract(inst: u32, expect: u64, op1: u64, op2: u64) {
        let mut m = machine_with_two_reg(op1, op2);
        m.execute(inst);
        let reg1 = m.greg(1).get();
        assert_eq!(reg1, expect, "expect {:?}, found {:?}", expect, reg1);
    }

    #[test]
    fn test_addu() {
        let addu_inst = 0x22010203u32;
        test_unsigned_add_substract(addu_inst, 14u64, 8u64, 6u64);
    }

    #[test]
    fn test_subu() {
        let subu_inst = 0x26010203u32;
        test_unsigned_add_substract(subu_inst, 3u64, 14u64, 11u64);
    }

    fn test_unsigned_multiply(inst: u32, expect: u128, op1: u64, op2: u64) {
        let mut m = machine_with_two_reg(op1, op2);
        m.execute(inst);
        let reg1 = m.greg(1).get() as u128;
        let r_d = m.spreg(SpecialRegister::rD).get() as u128;
        let result = (r_d << 64) | reg1;
        assert_eq!(result, expect, "expect {:?}, found {:?}", expect, result);
    }

    #[test]
    fn test_mulu() {
        let mulu_inst = 0x1a010203u32;

        test_unsigned_multiply(mulu_inst, 15u128, 3u64, 5u64);
        test_unsigned_multiply(mulu_inst, 551240594518494412800u128, 30u64, 18374686483949813760u64);
    }

    fn test_unsigned_divide(inst: u32, expect_r1: u64, expect_rr: u64, rd: u64, op1: u64, op2: u64) {
        let mut m = machine_with_two_reg(op1, op2);
        m.spreg(SpecialRegister::rD).set(rd);
        m.execute(inst);
        let reg1 = m.greg(1).get();
        let r_r = m.spreg(SpecialRegister::rR).get();
        assert_eq!(expect_r1, reg1, "expect quotient {:?}, found {:?}", expect_r1, reg1);
        assert_eq!(expect_rr, r_r, "expect remainder {:?}, found {:?}", expect_rr, r_r);
    }

    #[test]
    fn test_divu() {
        let divu_inst = 0x1e010203u32;

        test_unsigned_divide(divu_inst, 9223372036854775809u64, 2u64, 2u64, 6u64, 4u64);
        test_unsigned_divide(divu_inst, 4u64, 1u64, 4u64, 1u64, 2u64);
    }

    fn test_naddu(inst: u32, expect: u64, op1: u64, op2: u64) {
        let mut m = machine_with_two_reg(op1, op2);
        m.execute(inst);
        let reg1 = m.greg(1).get();
        assert_eq!(expect, reg1, "expect {:?}, found {:?}", expect, reg1);
    }

    #[test]
    fn test_2addu() {
        let two_addu_inst = 0x28010203u32;
        test_naddu(two_addu_inst, 18u64, 4u64, 10u64);
    }

    #[test]
    fn test_4addu() {
        let four_addu_inst = 0x2a010203u32;
        test_naddu(four_addu_inst, 18u64, 2u64, 10u64);
    }

    #[test]
    fn test_8addu() {
        let eight_addu_inst = 0x2c010203u32;
        test_naddu(eight_addu_inst, 26u64, 2u64, 10u64);
    }

    #[test]
    fn test_16addu() {
        let sixteen_addu_inst = 0x2e010203u32;
        test_naddu(sixteen_addu_inst, 26u64, 1u64, 10u64);
    }

    fn test_signed_negate(inst: u32, expect: i64, op3: i64) {
        let mut m = machine_with_one_reg(op3 as u64);
        m.execute(inst);
        let reg1: i64 = m.greg(1).get() as i64;
        assert_eq!(expect, reg1, "expect {:?}, found {:?}", expect, reg1);
    }

    #[test]
    fn test_neg() {
        let neg_inst = 0x34010003u32;
        test_signed_negate(neg_inst, -22i64, 22i64);

        let neg_inst2 = 0x34010503u32;
        test_signed_negate(neg_inst2, -17i64 , 22i64);
    }

    fn test_unsigned_negate(inst: u32, expect: u64, op3: u64) {
        let mut m = machine_with_one_reg(op3);
        m.execute(inst);
        let reg1 = m.greg(1).get();
        assert_eq!(expect, reg1, "expect {:?}, found {:?}", expect, reg1);
    }

    #[test]
    fn test_negu() {
        let negu_inst = 0x3601ff03u32;
        test_unsigned_negate(negu_inst, 2u64, 253u64);
    }
}

mod memory;
use memory::{ Memory, HashMemory };

#[allow(dead_code)]
struct Machine<T: Memory> {
    memory: T,
    general_registers: [u64; 256],
    special_registers: [u64; 32],
    instructions: [InstFn; 256],
}

impl<T> Machine<T> where T: Memory {
    fn new(memory: T) -> Machine<T> {
        let insts = [ dummy_inst as InstFn; 256];
        
        Machine {
            memory,
            general_registers: [0; 256],
            special_registers: [0; 32],
            instructions: insts,
        }
    }

    fn execute(&mut self, inst: u32) {
        let opcode = (inst >> 24 ) as u8;
        match opcode {
            0x80 => {
                let x = (inst >> 16) as u8;
                let y = (inst >> 8) as u8;
                let z = inst as u8;

                let x: usize = x.into();
                let y: usize = y.into();
                let z: usize = z.into();
                self.general_registers[x] = signed_load_byte(&self.memory, self.general_registers[y] + self.general_registers[z]);
            },
            _ => {}
        }
    }
}

type InstFn = fn(&mut Machine<HashMemory>, u32);

fn dummy_inst(_m: &mut Machine<HashMemory>, _ops: u32) {}

#[allow(dead_code)]
fn signed_load_byte(memory: &dyn Memory, address: u64) -> u64 {
    let b = memory.load_byte(address);
    let i: i64 = (b as i8).into();
    i as u64
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
        m.general_registers[2] = 1000;
        m.general_registers[3] = 2;
        m
    }

    //LDB
    #[test]
    fn test_ldb() {
        let mut m = machine_for_tests();
        let ldb_inst = 0x80010203u32;

        m.execute(ldb_inst);
        // assert $1 = 0x0000_0000_0000_0045
        assert_eq!(m.general_registers[1], 0x0000_0000_0000_0045u64);
    }
}

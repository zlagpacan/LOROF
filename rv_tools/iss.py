import sys
import argparse

def get_word_list(mem):
    word_dict = dict()
    for byte_addr, byte_value in mem.items():
        try:
            word_dict[byte_addr >> 2][byte_addr & 0x3] = byte_value
        except KeyError:
            word_dict[byte_addr >> 2] = [0x0, 0x0, 0x0, 0x0]
            word_dict[byte_addr >> 2][byte_addr & 0x3] = byte_value

    word_list = []
    for word_addr, word_value in word_dict.items():
        if any(word_value):
            word_list.append((word_addr, word_value))

    return sorted(word_list, key=lambda x: x[0])

def bits(num, upper_index, lower_index):
    return (num >> lower_index) & (2**(upper_index - lower_index + 1) - 1)

def signed32(num, size):
    if num >> (size - 1) & 0b1:
        return bits((0xFFFFFFFF << size) + num, 31, 0)
    else:
        return num

class ArchState:
    def __init__(self, start_pc, mem):
        self.pc = start_pc
        self.arf = [0x0 for x in range(32)]
        self.instret = 0
        self.mem = mem
        self.log = ""

    def exec_instr(self):

        instr = 0
        for i in range(4):
            if self.pc+i in self.mem:
                instr += self.mem[self.pc+i] << 8*i
            else:
                break

        opcode2 = bits(instr, 1, 0)

        # uncompressed
        if opcode2 == 0b11:
            self.log += f"MEM[0x{self.pc:08X}] = 0x{instr:08X}: "
            opcode5 = bits(instr, 6, 2)
            funct3 = bits(instr, 14, 12)
            funct7 = bits(instr, 31, 25)
            rd = bits(instr, 11, 7)
            rs1 = bits(instr, 19, 15)
            rs2 = bits(instr, 24, 20)

            if opcode5 == 0b01101:
                imm20 = bits(instr, 31, 12)
                self.log += f"LUI x{rd}, 0x{imm20:05X}\n"
                result = imm20 << 12
                self.write_arf(rd, result)
                self.incr_pc(4)



            elif opcode5 == 0b00000:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)
                self.log += f"LW x{rd}, 0x{imm32}(x{rs1})\n"
                addr = bits(self.arf[rs1] + imm32, 31, 0)
                value = self.read_mem(addr, 4)
                self.write_arf(rd, value)
                self.incr_pc(4)

            

            elif opcode5 == 0b01000:
                imm12 = bits(instr, 11, 7)
                imm12 += bits(instr, 31, 25) << 5
                imm32 = signed32(imm12, 12)
                addr = bits(self.arf[rs1] + imm32, 31, 0)
                value = self.arf[rs2]

                if funct3 == 0b000:
                    self.log += f"illegal instr\n"
                    return False
                


                elif funct3 == 0b010:
                    self.log += f"SW x{rs2}, 0x{imm32:08X}(x{rs1})\n"
                    self.write_mem(addr, value, 4)

                else:
                    self.log += f"illegal instr\n"
                    return False

                self.incr_pc(4)

            elif opcode5 == 0b00100:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)

                if funct3 == 0b000:
                    self.log += f"ADDI x{rd}, x{rs1}, 0x{imm32:08X}\n"
                    result = bits(self.arf[rs1] + imm32, 31, 0)
                    self.write_arf(rd, result)

                else:
                    self.log += f"illegal instr\n"
                    return False



                self.incr_pc(4)

            else:
                self.log += f"illegal instr\n"
                return False

        # compressed
        else:
            instr = bits(instr, 15, 0)
            self.log += f"MEM[0x{self.pc:08X}] = 0x{instr:04X}: "

            if opcode2 == 0b00:
                self.log += f"illegal instr\n"
                return False
            
            elif opcode2 == 0b01:
                self.log += f"illegal instr\n"
                return False

            elif opcode2 == 0b10:
                rs2 = bits(instr, 6, 2)
                uimm = bits(instr, 12, 9) << 2
                uimm += bits(instr, 8, 7) << 6
                self.log += f"C.SWSP x{rs2}, 0x{uimm:02X}\n"
                addr = bits(self.arf[2] + uimm, 31, 0)
                value = self.arf[rs2]
                self.write_mem(addr, value, 4)
                self.incr_pc(2)
                
            else:
                self.log += f"illegal instr\n"
                return False

        return True
    
    def write_arf(self, dest, value):
        if dest == 0:
            self.log += f"    ARF[x0] = 0x00000000 <=/= 0x{value:08X}\n"
        else:
            self.log += f"    ARF[x{dest}] <= 0x{value:08X}\n"
            self.arf[dest] = value

    def write_pc(self, value):
        self.log += f"    PC <= 0x{value:08X}\n"
        self.pc = value
    
    def incr_pc(self, incr):
        self.write_pc(self.pc + incr)

    def read_mem(self, addr, num_bytes):
        value = 0
        for i in range(num_bytes):
            sub_addr = bits(addr+i, 31, 0)
            sub_value = self.mem[sub_addr]
            self.log += f"    MEM[0x{sub_addr:08X}] = 0x{sub_value:02X}\n"
            value += sub_value << 8*i
        return value

    def write_mem(self, addr, value, num_bytes):
        for i in range(num_bytes):
            sub_addr = bits(addr+i, 31, 0)
            sub_value = bits(value, 8*i+7, 8*i)
            self.log += f"    MEM[0x{sub_addr:08X}] <= 0x{sub_value:02X}\n"
            self.mem[sub_addr] = sub_value

    def print_log(self):
        print(self.log)

    def print_arf(self):
        print(f"ARF:")
        for ar, value in enumerate(self.arf):
            print(f"    {ar:2d}: 0x{value:08X}")

    def print_mem(self):
        
        word_list = get_word_list(self.mem)

        print("\nMEM:")
        for word_addr, word_value in word_list:
            word_value_str = " ".join([f"{x:02X}" for x in word_value])
            print(f"    0x{word_addr << 2:08X}: {word_value_str}")
        print()

if __name__ == "__main__":
    print(" ".join(sys.argv))

    parser = argparse.ArgumentParser()
    parser.add_argument("input_mem_file_path")
    parser.add_argument("output_mem_file_path")
    parser.add_argument("-pc", "--start-pc", default=0x0)
    parser.add_argument("-s", "--steps", action="store_true")
    args = parser.parse_args()
    # print(args)

    # read mem
    with open(args.input_mem_file_path, "r") as fp:
        input_mem_lines = fp.readlines()

    # parse input mem
    mem = dict()
    ptr = 0x0
    for mem_line in input_mem_lines:
        # ignore all comments on the right
        if "//" in mem_line:
            mem_line = mem_line[:mem_line.index("//")]
        mem_line = mem_line.lstrip().rstrip()

        # ptr change
        if mem_line.startswith("@"):
            ptr = int(mem_line[1:], 16)

        # byte fill
        elif mem_line:
            while mem_line:
                # print(f"mem_line: {mem_line}")
                mem_line = mem_line.lstrip()
                mem[ptr] = int(mem_line[:2], 16)
                mem_line = mem_line[2:]
                ptr += 1
            
        # otherwise, empty line after removal of comments

    # init arch state
    arch_state = ArchState(args.start_pc, mem)
    arch_state.print_mem()

    # execute program
    no_exception = True
    while no_exception:
        no_exception = arch_state.exec_instr()

    arch_state.print_log()
    arch_state.print_arf()
    arch_state.print_mem()

    # write output mem
    with open(args.output_mem_file_path, "w") as fp:
        word_list = get_word_list(mem)

        first = True
        ptr_word_addr = -1
        for word_addr, word_value in word_list:
            word_value_str = " ".join([f"{x:02X}" for x in word_value])
            if word_addr != ptr_word_addr:
                if not first:
                    fp.write("\n")
                else:
                    first = False
                fp.write(f"@{word_addr << 2:X}\n")
                ptr_word_addr = word_addr
            fp.write(word_value_str + "\n")
            ptr_word_addr += 1
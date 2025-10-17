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

def bit(num, index):
    return num >> index & 0b1

def signed32(num, size=32):
    if bit(num, size-1):
        return bits((0xFFFFFFFF << size) + num, 31, 0)
    else:
        return num
    
def make_signed(num, size=32):
    if bit(num, size-1):
        return -1 * 2**(size-1) + bits(num, size-2, 0)
    else:
        return num

class ArchState:
    def __init__(self, start_pc, mem):
        self.pc = signed32(start_pc)
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

            # LUI
            if opcode5 == 0b01101:
                imm20 = bits(instr, 31, 12)
                self.log += f"LUI x{rd}, 0x{imm20:05X}\n"
                result = imm20 << 12
                self.write_arf(rd, result)
                self.incr_pc(4)

            # AUIPC
            elif opcode5 == 0b00101:
                imm20 = bits(instr, 31, 12)
                imm32 = imm20 << 12
                self.log += f"AUIPC x{rd}, 0x{imm20:05X}\n"
                result = signed32(self.pc + imm32)
                self.write_arf(rd, result)
                self.incr_pc(4)

            # JAL
            elif opcode5 == 0b11011:
                imm21 = bit(instr, 31) << 20
                imm21 += bits(instr, 30, 21) << 1
                imm21 += bit(instr, 20) << 11
                imm21 += bits(instr, 19, 12) << 12
                imm32 = signed32(imm21, 21)
                self.log += f"JAL x{rd}, 0x{imm21:06X}\n"
                result = signed32(self.pc + 4)
                self.write_arf(rd, result)
                self.incr_pc(imm32)

            # JALR
            elif opcode5 == 0b11001:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)
                self.log += f"JALR x{rd}, 0x{imm12:03X}(x{rs1})\n"
                result = signed32(self.pc + 4)
                npc = signed32(self.arf[rs1] + imm32)
                self.write_arf(rd, result)
                self.write_pc(npc)

            # B-Type
            elif opcode5 == 0b11000:
                imm13 = bit(instr, 31) << 12
                imm13 += bits(instr, 30, 25) << 5
                imm13 += bits(instr, 11, 8) << 1
                imm13 += bit(instr, 7) << 11
                imm32 = signed32(imm13, 13)
                
                # BEQ
                if funct3 == 0b000:
                    self.log += f"BEQ x{rs1}, x{rs2}, 0x{imm13:04X}\n"
                    if self.arf[rs1] == self.arf[rs2]:
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BNE
                elif funct3 == 0b001:
                    self.log += f"BNE x{rs1}, x{rs2}, 0x{imm13:04X}\n"
                    if self.arf[rs1] != self.arf[rs2]:
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BLT
                elif funct3 == 0b100:
                    self.log += f"BLT x{rs1}, x{rs2}, 0x{imm13:04X}\n"
                    if make_signed(self.arf[rs1]) < make_signed(self.arf[rs2]):
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BGE
                elif funct3 == 0b101:
                    self.log += f"BGE x{rs1}, x{rs2}, 0x{imm13:04X}\n"
                    if make_signed(self.arf[rs1]) >= make_signed(self.arf[rs2]):
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BLTU
                elif funct3 == 0b110:
                    self.log += f"BLTU x{rs1}, x{rs2}, 0x{imm13:04X}\n"
                    if self.arf[rs1] < self.arf[rs2]:
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BGEU
                elif funct3 == 0b111:
                    self.log += f"BGEU x{rs1}, x{rs2}, 0x{imm13:04X}\n"
                    if self.arf[rs1] >= self.arf[rs2]:
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                else:
                    self.log += f"illegal instr\n"
                    return False

            # L-Type
            elif opcode5 == 0b00000:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)
                addr = signed32(self.arf[rs1] + imm32)

                # LB
                if funct3 == 0b000:
                    self.log += f"LB x{rd}, 0x{imm12:03X}(x{rs1})\n"
                    value = signed32(self.read_mem(addr, 1), 8)

                # LH
                elif funct3 == 0b001:
                    self.log += f"LH x{rd}, 0x{imm12:03X}(x{rs1})\n"
                    value = signed32(self.read_mem(addr, 2), 16)

                # LW
                elif funct3 == 0b010:
                    self.log += f"LW x{rd}, 0x{imm12:03X}(x{rs1})\n"
                    value = self.read_mem(addr, 4)

                # LBU
                elif funct3 == 0b100:
                    self.log += f"LBU x{rd}, 0x{imm12:03X}(x{rs1})\n"
                    value = self.read_mem(addr, 1)

                # LHU
                elif funct3 == 0b101:
                    self.log += f"LHU x{rd}, 0x{imm12:03X}(x{rs1})\n"
                    value = self.read_mem(addr, 2)

                else:
                    self.log += f"illegal instr\n"
                    return False

                self.write_arf(rd, value)
                self.incr_pc(4)

            # S-Type
            elif opcode5 == 0b01000:
                imm12 = bits(instr, 11, 7)
                imm12 += bits(instr, 31, 25) << 5
                imm32 = signed32(imm12, 12)
                addr = bits(self.arf[rs1] + imm32, 31, 0)
                value = self.arf[rs2]

                # SB
                if funct3 == 0b000:
                    self.log += f"SB x{rs2}, 0x{imm12:03X}(x{rs1})\n"
                    self.write_mem(addr, value, 1)
                
                # SH
                elif funct3 == 0b001:
                    self.log += f"SH x{rs2}, 0x{imm12:03X}(x{rs1})\n"
                    self.write_mem(addr, value, 2)

                # SW
                elif funct3 == 0b010:
                    self.log += f"SW x{rs2}, 0x{imm12:03X}(x{rs1})\n"
                    self.write_mem(addr, value, 4)

                else:
                    self.log += f"illegal instr\n"
                    return False

                self.incr_pc(4)

            # I-Type
            elif opcode5 == 0b00100:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)
                shamt = bits(instr, 24, 20)

                # ADDI
                if funct3 == 0b000:
                    self.log += f"ADDI x{rd}, x{rs1}, 0x{imm12:03X}\n"
                    result = signed32(self.arf[rs1] + imm32)

                # SLLI
                elif funct3 == 0b001:
                    self.log += f"SLLI x{rd}, x{rs1}, 0x{shamt:02X}\n"
                    result = signed32(self.arf[rs1] << shamt)

                # SLTI
                elif funct3 == 0b010:

                    if funct7 == 0b0000000:
                        self.log += f"SLTI x{rd}, x{rs1}, 0x{imm12:03X}\n"
                        if make_signed(self.arf[rs1]) < make_signed(imm32):
                            result = 1
                        else:
                            result = 0

                    else:
                        self.log += f"illegal instr\n"
                        return False

                # SLTIU
                elif funct3 == 0b011:
                    self.log += f"SLTIU x{rd}, x{rs1}, 0x{imm12:03X}\n"
                    if self.arf[rs1] < imm32:
                        result = 1
                    else:
                        result = 0

                # XORI
                elif funct3 == 0b100:
                    self.log += f"XORI x{rd}, x{rs1}, 0x{imm12:03X}\n"
                    result = signed32(self.arf[rs1] ^ imm32)

                # SR*I
                elif funct3 == 0b101:
                        
                    # SRLI
                    if funct7 == 0b0000000:
                        self.log += f"SRLI x{rd}, x{rs1}, 0x{shamt:02X}\n"
                        result = self.arf[rs1] >> shamt

                    # SRAI
                    elif funct7 == 0b0100000:
                        self.log += f"SRAI x{rd}, x{rs1}, 0x{shamt:02X}\n"
                        result = signed32(self.arf[rs1] >> shamt, 32-shamt)

                    else:
                        self.log += f"illegal instr\n"
                        return False

                # ORI
                elif funct3 == 0b110:
                    self.log += f"ORI x{rd}, x{rs1}, 0x{imm12:03X}\n"
                    result = signed32(self.arf[rs1] | imm32)

                # ANDI
                elif funct3 == 0b111:
                    self.log += f"ORI x{rd}, x{rs1}, 0x{imm12:03X}\n"
                    result = signed32(self.arf[rs1] & imm32)

                else:
                    self.log += f"illegal instr\n"
                    return False

                self.write_arf(rd, result)
                self.incr_pc(4)

            # R-Type
            elif opcode5 == 0b01100:

                # ADD/SUB
                if funct3 == 0b000:

                    # ADD
                    if funct7 == 0b0000000:
                        self.log += f"ADD x{rd}, x{rs1}, x{rs2}\n"
                        result = signed32(self.arf[rs1] + self.arf[rs2])

                    # SUB
                    elif funct7 == 0b0100000:
                        self.log += f"ADD x{rd}, x{rs1}, x{rs2}\n"
                        result = signed32(self.arf[rs1] - self.arf[rs2])

                    else:
                        self.log += f"illegal instr\n"
                        return False

                # SLL
                elif funct3 == 0b001:
                    shamt = bits(self.arf[rs2], 4, 0)
                    if funct7 != 0b0000000:
                        self.log += f"illegal instr\n"
                        return False
                    self.log += f"SLL x{rd}, x{rs1}, x{rs2}\n"
                    result = signed32(self.arf[rs1] << shamt)

                # SLT
                elif funct3 == 0b010:
                    if funct7 != 0b0000000:
                        self.log += f"illegal instr\n"
                        return False
                    self.log += f"SLT x{rd}, x{rs1}, x{rs2}\n"
                    if make_signed(self.arf[rs1]) < make_signed(self.arf[rs2]):
                        result = 1
                    else:
                        result = 0

                # SLTU
                elif funct3 == 0b011:
                    if funct7 != 0b0000000:
                        self.log += f"illegal instr\n"
                        return False
                    self.log += f"SLTU x{rd}, x{rs1}, x{rs2}\n"
                    if self.arf[rs1] < self.arf[rs2]:
                        result = 1
                    else:
                        result = 0

                # XOR
                elif funct3 == 0b100:
                    if funct7 != 0b0000000:
                        self.log += f"illegal instr\n"
                        return False
                    self.log += f"XOR x{rd}, x{rs1}, x{rs2}\n"
                    result = signed32(self.arf[rs1] ^ self.arf[rs2])

                # SR*
                elif funct3 == 0b101:
                    shamt = bits(self.arf[rs2], 4, 0)

                    # SRL
                    if funct7 == 0b0000000:
                        self.log += f"SRL x{rd}, x{rs1}, x{rs2}\n"
                        result = self.arf[rs1] >> shamt

                    # SRA
                    elif funct7 == 0b0100000:
                        self.log += f"SRA x{rd}, x{rs1}, x{rs2}\n"
                        result = signed32(self.arf[rs1] >> shamt, 32-shamt)

                    else:
                        self.log += f"illegal instr\n"
                        return False
                    
                # OR
                elif funct3 == 0b110:
                    if funct7 != 0b0000000:
                        self.log += f"illegal instr\n"
                        return False
                    self.log += f"OR x{rd}, x{rs1}, x{rs2}\n"
                    result = signed32(self.arf[rs1] | self.arf[rs2])
                    
                # AND
                elif funct3 == 0b111:
                    if funct7 != 0b0000000:
                        self.log += f"illegal instr\n"
                        return False
                    self.log += f"AND x{rd}, x{rs1}, x{rs2}\n"
                    result = signed32(self.arf[rs1] & self.arf[rs2])

                else:
                    self.log += f"illegal instr\n"
                    return False

                self.write_arf(rd, result)
                self.incr_pc(4)

            # FENCE*
            elif opcode5 == 0b00011:
                fm = bits(instr, 31, 28)

                # FENCE[.TSO]
                if funct3 == 0b000:

                    if fm == 0b0000:
                        self.log += f"FENCE "

                    elif fm == 0b1000:
                        self.log += f"FENCE.TSO "

                    else:
                        self.log += f"illegal instr\n"
                        return False
                    
                    if bit(instr, 27):
                        self.log += "i"
                    if bit(instr, 26):
                        self.log += "o"
                    if bit(instr, 25):
                        self.log += "r"
                    if bit(instr, 24):
                        self.log += "w"

                    self.log += f", "

                    if bit(instr, 23):
                        self.log += "i"
                    if bit(instr, 22):
                        self.log += "o"
                    if bit(instr, 21):
                        self.log += "r"
                    if bit(instr, 20):
                        self.log += "w"

                # FENCE.I
                elif funct3 == 0b001:
                    pass

                else:
                    self.log += f"illegal instr\n"
                    return False

                self.incr_pc(4)

            # SYS
            elif opcode5 == 0b11100:

                # ECALL/EBREAK
                if funct3 == 0b000:

                    if funct7 != 0 or rs1 != 0 or rd != 0:
                        self.log += f"illegal instr\n"
                        return False

                    # ECALL
                    if rd == 0b00000:
                        self.log += f"ECALL"
                        return False
                    
                    # EBREAK
                    elif rd == 0b00001:
                        self.log += f"EBREAK"
                        return False
                
                    else:
                        self.log += f"illegal instr"
                        return False
                    
                # CSR
                else:
                    csr = bits(instr, 31, 20)
                    uimm = rs1
                    
                    # CSRRW
                    if funct3 == 0b001:
                        self.log += f"CSRRW x{rd}, 0x{csr:03X}, x{rs1}"
                        return False
                        
                    # CSRRS
                    elif funct3 == 0b010:
                        self.log += f"CSRRS x{rd}, 0x{csr:03X}, x{rs1}"
                        return False
                        
                    # CSRRC
                    elif funct3 == 0b011:
                        self.log += f"CSRRC x{rd}, 0x{csr:03X}, x{rs1}"
                        return False
                        
                    # CSRRWI
                    elif funct3 == 0b101:
                        self.log += f"CSRRWI x{rd}, 0x{csr:03X}, 0x{uimm:02X}"
                        return False
                        
                    # CSRRSI
                    elif funct3 == 0b110:
                        self.log += f"CSRRSI x{rd}, 0x{csr:03X}, 0x{uimm:02X}"
                        return False
                        
                    # CSRRCI
                    elif funct3 == 0b111:
                        self.log += f"CSRRCI x{rd}, 0x{csr:03X}, 0x{uimm:02X}"
                        return False
                
                    else:
                        self.log += f"illegal instr"
                        return False
                    
                self.incr_pc(4)

            # M-Ext
            elif opcode5 == 0b01100:
                
                if funct7 != 0b0000001:
                    self.log += f"illegal instr"
                    return False

                # MUL
                if funct3 == 0b000:
                    self.log += f"MUL x{rd}, x{rs1}, x{rs2}"
                    result = signed32(self.arf[rs1] * self.arf[rs2])
                
                # MULH
                elif funct3 == 0b001:
                    self.log += f"MULH x{rd}, x{rs1}, x{rs2}"
                    result = signed32((make_signed(self.arf[rs1]) * make_signed(self.arf[rs2])) >> 32)

                # MULHSU
                elif funct3 == 0b010:
                    self.log += f"MULHSU x{rd}, x{rs1}, x{rs2}"
                    result = signed32((make_signed(self.arf[rs1]) * self.arf[rs2]) >> 32)

                # MULHU
                elif funct3 == 0b011:
                    self.log += f"MULHU x{rd}, x{rs1}, x{rs2}"
                    result = signed32((self.arf[rs1] * self.arf[rs2]) >> 32)

                # DIV
                elif funct3 == 0b100:
                    self.log += f"DIV x{rd}, x{rs1}, x{rs2}"
                    if self.arf[rs2] == 0:
                        result = 0xFFFFFFFF
                    # elif self.arf[rs1] == 0x80000000 and self.arf[rs2] == 0xFFFFFFFF:
                    #     result = 0x80000000
                        # default case handles this overflow, get 0x80000000 regardless
                    else:
                        result = signed32(int(make_signed(self.arf[rs1]) / make_signed(self.arf[rs2])))

                # DIVU
                elif funct3 == 0b101:
                    self.log += f"DIVU x{rd}, x{rs1}, x{rs2}"
                    if self.arf[rs2] == 0:
                        result = 0xFFFFFFFF
                    else:
                        result = signed32(self.arf[rs1] // self.arf[rs2])

                # REM
                elif funct3 == 0b110:
                    self.log += f"REM x{rd}, x{rs1}, x{rs2}"
                    if self.arf[rs2] == 0:
                        result = self.arf[rs1]
                    else:
                        quotient = int(self.arf[rs1] / self.arf[rs2]) # round towards 0
                        result = self.arf[rs1] - (quotient * self.arf[rs2])

                # REMU
                elif funct3 == 0b111:
                    self.log += f"REM x{rd}, x{rs1}, x{rs2}"
                    if self.arf[rs2] == 0:
                        result = self.arf[rs1]
                    else:
                        result = signed32(self.arf[rs1] % self.arf[rs2])

                self.write_arf(rd, result)
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
            self.arf[dest] = signed32(value)

    def write_pc(self, value):
        self.log += f"    PC <= 0x{value:08X}\n"
        self.pc = signed32(value)
    
    def incr_pc(self, incr):
        self.write_pc(signed32(self.pc + incr))

    def read_mem(self, addr, num_bytes):
        value = 0
        for i in range(num_bytes):
            sub_addr = signed32(addr + i)
            sub_value = self.mem[sub_addr]
            self.log += f"    MEM[0x{sub_addr:08X}] = 0x{sub_value:02X}\n"
            value += sub_value << 8*i
        return value

    def write_mem(self, addr, value, num_bytes):
        for i in range(num_bytes):
            sub_addr = signed32(addr + i)
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
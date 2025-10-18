import sys
import argparse

def bits(num, upper_index, lower_index):
    return (num >> lower_index) & (2**(upper_index - lower_index + 1) - 1)

def bit(num, index):
    return num >> index & 0b1

def signed32(num, size=32):
    if bit(num, size-1):
        return bits((0xFFFFFFFF << size) + num, 31, 0)
    else:
        return bits(num, size-1, 0)
    
def make_signed(num, size=32):
    if bit(num, size-1):
        return -1 * 2**(size-1) + bits(num, size-2, 0)
    else:
        return bits(num, size-1, 0)
    
class Log:
    def __init__(self):
        self.log_str = ""

    def write(self, string):
        self.log_str += string

    def print_log(self):
        print(self.log_str)
        self.log_str = ""

class Mem:
    def __init__(self, mem_file_path, log):
        self.log = log
        self.reserve_set_dict = dict()

        # read mem
        with open(mem_file_path, "r") as fp:
            input_mem_lines = fp.readlines()

        # parse input mem
        self.mem_dict = dict()
        ptr = 0x0
        try:
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
                        self.mem_dict[ptr] = int(mem_line[:2], 16)
                        mem_line = mem_line[2:]
                        ptr += 1
                    
                # otherwise, empty line after removal of comments
        
        except ValueError:
            raise Exception("ERROR: input mem file syntax error")

    def read_instr(self, pc):
        instr = 0
        for i in range(4):
            if pc + i in self.mem_dict:
                instr += self.mem_dict[pc + i] << 8 * i
            else:
                break
        return instr

    def read_data(self, addr, num_bytes):
        value = 0
        for i in range(num_bytes):
            sub_addr = signed32(addr + i)
            try:
                sub_value = self.mem_dict[sub_addr]
            except KeyError as e:
                sub_value = 0x00
            self.log.write(f"    MEM[0x{sub_addr:08X}] = 0x{sub_value:02X}\n")
            value += sub_value << 8 * i
        return value

    def write_data(self, addr, value, num_bytes):
        for i in range(num_bytes):
            sub_addr = signed32(addr + i)
            delete_id_list = []
            for hart_id, word_addr in self.reserve_set_dict.items():
                if sub_addr >> 2 == word_addr:
                    self.log.write(f"    invalidating reservation set for Hart {hart_id}: 0x{word_addr << 2:08X}\n")
                    delete_id_list.append(hart_id)
            for hart_id in delete_id_list:
                self.reserve_set_dict.pop(hart_id)
            sub_value = bits(value, 8*i+7, 8*i)
            self.log.write(f"    MEM[0x{sub_addr:08X}] <= 0x{sub_value:02X}\n")
            self.mem_dict[sub_addr] = sub_value

    def reserve_set(self, hart_id, byte_addr):
        self.reserve_set_dict[hart_id] = byte_addr >> 2 # word addr granularity
        self.log.write(f"    new reservation set for Hart {hart_id}: 0x{byte_addr:08X}\n")

    def check_reserve_set(self, hart_id, byte_addr):
        self.log.write(f"    check reservation set for Hart {hart_id} for addr: 0x{byte_addr:08X}\n")

        valid = False
        if hart_id in self.reserve_set_dict.keys():
            self.log.write(f"    reservation set: 0x{self.reserve_set_dict[hart_id] << 2:08X}\n")
            if self.reserve_set_dict[hart_id] == byte_addr >> 2: # word addr granularity
                valid = True
        else:
            self.log.write(f"    reservation set: invalid\n")

        if valid:
            self.log.write(f"    reservation set check passed\n")
        else:
            self.log.write(f"    reservation set check failed\n")
            
        return valid

    def get_word_list(self):
        word_dict = dict()
        for byte_addr, byte_value in self.mem_dict.items():
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

    def print_mem(self):
        word_list = self.get_word_list()

        print("\nMEM:")
        for word_addr, word_value in word_list:
            word_value_str = " ".join([f"{x:02X}" for x in word_value])
            print(f"    0x{word_addr << 2:08X}: {word_value_str}")
        print()

    def write_mem_file(self, mem_file_path):
        with open(mem_file_path, "w") as fp:
            word_list = self.get_word_list()

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

class Hart:
    def __init__(self, hart_id, start_pc, mem, log, trace):
        self.hart_id = hart_id
        self.pc = signed32(start_pc)
        self.arf = [0x0 for x in range(32)]
        self.instret = 0
        self.mem = mem
        self.log = log
        self.trace = trace

    def exec_instr(self):
        self.log.write(f"Hart {self.hart_id}: PC = 0x{self.pc:08X}:\n")

        # read instr
        instr = self.mem.read_instr(self.pc)
        opcode2 = bits(instr, 1, 0)

        # uncompressed
        if opcode2 == 0b11:
            self.log.write(f"    MEM[0x{self.pc:08X}] = 0x{instr:08X}: ")
            opcode5 = bits(instr, 6, 2)
            funct3 = bits(instr, 14, 12)
            funct7 = bits(instr, 31, 25)
            rd = bits(instr, 11, 7)
            rs1 = bits(instr, 19, 15)
            rs2 = bits(instr, 24, 20)

            # LUI
            if opcode5 == 0b01101:
                imm20 = bits(instr, 31, 12)
                self.log.write(f"LUI x{rd}, 0x{imm20:05X}\n")
                result = imm20 << 12
                self.write_arf(rd, result)
                self.incr_pc(4)

            # AUIPC
            elif opcode5 == 0b00101:
                imm20 = bits(instr, 31, 12)
                imm32 = imm20 << 12
                self.log.write(f"AUIPC x{rd}, 0x{imm20:05X}\n")
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
                self.log.write(f"JAL x{rd}, 0x{imm21:06X}\n")
                result = signed32(self.pc + 4)
                self.write_arf(rd, result)
                self.incr_pc(imm32)

            # JALR
            elif opcode5 == 0b11001:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)
                self.log.write(f"JALR x{rd}, 0x{imm12:03X}(x{rs1})\n")
                result = signed32(self.pc + 4)
                npc = signed32(self.read_arf(rs1) + imm32)
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
                    self.log.write(f"BEQ x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if self.read_arf(rs1) == self.read_arf(rs2):
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BNE
                elif funct3 == 0b001:
                    self.log.write(f"BNE x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if self.read_arf(rs1) != self.read_arf(rs2):
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BLT
                elif funct3 == 0b100:
                    self.log.write(f"BLT x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if make_signed(self.read_arf(rs1)) < make_signed(self.read_arf(rs2)):
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BGE
                elif funct3 == 0b101:
                    self.log.write(f"BGE x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if make_signed(self.read_arf(rs1)) >= make_signed(self.read_arf(rs2)):
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BLTU
                elif funct3 == 0b110:
                    self.log.write(f"BLTU x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if self.read_arf(rs1) < self.read_arf(rs2):
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                # BGEU
                elif funct3 == 0b111:
                    self.log.write(f"BGEU x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if self.read_arf(rs1) >= self.read_arf(rs2):
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(4)

                else:
                    self.log.write(f"illegal B-Type instr\n")
                    return False

            # L-Type
            elif opcode5 == 0b00000:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)

                # LB
                if funct3 == 0b000:
                    self.log.write(f"LB x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed32(self.read_arf(rs1) + imm32)
                    value = signed32(self.mem.read_data(addr, 1), 8)

                # LH
                elif funct3 == 0b001:
                    self.log.write(f"LH x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed32(self.read_arf(rs1) + imm32)
                    value = signed32(self.mem.read_data(addr, 2), 16)

                # LW
                elif funct3 == 0b010:
                    self.log.write(f"LW x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed32(self.read_arf(rs1) + imm32)
                    value = self.mem.read_data(addr, 4)

                # LBU
                elif funct3 == 0b100:
                    self.log.write(f"LBU x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed32(self.read_arf(rs1) + imm32)
                    value = self.mem.read_data(addr, 1)

                # LHU
                elif funct3 == 0b101:
                    self.log.write(f"LHU x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed32(self.read_arf(rs1) + imm32)
                    value = self.mem.read_data(addr, 2)

                else:
                    self.log.write(f"illegal L-Type instr\n")
                    return False

                self.write_arf(rd, value)
                self.incr_pc(4)

            # S-Type
            elif opcode5 == 0b01000:
                imm12 = bits(instr, 11, 7)
                imm12 += bits(instr, 31, 25) << 5
                imm32 = signed32(imm12, 12)

                # SB
                if funct3 == 0b000:
                    self.log.write(f"SB x{rs2}, 0x{imm12:03X}(x{rs1})\n")
                    addr = bits(self.read_arf(rs1) + imm32, 31, 0)
                    value = self.read_arf(rs2)
                    self.mem.write_data(addr, value, 1)
                
                # SH
                elif funct3 == 0b001:
                    self.log.write(f"SH x{rs2}, 0x{imm12:03X}(x{rs1})\n")
                    addr = bits(self.read_arf(rs1) + imm32, 31, 0)
                    value = self.read_arf(rs2)
                    self.mem.write_data(addr, value, 2)

                # SW
                elif funct3 == 0b010:
                    self.log.write(f"SW x{rs2}, 0x{imm12:03X}(x{rs1})\n")
                    addr = bits(self.read_arf(rs1) + imm32, 31, 0)
                    value = self.read_arf(rs2)
                    self.mem.write_data(addr, value, 4)

                else:
                    self.log.write(f"illegal S-Type instr\n")
                    return False

                self.incr_pc(4)

            # I-Type
            elif opcode5 == 0b00100:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)
                shamt = bits(instr, 24, 20)

                # ADDI
                if funct3 == 0b000:
                    self.log.write(f"ADDI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed32(self.read_arf(rs1) + imm32)

                # SLLI
                elif funct3 == 0b001:
                    if funct7 == 0b0000000:
                        self.log.write(f"SLLI x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = signed32(self.read_arf(rs1) << shamt)
                    else:
                        self.log.write(f"illegal I-Type instr\n")
                        return False

                # SLTI
                elif funct3 == 0b010:
                    self.log.write(f"SLTI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    if make_signed(self.read_arf(rs1)) < make_signed(imm32):
                        result = 1
                    else:
                        result = 0

                # SLTIU
                elif funct3 == 0b011:
                    self.log.write(f"SLTIU x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    if self.read_arf(rs1) < imm32:
                        result = 1
                    else:
                        result = 0

                # XORI
                elif funct3 == 0b100:
                    self.log.write(f"XORI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed32(self.read_arf(rs1) ^ imm32)

                # SR*I
                elif funct3 == 0b101:
                        
                    # SRLI
                    if funct7 == 0b0000000:
                        self.log.write(f"SRLI x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = self.read_arf(rs1) >> shamt

                    # SRAI
                    elif funct7 == 0b0100000:
                        self.log.write(f"SRAI x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = signed32(self.read_arf(rs1) >> shamt, 32-shamt)

                    else:
                        self.log.write(f"illegal I-Type instr\n")
                        return False

                # ORI
                elif funct3 == 0b110:
                    self.log.write(f"ORI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed32(self.read_arf(rs1) | imm32)

                # ANDI
                elif funct3 == 0b111:
                    self.log.write(f"ANDI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed32(self.read_arf(rs1) & imm32)

                else:
                    self.log.write(f"illegal I-Type instr\n")
                    return False

                self.write_arf(rd, result)
                self.incr_pc(4)

            # R-Type and M-Ext
            elif opcode5 == 0b01100:

                # R-Type
                if funct7 == 0b0000000 or funct7 == 0b0100000:

                    # ADD/SUB
                    if funct3 == 0b000:

                        # ADD
                        if funct7 == 0b0000000:
                            self.log.write(f"ADD x{rd}, x{rs1}, x{rs2}\n")
                            result = signed32(self.read_arf(rs1) + self.read_arf(rs2))

                        # SUB
                        elif funct7 == 0b0100000:
                            self.log.write(f"SUB x{rd}, x{rs1}, x{rs2}\n")
                            result = signed32(self.read_arf(rs1) - self.read_arf(rs2))

                        else:
                            self.log.write(f"illegal R-Type instr\n")
                            return False

                    # SLL
                    elif funct3 == 0b001:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            return False
                        self.log.write(f"SLL x{rd}, x{rs1}, x{rs2}\n")
                        shamt = bits(self.read_arf(rs2), 4, 0)
                        self.log.write(f"    shamt = {shamt}\n")
                        result = signed32(self.read_arf(rs1) << shamt)

                    # SLT
                    elif funct3 == 0b010:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            return False
                        self.log.write(f"SLT x{rd}, x{rs1}, x{rs2}\n")
                        if make_signed(self.read_arf(rs1)) < make_signed(self.read_arf(rs2)):
                            result = 1
                        else:
                            result = 0

                    # SLTU
                    elif funct3 == 0b011:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            return False
                        self.log.write(f"SLTU x{rd}, x{rs1}, x{rs2}\n")
                        if self.read_arf(rs1) < self.read_arf(rs2):
                            result = 1
                        else:
                            result = 0

                    # XOR
                    elif funct3 == 0b100:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            return False
                        self.log.write(f"XOR x{rd}, x{rs1}, x{rs2}\n")
                        result = signed32(self.read_arf(rs1) ^ self.read_arf(rs2))

                    # SR*
                    elif funct3 == 0b101:

                        # SRL
                        if funct7 == 0b0000000:
                            self.log.write(f"SRL x{rd}, x{rs1}, x{rs2}\n")
                            shamt = bits(self.read_arf(rs2), 4, 0)
                            self.log.write(f"    shamt = {shamt}\n")
                            result = self.read_arf(rs1) >> shamt

                        # SRA
                        elif funct7 == 0b0100000:
                            self.log.write(f"SRA x{rd}, x{rs1}, x{rs2}\n")
                            shamt = bits(self.read_arf(rs2), 4, 0)
                            self.log.write(f"    shamt = {shamt}\n")
                            result = signed32(self.read_arf(rs1) >> shamt, 32-shamt)

                        else:
                            self.log.write(f"illegal R-Type instr\n")
                            return False
                        
                    # OR
                    elif funct3 == 0b110:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            return False
                        self.log.write(f"OR x{rd}, x{rs1}, x{rs2}\n")
                        result = signed32(self.read_arf(rs1) | self.read_arf(rs2))
                        
                    # AND
                    elif funct3 == 0b111:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            return False
                        self.log.write(f"AND x{rd}, x{rs1}, x{rs2}\n")
                        result = signed32(self.read_arf(rs1) & self.read_arf(rs2))

                    else:
                        self.log.write(f"illegal R-Type instr\n")
                        return False
                    
                # M-Ext
                elif funct7 == 0b0000001:

                    # MUL
                    if funct3 == 0b000:
                        self.log.write(f"MUL x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        result = signed32(R_rs1 * R_rs2)
                    
                    # MULH
                    elif funct3 == 0b001:
                        self.log.write(f"MULH x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        result = signed32((make_signed(R_rs1) * make_signed(R_rs2)) >> 32)

                    # MULHSU
                    elif funct3 == 0b010:
                        self.log.write(f"MULHSU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        result = signed32((make_signed(R_rs1) * R_rs2) >> 32)

                    # MULHU
                    elif funct3 == 0b011:
                        self.log.write(f"MULHU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        result = signed32((R_rs1 * R_rs2) >> 32)

                    # DIV
                    elif funct3 == 0b100:
                        self.log.write(f"DIV x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs2 == 0:
                            result = 0xFFFFFFFF
                        # elif R_rs1 == 0x80000000 and R_rs2 == 0xFFFFFFFF:
                        #     result = 0x80000000
                            # default case handles this overflow, get 0x80000000 regardless
                        else:
                            result = signed32(int(make_signed(R_rs1) / make_signed(R_rs2)))

                    # DIVU
                    elif funct3 == 0b101:
                        self.log.write(f"DIVU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs2 == 0:
                            result = 0xFFFFFFFF
                        else:
                            result = signed32(R_rs1 // R_rs2)

                    # REM
                    elif funct3 == 0b110:
                        self.log.write(f"REM x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs2 == 0:
                            result = R_rs1
                        else:
                            quotient = int(make_signed(R_rs1) / make_signed(R_rs2)) # round towards 0
                            result = signed32(make_signed(R_rs1) - (quotient * make_signed(R_rs2)))

                    # REMU
                    elif funct3 == 0b111:
                        self.log.write(f"REMU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs2 == 0:
                            result = R_rs1
                        else:
                            result = signed32(R_rs1 % R_rs2)

                else:
                    self.log.write(f"illegal R-Type / M-Ext instr\n")
                    return False

                self.write_arf(rd, result)
                self.incr_pc(4)

            # FENCE*
            elif opcode5 == 0b00011:
                fm = bits(instr, 31, 28)

                # FENCE[.TSO]
                if funct3 == 0b000:

                    if fm == 0b0000:
                        self.log.write(f"FENCE ")

                    elif fm == 0b1000:
                        self.log.write(f"FENCE.TSO ")

                    else:
                        self.log.write(f"illegal FENCE instr\n")
                        return False
                    
                    if bit(instr, 27):
                        self.log.write("i")
                    if bit(instr, 26):
                        self.log.write("o")
                    if bit(instr, 25):
                        self.log.write("r")
                    if bit(instr, 24):
                        self.log.write("w")

                    self.log.write(f", ")

                    if bit(instr, 23):
                        self.log.write("i")
                    if bit(instr, 22):
                        self.log.write("o")
                    if bit(instr, 21):
                        self.log.write("r")
                    if bit(instr, 20):
                        self.log.write("w")
                    
                    self.log.write(f"\n")

                # FENCE.I
                elif funct3 == 0b001:
                    self.log.write(f"FENCE.I\n")

                else:
                    self.log.write(f"illegal FENCE instr\n")
                    return False

                self.incr_pc(4)

            # SYS
            elif opcode5 == 0b11100:

                # ECALL/EBREAK
                if funct3 == 0b000:

                    if funct7 != 0 or rs1 != 0 or rd != 0:
                        self.log.write(f"illegal ECALL/EBREAK instr\n")
                        return False

                    # ECALL
                    if rs2 == 0b00000:
                        self.log.write(f"ECALL\n")
                        return False
                    
                    # EBREAK
                    elif rs2 == 0b00001:
                        self.log.write(f"EBREAK\n")
                        return False
                
                    else:
                        self.log.write(f"illegal ECALL/EBREAK instr\n")
                        return False
                    
                # CSR
                else:
                    csr = bits(instr, 31, 20)
                    uimm = rs1
                    
                    # CSRRW
                    if funct3 == 0b001:
                        self.log.write(f"CSRRW x{rd}, 0x{csr:03X}, x{rs1}\n")
                        return False
                        
                    # CSRRS
                    elif funct3 == 0b010:
                        self.log.write(f"CSRRS x{rd}, 0x{csr:03X}, x{rs1}\n")
                        return False
                        
                    # CSRRC
                    elif funct3 == 0b011:
                        self.log.write(f"CSRRC x{rd}, 0x{csr:03X}, x{rs1}\n")
                        return False
                        
                    # CSRRWI
                    elif funct3 == 0b101:
                        self.log.write(f"CSRRWI x{rd}, 0x{csr:03X}, 0x{uimm:02X}\n")
                        return False
                        
                    # CSRRSI
                    elif funct3 == 0b110:
                        self.log.write(f"CSRRSI x{rd}, 0x{csr:03X}, 0x{uimm:02X}\n")
                        return False
                        
                    # CSRRCI
                    elif funct3 == 0b111:
                        self.log.write(f"CSRRCI x{rd}, 0x{csr:03X}, 0x{uimm:02X}\n")
                        return False
                
                    else:
                        self.log.write(f"illegal SYS instr\n")
                        return False
                    
                self.incr_pc(4)

            # A-Ext
            elif opcode5 == 0b01011:
                funct5 = bits(instr, 31, 27)
                aq = bit(instr, 26)
                rl = bit(instr, 25)
                if aq:
                    if rl:
                        aqrl_str = ".AQRL"
                    else:
                        aqrl_str = ".AQ"
                elif rl:
                    aqrl_str = ".RL"
                else:
                    aqrl_str = ""

                if funct3 != 0b010:
                    self.log.write(f"illegal A-Ext instr\n")
                    return False

                # LR.W
                if funct5 == 0b00010:
                    self.log.write(f"LR.W{aqrl_str} x{rd}, (x{rs1})\n")
                    R_rs1 = self.read_arf(rs1)
                    R_rs2 = self.read_arf(rs2)
                    if R_rs1 % 4 != 0:
                        self.log.write(f"misaligned AMO\n")
                        self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                        return False
                    self.mem.reserve_set(self.hart_id, R_rs1)
                    read_value = self.mem.read_data(R_rs1, 4)

                # SC.W
                elif funct5 == 0b00011:
                    self.log.write(f"SC.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                    R_rs1 = self.read_arf(rs1)
                    R_rs2 = self.read_arf(rs2)
                    if R_rs1 % 4 != 0:
                        self.log.write(f"misaligned AMO\n")
                        self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                        return False
                    if self.mem.check_reserve_set(self.hart_id, R_rs1):
                        self.mem.write_data(R_rs1, R_rs2, 4)
                        read_value = 0
                    else:
                        read_value = 1

                # AMO*
                else:
                    # AMOSWAP.W
                    if funct5 == 0b00001:
                        self.log.write(f"AMOSWAP.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        write_value = R_rs2
                        self.mem.write_data(R_rs1, write_value, 4)

                    # AMOADD.W
                    elif funct5 == 0b00000:
                        self.log.write(f"AMOADD.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        write_value = signed32(read_value + R_rs2)
                        self.mem.write_data(R_rs1, write_value, 4)

                    # AMOXOR.W
                    elif funct5 == 0b00100:
                        self.log.write(f"AMOXOR.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        write_value = signed32(read_value ^ R_rs2)
                        self.mem.write_data(R_rs1, write_value, 4)

                    # AMOAND.W
                    elif funct5 == 0b01100:
                        self.log.write(f"AMOAND.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        write_value = signed32(read_value & R_rs2)
                        self.mem.write_data(R_rs1, write_value, 4)

                    # AMOOR.W
                    elif funct5 == 0b01000:
                        self.log.write(f"AMOOR.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        write_value = signed32(read_value | R_rs2)
                        self.mem.write_data(R_rs1, write_value, 4)

                    # AMOMIN.W
                    elif funct5 == 0b10000:
                        self.log.write(f"AMOMIN.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        if make_signed(R_rs2) < make_signed(read_value):
                            write_value = R_rs2
                        else:
                            write_value = read_value
                        self.mem.write_data(R_rs1, write_value, 4)

                    # AMOMAX.W
                    elif funct5 == 0b10100:
                        self.log.write(f"AMOMAX.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        if make_signed(R_rs2) > make_signed(read_value):
                            write_value = R_rs2
                        else:
                            write_value = read_value
                        self.mem.write_data(R_rs1, write_value, 4)

                    # AMOMINU.W
                    elif funct5 == 0b11000:
                        self.log.write(f"AMOMINU.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        if R_rs2 < read_value:
                            write_value = R_rs2
                        else:
                            write_value = read_value
                        self.mem.write_data(R_rs1, write_value, 4)

                    # AMOMAXU.W
                    elif funct5 == 0b11100:
                        self.log.write(f"AMOMAXU.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            return False
                        read_value = self.mem.read_data(R_rs1, 4)
                        if R_rs2 > read_value:
                            write_value = R_rs2
                        else:
                            write_value = read_value
                        self.mem.write_data(R_rs1, write_value, 4)

                    else:
                        self.log.write(f"illegal A-Ext instr\n")
                        return False
                
                self.write_arf(rd, read_value)
                self.incr_pc(4)

            else:
                self.log.write(f"illegal uncompressed instr\n")
                return False

        # compressed
        else:
            instr = bits(instr, 15, 0)
            self.log.write(f"    MEM[0x{self.pc:08X}] = 0x{instr:04X}: ")

            if opcode2 == 0b00:
                self.log.write(f"illegal compressed instr\n")
                return False
            
            elif opcode2 == 0b01:
                self.log.write(f"illegal compressed instr\n")
                return False

            elif opcode2 == 0b10:
                rs2 = bits(instr, 6, 2)
                uimm = bits(instr, 12, 9) << 2
                uimm += bits(instr, 8, 7) << 6
                self.log.write(f"C.SWSP x{rs2}, 0x{uimm:02X}\n")
                addr = bits(self.read_arf(2) + uimm, 31, 0)
                value = self.read_arf(rs2)
                self.mem.write_data(addr, value, 4)
                self.incr_pc(2)
                
            else:
                self.log.write(f"illegal compressed instr\n")
                return False

        self.instret += 1
        if self.trace:
            self.log.print_log()
        return True
    
    def read_arf(self, rs):
        self.log.write(f"    ARF[x{rs}] = 0x{self.arf[rs]:08X}\n")
        return self.arf[rs]
    
    def write_arf(self, dest, value):
        if dest == 0:
            self.log.write(f"    ARF[x0] = 0x00000000 <=/= 0x{value:08X}\n")
        else:
            self.log.write(f"    ARF[x{dest}] <= 0x{value:08X}\n")
            self.arf[dest] = signed32(value)

    def write_pc(self, value):
        self.log.write(f"    PC <= 0x{value:08X}\n")
        self.pc = signed32(value)
    
    def incr_pc(self, incr):
        self.write_pc(signed32(self.pc + incr))

    def print_hart(self):
        print(f"Hart {self.hart_id}:")
        print(f"    PC = 0x{self.pc:08X}")
        print(f"    instret = {self.instret}")
        print(f"    ARF:")
        for ar, value in enumerate(self.arf):
            print(f"        {ar:2d}: 0x{value:08X}")

if __name__ == "__main__":
    print(" ".join(sys.argv))

    parser = argparse.ArgumentParser()
    parser.add_argument("input_mem_file_path")
    parser.add_argument("output_mem_file_path")
    parser.add_argument("-pc", "--start-pc", default=0x0)
    parser.add_argument("-s", "--silent", action="store_true")
    args = parser.parse_args()

    # init arch components
    log = Log()
    mem = Mem(args.input_mem_file_path, log)
    hart = Hart(0, args.start_pc, mem, log, not args.silent)

    if not args.silent:
        mem.print_mem()

    # execute program
    while hart.exec_instr():
        continue

    if not args.silent:
        log.print_log()
        hart.print_hart()
        mem.print_mem()

    mem.write_mem_file(args.output_mem_file_path)
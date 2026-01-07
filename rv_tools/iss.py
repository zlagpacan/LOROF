import sys
import argparse
import numpy as np

def bits(num, upper_index, lower_index):
    return (num >> lower_index) & (2**(upper_index - lower_index + 1) - 1)

def bit(num, index):
    return num >> index & 0b1

def signed32(num, size=32):
    if bit(num, size-1):
        return bits((0xFFFFFFFF << size) + num, 31, 0)
    else:
        return bits(num, size-1, 0)
    
def signed64(num, size=64):
    if bit(num, size-1):
        return bits((0xFFFFFFFF_FFFFFFFF << size) + num, 63, 0)
    else:
        return bits(num, size-1, 0)

def make_signed(num, size=64):
    if bit(num, size-1):
        return -1 * 2**(size-1) + bits(num, size-2, 0)
    else:
        return bits(num, size-1, 0)
    
class Log:
    def __init__(self):
        self.log_str = ""

    def write(self, string):
        self.log_str += string

    def print(self):
        print(self.log_str)
        self.log_str = ""

class PerfCounters:
    perf_counter_name_list = [
        "any instr",
        "alu_reg instr",
        "alu_imm instr",
        "mdu instr",
        "bru instr",
        "ldu instr",
        "stamofu instr",
        "sysu instr",
        "fpu instr",
    ]

    def __init__(self):
        self.perf_counter_dict = dict()
        for perf_counter_name in self.perf_counter_name_list:
            self.perf_counter_dict[perf_counter_name] = 0

    def incr(self, perf_counter_name):
        self.perf_counter_dict[perf_counter_name] += 1

    def func(self, perf_counter_name, function):
        self.perf_counter_dict[perf_counter_name] = function(self.perf_counter_dict[perf_counter_name])
    
    def print(self):
        print(f"Perf Counters:")
        for perf_counter_name, perf_counter_value in self.perf_counter_dict.items():
            print(f"    {perf_counter_name}: {perf_counter_value}")
        print()

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
            sub_addr = signed64(addr + i)
            try:
                sub_value = self.mem_dict[sub_addr]
            except KeyError as e:
                sub_value = 0x00
            self.log.write(f"    MEM[0x{sub_addr:016X}] => 0x{sub_value:02X}\n")
            value += sub_value << 8 * i
        return value

    def write_data(self, addr, value, num_bytes):
        for i in range(num_bytes):
            sub_addr = signed64(addr + i)
            delete_id_list = []
            for hart_id, doubleword_addr in self.reserve_set_dict.items():
                if sub_addr >> 3 == doubleword_addr:
                    self.log.write(f"    invalidating reservation set for Hart {hart_id}: 0x{doubleword_addr << 3:016X}\n")
                    delete_id_list.append(hart_id)
            for hart_id in delete_id_list:
                self.reserve_set_dict.pop(hart_id)
            sub_value = bits(value, 8*i+7, 8*i)
            self.log.write(f"    MEM[0x{sub_addr:016X}] <= 0x{sub_value:02X}\n")
            self.mem_dict[sub_addr] = sub_value

    def reserve_set(self, hart_id, byte_addr):
        self.reserve_set_dict[hart_id] = byte_addr >> 3 # doubleword addr granularity
        self.log.write(f"    new reservation set for Hart {hart_id}: 0x{byte_addr:016X}\n")

    def check_reserve_set(self, hart_id, byte_addr):
        self.log.write(f"    check reservation set for Hart {hart_id} for addr: 0x{byte_addr:016X}\n")

        valid = False
        if hart_id in self.reserve_set_dict.keys():
            self.log.write(f"    reservation set: 0x{self.reserve_set_dict[hart_id] << 3:016X}\n")
            if self.reserve_set_dict[hart_id] == byte_addr >> 3: # doubleword addr granularity
                valid = True
        else:
            self.log.write(f"    reservation set: invalid\n")

        if valid:
            self.log.write(f"    reservation set check passed\n")
        else:
            self.log.write(f"    reservation set check failed\n")
            
        return valid

    def get_doubleword_list(self):
        doubleword_dict = dict()
        for byte_addr, byte_value in self.mem_dict.items():
            try:
                doubleword_dict[byte_addr >> 3][byte_addr & 0x7] = byte_value
            except KeyError:
                doubleword_dict[byte_addr >> 3] = [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
                doubleword_dict[byte_addr >> 3][byte_addr & 0x7] = byte_value

        doubleword_list = []
        for doubleword_addr, doubleword_value in doubleword_dict.items():
            if any(doubleword_value):
                doubleword_list.append((doubleword_addr, doubleword_value))

        return sorted(doubleword_list, key=lambda x: x[0])

    def print(self):
        doubleword_list = self.get_doubleword_list()

        print("\nMEM:")
        for doubleword_addr, doubleword_value in doubleword_list:
            doubleword_value_str = " ".join([f"{x:02X}" for x in doubleword_value])
            print(f"    0x{doubleword_addr << 3:016X}: {doubleword_value_str}")
        print()

    def write_mem_file(self, mem_file_path):
        with open(mem_file_path, "w") as fp:
            doubleword_list = self.get_doubleword_list()

            first = True
            ptr_doubleword_addr = -1
            for doubleword_addr, doubleword_value in doubleword_list:
                doubleword_value_str = " ".join([f"{x:02X}" for x in doubleword_value])
                if doubleword_addr != ptr_doubleword_addr:
                    if not first:
                        fp.write("\n")
                    else:
                        first = False
                    fp.write(f"@{doubleword_addr << 3:X}\n")
                    ptr_doubleword_addr = doubleword_addr
                fp.write(doubleword_value_str + "\n")
                ptr_doubleword_addr += 1

class Hart:
    def __init__(self, hart_id, start_pc, log, perf_counters, mem, trace):
        self.hart_id = hart_id
        self.pc = signed64(start_pc)
        self.arf = [0x0 for x in range(32)]
        self.farf = [np.float64(0) for x in range(32)]
        self.instret = 0
        self.log = log
        self.perf_counters = perf_counters
        self.mem = mem
        self.trace = trace

    def exec_instr(self):
        self.log.write(f"Hart {self.hart_id}: PC = 0x{self.pc:016X}:\n")

        # read instr
        instr = self.mem.read_instr(self.pc)
        opcode2 = bits(instr, 1, 0)

        # uncompressed
        if opcode2 == 0b11:
            self.log.write(f"    MEM[0x{self.pc:016X}] => 0x{instr:08X}: ")
            opcode5 = bits(instr, 6, 2)
            funct3 = bits(instr, 14, 12)
            funct7 = bits(instr, 31, 25)
            funct6 = bits(instr, 31, 26)
            rd = bits(instr, 11, 7)
            rs1 = bits(instr, 19, 15)
            rs2 = bits(instr, 24, 20)

            # LUI
            if opcode5 == 0b01101:
                imm20 = bits(instr, 31, 12)
                self.log.write(f"LUI x{rd}, 0x{imm20:05X}\n")
                result = signed64(imm20 << 12, size=32)
                self.write_arf(rd, result)
                self.incr_pc(4)
                self.perf_counters.incr("bru instr")

            # AUIPC
            elif opcode5 == 0b00101:
                imm20 = bits(instr, 31, 12)
                imm64 = signed64(imm20 << 12, size=32)
                self.log.write(f"AUIPC x{rd}, 0x{imm20:05X}\n")
                result = signed64(self.pc + imm64)
                self.write_arf(rd, result)
                self.incr_pc(4)
                self.perf_counters.incr("bru instr")

            # JAL
            elif opcode5 == 0b11011:
                imm21 = bit(instr, 31) << 20
                imm21 += bits(instr, 30, 21) << 1
                imm21 += bit(instr, 20) << 11
                imm21 += bits(instr, 19, 12) << 12
                imm64 = signed64(imm21, 21)
                self.log.write(f"JAL x{rd}, 0x{imm21:06X}\n")
                result = signed64(self.pc + 4)
                self.write_arf(rd, result)
                self.incr_pc(imm64)
                self.perf_counters.incr("bru instr")

            # JALR
            elif opcode5 == 0b11001:
                imm12 = bits(instr, 31, 20)
                imm64 = signed64(imm12, 12)
                self.log.write(f"JALR x{rd}, 0x{imm12:03X}(x{rs1})\n")
                result = signed64(self.pc + 4)
                npc = signed64(self.read_arf(rs1) + imm64)
                self.write_arf(rd, result)
                self.write_pc(npc)
                self.perf_counters.incr("bru instr")

            # B-Type
            elif opcode5 == 0b11000:
                imm13 = bit(instr, 31) << 12
                imm13 += bits(instr, 30, 25) << 5
                imm13 += bits(instr, 11, 8) << 1
                imm13 += bit(instr, 7) << 11
                imm64 = signed64(imm13, 13)
                
                # BEQ
                if funct3 == 0b000:
                    self.log.write(f"BEQ x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if self.read_arf(rs1) == self.read_arf(rs2):
                        self.incr_pc(imm64)
                    else:
                        self.incr_pc(4)
                    self.perf_counters.incr("bru instr")

                # BNE
                elif funct3 == 0b001:
                    self.log.write(f"BNE x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if self.read_arf(rs1) != self.read_arf(rs2):
                        self.incr_pc(imm64)
                    else:
                        self.incr_pc(4)
                    self.perf_counters.incr("bru instr")

                # BLT
                elif funct3 == 0b100:
                    self.log.write(f"BLT x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if make_signed(self.read_arf(rs1)) < make_signed(self.read_arf(rs2)):
                        self.incr_pc(imm64)
                    else:
                        self.incr_pc(4)
                    self.perf_counters.incr("bru instr")

                # BGE
                elif funct3 == 0b101:
                    self.log.write(f"BGE x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if make_signed(self.read_arf(rs1)) >= make_signed(self.read_arf(rs2)):
                        self.incr_pc(imm64)
                    else:
                        self.incr_pc(4)
                    self.perf_counters.incr("bru instr")

                # BLTU
                elif funct3 == 0b110:
                    self.log.write(f"BLTU x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if self.read_arf(rs1) < self.read_arf(rs2):
                        self.incr_pc(imm64)
                    else:
                        self.incr_pc(4)
                    self.perf_counters.incr("bru instr")

                # BGEU
                elif funct3 == 0b111:
                    self.log.write(f"BGEU x{rs1}, x{rs2}, 0x{imm13:04X}\n")
                    if self.read_arf(rs1) >= self.read_arf(rs2):
                        self.incr_pc(imm64)
                    else:
                        self.incr_pc(4)
                    self.perf_counters.incr("bru instr")

                else:
                    self.log.write(f"illegal B-Type instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False

            # L-Type
            elif opcode5 == 0b00000:
                imm12 = bits(instr, 31, 20)
                imm64 = signed64(imm12, 12)

                # LB
                if funct3 == 0b000:
                    self.log.write(f"LB x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = signed64(self.mem.read_data(addr, 1), 8)

                # LH
                elif funct3 == 0b001:
                    self.log.write(f"LH x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = signed64(self.mem.read_data(addr, 2), 16)

                # LW
                elif funct3 == 0b010:
                    self.log.write(f"LW x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = signed64(self.mem.read_data(addr, 4), 32)

                # LD
                elif funct3 == 0b011:
                    self.log.write(f"LD x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = self.mem.read_data(addr, 8)

                # LBU
                elif funct3 == 0b100:
                    self.log.write(f"LBU x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = self.mem.read_data(addr, 1)

                # LHU
                elif funct3 == 0b101:
                    self.log.write(f"LHU x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = self.mem.read_data(addr, 2)

                # LWU
                elif funct3 == 0b110:
                    self.log.write(f"LWU x{rd}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = self.mem.read_data(addr, 4)

                else:
                    self.log.write(f"illegal L-Type instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False

                self.write_arf(rd, value)
                self.incr_pc(4)
                self.perf_counters.incr("ldu instr")

            # S-Type
            elif opcode5 == 0b01000:
                imm12 = bits(instr, 11, 7)
                imm12 += bits(instr, 31, 25) << 5
                imm64 = signed64(imm12, 12)

                # SB
                if funct3 == 0b000:
                    self.log.write(f"SB x{rs2}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = self.read_arf(rs2)
                    self.mem.write_data(addr, value, 1)
                
                # SH
                elif funct3 == 0b001:
                    self.log.write(f"SH x{rs2}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = self.read_arf(rs2)
                    self.mem.write_data(addr, value, 2)

                # SW
                elif funct3 == 0b010:
                    self.log.write(f"SW x{rs2}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = self.read_arf(rs2)
                    self.mem.write_data(addr, value, 4)

                # SD
                elif funct3 == 0b011:
                    self.log.write(f"SD x{rs2}, 0x{imm12:03X}(x{rs1})\n")
                    addr = signed64(self.read_arf(rs1) + imm64)
                    value = self.read_arf(rs2)
                    self.mem.write_data(addr, value, 8)

                else:
                    self.log.write(f"illegal S-Type instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False

                self.incr_pc(4)
                self.perf_counters.incr("stamofu instr")

            # I-Type
            elif opcode5 == 0b00100:
                imm12 = bits(instr, 31, 20)
                imm64 = signed64(imm12, 12)
                shamt = bits(instr, 25, 20)

                # ADDI
                if funct3 == 0b000:
                    self.log.write(f"ADDI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed64(self.read_arf(rs1) + imm64)

                # SLLI
                elif funct3 == 0b001:
                    if funct6 == 0b000000:
                        self.log.write(f"SLLI x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = signed64(self.read_arf(rs1) << shamt)
                    else:
                        self.log.write(f"illegal I-Type instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                # SLTI
                elif funct3 == 0b010:
                    self.log.write(f"SLTI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    if make_signed(self.read_arf(rs1)) < make_signed(imm64):
                        result = 1
                    else:
                        result = 0

                # SLTIU
                elif funct3 == 0b011:
                    self.log.write(f"SLTIU x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    if self.read_arf(rs1) < imm64:
                        result = 1
                    else:
                        result = 0

                # XORI
                elif funct3 == 0b100:
                    self.log.write(f"XORI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed64(self.read_arf(rs1) ^ imm64)

                # SR*I
                elif funct3 == 0b101:
                        
                    # SRLI
                    if funct6 == 0b000000:
                        self.log.write(f"SRLI x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = self.read_arf(rs1) >> shamt

                    # SRAI
                    elif funct6 == 0b010000:
                        self.log.write(f"SRAI x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = signed64(self.read_arf(rs1) >> shamt, 64-shamt)

                    else:
                        self.log.write(f"illegal I-Type instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                # ORI
                elif funct3 == 0b110:
                    self.log.write(f"ORI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed64(self.read_arf(rs1) | imm64)

                # ANDI
                elif funct3 == 0b111:
                    self.log.write(f"ANDI x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed64(self.read_arf(rs1) & imm64)

                else:
                    self.log.write(f"illegal I-Type instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False

                self.write_arf(rd, result)
                self.incr_pc(4)
                self.perf_counters.incr("alu_imm instr")

            # IW-Type
            elif opcode5 == 0b00100:
                imm12 = bits(instr, 31, 20)
                imm32 = signed32(imm12, 12)
                shamt = bits(instr, 24, 20)

                # ADDIW
                if funct3 == 0b000:
                    self.log.write(f"ADDIW x{rd}, x{rs1}, 0x{imm12:03X}\n")
                    result = signed64(signed32(self.read_arf(rs1)) + imm32, 32)

                # SLLIW
                elif funct3 == 0b001:
                    if funct6 == 0b0000000:
                        self.log.write(f"SLLIW x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = signed64(signed32(self.read_arf(rs1)) << shamt, 32)
                    else:
                        self.log.write(f"illegal I-Type instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                # SR*IW
                elif funct3 == 0b101:
                        
                    # SRLIW
                    if funct6 == 0b000000:
                        self.log.write(f"SRLIW x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = signed64(signed32(self.read_arf(rs1)) >> shamt, 32)

                    # SRAIW
                    elif funct6 == 0b010000:
                        self.log.write(f"SRAIW x{rd}, x{rs1}, 0x{shamt:02X}\n")
                        result = signed64(signed32(self.read_arf(rs1)) >> shamt, 32-shamt)

                    else:
                        self.log.write(f"illegal I-Type instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                else:
                    self.log.write(f"illegal IW-Type instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False

                self.write_arf(rd, result)
                self.incr_pc(4)
                self.perf_counters.incr("alu_imm instr")

            # R-Type and M-Ext
            elif opcode5 == 0b01100:

                # R-Type
                if funct7 == 0b0000000 or funct7 == 0b0100000:

                    # ADD/SUB
                    if funct3 == 0b000:

                        # ADD
                        if funct7 == 0b0000000:
                            self.log.write(f"ADD x{rd}, x{rs1}, x{rs2}\n")
                            result = signed64(self.read_arf(rs1) + self.read_arf(rs2))

                        # SUB
                        elif funct7 == 0b0100000:
                            self.log.write(f"SUB x{rd}, x{rs1}, x{rs2}\n")
                            result = signed64(self.read_arf(rs1) - self.read_arf(rs2))

                        else:
                            self.log.write(f"illegal R-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False

                    # SLL
                    elif funct3 == 0b001:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        self.log.write(f"SLL x{rd}, x{rs1}, x{rs2}\n")
                        shamt = bits(self.read_arf(rs2), 5, 0)
                        self.log.write(f"    shamt = {shamt}\n")
                        result = signed64(self.read_arf(rs1) << shamt)

                    # SLT
                    elif funct3 == 0b010:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
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
                            self.log.write(f"\n< Exiting Execution >\n")
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
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        self.log.write(f"XOR x{rd}, x{rs1}, x{rs2}\n")
                        result = signed64(self.read_arf(rs1) ^ self.read_arf(rs2))

                    # SR*
                    elif funct3 == 0b101:

                        # SRL
                        if funct7 == 0b0000000:
                            self.log.write(f"SRL x{rd}, x{rs1}, x{rs2}\n")
                            shamt = bits(self.read_arf(rs2), 5, 0)
                            self.log.write(f"    shamt = {shamt}\n")
                            result = self.read_arf(rs1) >> shamt

                        # SRA
                        elif funct7 == 0b0100000:
                            self.log.write(f"SRA x{rd}, x{rs1}, x{rs2}\n")
                            shamt = bits(self.read_arf(rs2), 5, 0)
                            self.log.write(f"    shamt = {shamt}\n")
                            result = signed64(self.read_arf(rs1) >> shamt, 64-shamt)

                        else:
                            self.log.write(f"illegal R-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        
                    # OR
                    elif funct3 == 0b110:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        self.log.write(f"OR x{rd}, x{rs1}, x{rs2}\n")
                        result = signed64(self.read_arf(rs1) | self.read_arf(rs2))
                        
                    # AND
                    elif funct3 == 0b111:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal R-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        self.log.write(f"AND x{rd}, x{rs1}, x{rs2}\n")
                        result = signed64(self.read_arf(rs1) & self.read_arf(rs2))

                    else:
                        self.log.write(f"illegal R-Type instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                    self.perf_counters.incr("alu_reg instr")
                    
                # M-Ext
                elif funct7 == 0b0000001:

                    # MUL
                    if funct3 == 0b000:
                        self.log.write(f"MUL x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        result = signed64(R_rs1 * R_rs2)
                    
                    # MULH
                    elif funct3 == 0b001:
                        self.log.write(f"MULH x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        result = signed64((make_signed(R_rs1) * make_signed(R_rs2)) >> 64)

                    # MULHSU
                    elif funct3 == 0b010:
                        self.log.write(f"MULHSU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        result = signed64((make_signed(R_rs1) * R_rs2) >> 64)

                    # MULHU
                    elif funct3 == 0b011:
                        self.log.write(f"MULHU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        result = signed64((R_rs1 * R_rs2) >> 64)

                    # DIV
                    elif funct3 == 0b100:
                        self.log.write(f"DIV x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs2 == 0:
                            result = 0xFFFFFFFF_FFFFFFFF
                        # elif R_rs1 == 0x80000000 and R_rs2 == 0xFFFFFFFF:
                        #     result = 0x80000000
                            # default case handles this overflow, get 0x80000000 regardless
                        else:
                            result = signed64(int(make_signed(R_rs1) / make_signed(R_rs2)))

                    # DIVU
                    elif funct3 == 0b101:
                        self.log.write(f"DIVU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs2 == 0:
                            result = 0xFFFFFFFF_FFFFFFFF
                        else:
                            result = signed64(R_rs1 // R_rs2)

                    # REM
                    elif funct3 == 0b110:
                        self.log.write(f"REM x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs2 == 0:
                            result = R_rs1
                        else:
                            quotient = int(make_signed(R_rs1) / make_signed(R_rs2)) # round towards 0
                            result = signed64(make_signed(R_rs1) - (quotient * make_signed(R_rs2)))

                    # REMU
                    elif funct3 == 0b111:
                        self.log.write(f"REMU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs2 == 0:
                            result = R_rs1
                        else:
                            result = signed64(R_rs1 % R_rs2)

                    else:
                        self.log.write(f"illegal M-Type instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                    self.perf_counters.incr("mdu instr")

                else:
                    self.log.write(f"illegal R-Type / M-Ext instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False

                self.write_arf(rd, result)
                self.incr_pc(4)

            # RW-Type and MW-Type
            elif opcode5 == 0b01110:

                # RW-Type
                if funct7 == 0b0000000 or funct7 == 0b0100000:

                    # ADDW/SUBW
                    if funct3 == 0b000:

                        # ADDW
                        if funct7 == 0b0000000:
                            self.log.write(f"ADDW x{rd}, x{rs1}, x{rs2}\n")
                            result = signed64(signed32(self.read_arf(rs1)) + signed32(self.read_arf(rs2)), 32)

                        # SUBW
                        elif funct7 == 0b0100000:
                            self.log.write(f"SUBW x{rd}, x{rs1}, x{rs2}\n")
                            result = signed64(signed32(self.read_arf(rs1)) - signed32(self.read_arf(rs2)), 32)

                        else:
                            self.log.write(f"illegal RW-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False

                    # SLLW
                    elif funct3 == 0b001:
                        if funct7 != 0b0000000:
                            self.log.write(f"illegal RW-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        self.log.write(f"SLLW x{rd}, x{rs1}, x{rs2}\n")
                        shamt = bits(self.read_arf(rs2), 4, 0)
                        self.log.write(f"    shamt = {shamt}\n")
                        result = signed64(signed32(self.read_arf(rs1)) << shamt, 32)

                    # SR*W
                    elif funct3 == 0b101:

                        # SRLW
                        if funct7 == 0b0000000:
                            self.log.write(f"SRLW x{rd}, x{rs1}, x{rs2}\n")
                            shamt = bits(self.read_arf(rs2), 4, 0)
                            self.log.write(f"    shamt = {shamt}\n")
                            result = signed64(signed32(self.read_arf(rs1)) >> shamt, 32)

                        # SRAW
                        elif funct7 == 0b0100000:
                            self.log.write(f"SRAW x{rd}, x{rs1}, x{rs2}\n")
                            shamt = bits(self.read_arf(rs2), 4, 0)
                            self.log.write(f"    shamt = {shamt}\n")
                            result = signed64(signed32(self.read_arf(rs1)) >> shamt, 32-shamt)

                        else:
                            self.log.write(f"illegal RW-Type instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False

                    else:
                        self.log.write(f"illegal RW-Type instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                    self.perf_counters.incr("alu_reg instr")
                    
                # M-Ext
                elif funct7 == 0b0000001:

                    # MULW
                    if funct3 == 0b000:
                        self.log.write(f"MULW x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = signed32(self.read_arf(rs1))
                        R_rs2 = signed32(self.read_arf(rs2))
                        result = signed64(R_rs1 * R_rs2, 32)

                    # DIVW
                    elif funct3 == 0b100:
                        self.log.write(f"DIVW x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = signed32(self.read_arf(rs1))
                        R_rs2 = signed32(self.read_arf(rs2))
                        if R_rs2 == 0:
                            result = 0xFFFFFFFF_FFFFFFFF
                        # elif R_rs1 == 0x80000000 and R_rs2 == 0xFFFFFFFF:
                        #     result = 0x80000000
                            # default case handles this overflow, get 0x80000000 regardless
                        else:
                            result = signed64(int(make_signed(R_rs1, 32) / make_signed(R_rs2, 32)), 32)

                    # DIVU
                    elif funct3 == 0b101:
                        self.log.write(f"DIVU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = signed32(self.read_arf(rs1))
                        R_rs2 = signed32(self.read_arf(rs2))
                        if R_rs2 == 0:
                            result = 0xFFFFFFFF_FFFFFFFF
                        else:
                            result = signed64(R_rs1 // R_rs2, 32)

                    # REM
                    elif funct3 == 0b110:
                        self.log.write(f"REM x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = signed32(self.read_arf(rs1))
                        R_rs2 = signed32(self.read_arf(rs2))
                        if R_rs2 == 0:
                            result = R_rs1
                        else:
                            quotient = int(make_signed(R_rs1, 32) / make_signed(R_rs2, 32)) # round towards 0
                            result = signed64(make_signed(R_rs1, 32) - (quotient * make_signed(R_rs2, 32)), 32)

                    # REMU
                    elif funct3 == 0b111:
                        self.log.write(f"REMU x{rd}, x{rs1}, x{rs2}\n")
                        R_rs1 = signed32(self.read_arf(rs1))
                        R_rs2 = signed32(self.read_arf(rs2))
                        if R_rs2 == 0:
                            result = R_rs1
                        else:
                            result = signed64(R_rs1 % R_rs2, 32)

                    else:
                        self.log.write(f"illegal MW-Type instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                    self.perf_counters.incr("mdu instr")

                else:
                    self.log.write(f"illegal RW-Type / MW-Ext instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
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
                        self.log.write(f"\n< Exiting Execution >\n")
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
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False

                self.incr_pc(4)
                self.perf_counters.incr("stamofu instr")

            # SYS
            elif opcode5 == 0b11100:

                # privilege switchers
                if funct3 == 0b000:

                    # E*
                    if funct7 == 0:

                        # ECALL
                        if rs2 == 0b00000:
                            self.log.write(f"ECALL\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            self.perf_counters.incr("sysu instr")
                            return False
                        
                        # EBREAK
                        elif rs2 == 0b00001:
                            self.log.write(f"EBREAK\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            self.perf_counters.incr("sysu instr")
                            return False
                    
                        else:
                            self.log.write(f"illegal SYS instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        
                    # MRET
                    elif funct7 == 0b0011000:

                        if rs2 == 0b00010:
                            self.log.write(f"MRET\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            self.perf_counters.incr("sysu instr")
                            return False
                    
                        else:
                            self.log.write(f"illegal SYS instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        
                    # WFI/SRET
                    elif funct7 == 0b0001000:

                        # WFI
                        if rs2 == 0b00101:
                            self.log.write(f"WFI\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            self.perf_counters.incr("sysu instr")
                            return False
                        
                        # SRET
                        elif rs2 == 0b00010:
                            self.log.write(f"SRET\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            self.perf_counters.incr("sysu instr")
                            return False
                    
                        else:
                            self.log.write(f"illegal SYS instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        
                    # SFENCE.VMA
                    elif funct7 == 0b0001001:
                        self.log.write(f"SFENCE.VMA x{rs1}, x{rs2}")
                        self.log.write(f"\n< Exiting Execution >\n")
                        self.perf_counters.incr("stamofu instr")
                        return False
                    
                # CSR
                else:
                    csr = bits(instr, 31, 20)
                    uimm = rs1
                    
                    # CSRRW
                    if funct3 == 0b001:
                        self.log.write(f"CSRRW x{rd}, 0x{csr:03X}, x{rs1}\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        self.perf_counters.incr("sysu instr")
                        return False
                        
                    # CSRRS
                    elif funct3 == 0b010:
                        self.log.write(f"CSRRS x{rd}, 0x{csr:03X}, x{rs1}\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        self.perf_counters.incr("sysu instr")
                        return False
                        
                    # CSRRC
                    elif funct3 == 0b011:
                        self.log.write(f"CSRRC x{rd}, 0x{csr:03X}, x{rs1}\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        self.perf_counters.incr("sysu instr")
                        return False
                        
                    # CSRRWI
                    elif funct3 == 0b101:
                        self.log.write(f"CSRRWI x{rd}, 0x{csr:03X}, 0x{uimm:02X}\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        self.perf_counters.incr("sysu instr")
                        return False
                        
                    # CSRRSI
                    elif funct3 == 0b110:
                        self.log.write(f"CSRRSI x{rd}, 0x{csr:03X}, 0x{uimm:02X}\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        self.perf_counters.incr("sysu instr")
                        return False
                        
                    # CSRRCI
                    elif funct3 == 0b111:
                        self.log.write(f"CSRRCI x{rd}, 0x{csr:03X}, 0x{uimm:02X}\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        self.perf_counters.incr("sysu instr")
                        return False
                
                    else:
                        self.log.write(f"illegal SYS instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
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

                # {LR,SC,AMO*}.W
                if funct3 == 0b010:

                    # LR.W
                    if funct5 == 0b00010:
                        self.log.write(f"LR.W{aqrl_str} x{rd}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        self.mem.reserve_set(self.hart_id, R_rs1)
                        read_value = signed64(self.mem.read_data(R_rs1, 4), 32)

                    # SC.W
                    elif funct5 == 0b00011:
                        self.log.write(f"SC.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 4 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        if self.mem.check_reserve_set(self.hart_id, R_rs1):
                            self.mem.write_data(R_rs1, signed32(R_rs2), 4)
                            read_value = 0
                        else:
                            read_value = 1

                    # AMO*.W
                    else:
                        # AMOSWAP.W
                        if funct5 == 0b00001:
                            self.log.write(f"AMOSWAP.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            write_value = signed32(R_rs2)
                            self.mem.write_data(R_rs1, write_value, 4)

                        # AMOADD.W
                        elif funct5 == 0b00000:
                            self.log.write(f"AMOADD.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            write_value = signed32(signed32(read_value) + signed32(R_rs2))
                            self.mem.write_data(R_rs1, write_value, 4)

                        # AMOXOR.W
                        elif funct5 == 0b00100:
                            self.log.write(f"AMOXOR.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            write_value = signed32(signed32(read_value) ^ signed32(R_rs2))
                            self.mem.write_data(R_rs1, write_value, 4)

                        # AMOAND.W
                        elif funct5 == 0b01100:
                            self.log.write(f"AMOAND.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            write_value = signed32(signed32(read_value) & signed32(R_rs2))
                            self.mem.write_data(R_rs1, write_value, 4)

                        # AMOOR.W
                        elif funct5 == 0b01000:
                            self.log.write(f"AMOOR.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            write_value = signed32(signed32(read_value) | signed32(R_rs2))
                            self.mem.write_data(R_rs1, write_value, 4)

                        # AMOMIN.W
                        elif funct5 == 0b10000:
                            self.log.write(f"AMOMIN.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            if make_signed(R_rs2, 32) < make_signed(read_value, 32):
                                write_value = signed32(R_rs2)
                            else:
                                write_value = signed32(read_value)
                            self.mem.write_data(R_rs1, write_value, 4)

                        # AMOMAX.W
                        elif funct5 == 0b10100:
                            self.log.write(f"AMOMAX.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            if make_signed(R_rs2, 32) > make_signed(read_value, 32):
                                write_value = signed32(R_rs2)
                            else:
                                write_value = signed32(read_value)
                            self.mem.write_data(R_rs1, write_value, 4)

                        # AMOMINU.W
                        elif funct5 == 0b11000:
                            self.log.write(f"AMOMINU.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            if signed32(R_rs2) < signed32(read_value):
                                write_value = signed32(R_rs2)
                            else:
                                write_value = signed32(read_value)
                            self.mem.write_data(R_rs1, write_value, 4)

                        # AMOMAXU.W
                        elif funct5 == 0b11100:
                            self.log.write(f"AMOMAXU.W{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 4 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 4), 32)
                            if signed32(R_rs2) > signed32(read_value):
                                write_value = signed32(R_rs2)
                            else:
                                write_value = signed32(read_value)
                            self.mem.write_data(R_rs1, write_value, 4)

                        else:
                            self.log.write(f"illegal A-Ext instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False

                # {LR,SC,AMO*}.D
                elif funct3 == 0b011:

                    # LR.D
                    if funct5 == 0b00010:
                        self.log.write(f"LR.D{aqrl_str} x{rd}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        if R_rs1 % 8 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        self.mem.reserve_set(self.hart_id, R_rs1)
                        read_value = signed64(self.mem.read_data(R_rs1, 8))

                    # SC.D
                    elif funct5 == 0b00011:
                        self.log.write(f"SC.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                        R_rs1 = self.read_arf(rs1)
                        R_rs2 = self.read_arf(rs2)
                        if R_rs1 % 8 != 0:
                            self.log.write(f"misaligned AMO\n")
                            self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False
                        if self.mem.check_reserve_set(self.hart_id, R_rs1):
                            self.mem.write_data(R_rs1, signed64(R_rs2), 8)
                            read_value = 0
                        else:
                            read_value = 1

                    # AMO*.D
                    else:
                        # AMOSWAP.W
                        if funct5 == 0b00001:
                            self.log.write(f"AMOSWAP.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            write_value = signed64(R_rs2)
                            self.mem.write_data(R_rs1, write_value, 8)

                        # AMOADD.D
                        elif funct5 == 0b00000:
                            self.log.write(f"AMOADD.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            write_value = signed64(signed64(read_value) + signed64(R_rs2))
                            self.mem.write_data(R_rs1, write_value, 8)

                        # AMOXOR.D
                        elif funct5 == 0b00100:
                            self.log.write(f"AMOXOR.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            write_value = signed64(signed64(read_value) ^ signed64(R_rs2))
                            self.mem.write_data(R_rs1, write_value, 8)

                        # AMOAND.D
                        elif funct5 == 0b01100:
                            self.log.write(f"AMOAND.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            write_value = signed64(signed64(read_value) & signed64(R_rs2))
                            self.mem.write_data(R_rs1, write_value, 8)

                        # AMOOR.D
                        elif funct5 == 0b01000:
                            self.log.write(f"AMOOR.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            write_value = signed64(signed64(read_value) | signed64(R_rs2))
                            self.mem.write_data(R_rs1, write_value, 8)

                        # AMOMIN.D
                        elif funct5 == 0b10000:
                            self.log.write(f"AMOMIN.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            if make_signed(R_rs2) < make_signed(read_value):
                                write_value = signed64(R_rs2)
                            else:
                                write_value = signed64(read_value)
                            self.mem.write_data(R_rs1, write_value, 8)

                        # AMOMAX.D
                        elif funct5 == 0b10100:
                            self.log.write(f"AMOMAX.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            if make_signed(R_rs2) > make_signed(read_value):
                                write_value = signed64(R_rs2)
                            else:
                                write_value = signed64(read_value)
                            self.mem.write_data(R_rs1, write_value, 8)

                        # AMOMINU.D
                        elif funct5 == 0b11000:
                            self.log.write(f"AMOMINU.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            if signed64(R_rs2) < signed64(read_value):
                                write_value = signed64(R_rs2)
                            else:
                                write_value = signed64(read_value)
                            self.mem.write_data(R_rs1, write_value, 8)

                        # AMOMAXU.D
                        elif funct5 == 0b11100:
                            self.log.write(f"AMOMAXU.D{aqrl_str} x{rd}, x{rs2}, (x{rs1})\n")
                            R_rs1 = self.read_arf(rs1)
                            R_rs2 = self.read_arf(rs2)
                            if R_rs1 % 8 != 0:
                                self.log.write(f"misaligned AMO\n")
                                self.log.write(f"    addr = 0x{R_rs1:08X}\n")
                                self.log.write(f"\n< Exiting Execution >\n")
                                return False
                            read_value = signed64(self.mem.read_data(R_rs1, 8))
                            if signed64(R_rs2) > signed64(read_value):
                                write_value = signed64(R_rs2)
                            else:
                                write_value = signed64(read_value)
                            self.mem.write_data(R_rs1, write_value, 8)

                        else:
                            self.log.write(f"illegal A-Ext instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False

                else:
                    self.log.write(f"illegal A-Ext instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False
                
                self.write_arf(rd, read_value)
                self.incr_pc(4)
                self.perf_counters.incr("stamofu instr")

            else:
                self.log.write(f"illegal uncompressed instr\n")
                self.log.write(f"\n< Exiting Execution >\n")
                return False

        # compressed
        else:
            instr = bits(instr, 15, 0)
            self.log.write(f"    MEM[0x{self.pc:016X}] => 0x{instr:04X}: ")
            opcode3 = bits(instr, 15, 13)

            if opcode2 == 0b00:

                # C.ADDI4SPN
                if opcode3 == 0b000:
                    uimm = bits(instr, 12, 11) << 4
                    uimm += bits(instr, 10, 7) << 6
                    uimm += bit(instr, 6) << 2
                    uimm += bit(instr, 5) << 3
                    if uimm == 0:
                        self.log.write(f"illegal all 0's instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False
                    rd = bits(instr, 4, 2) + 8
                    self.log.write(f"C.ADDI4SPN x{rd}, 0x{uimm:03X}\n")
                    value = signed32(self.read_arf(2) + uimm)
                    self.write_arf(rd, value)
                    self.incr_pc(2)
                    self.perf_counters.incr("alu_imm instr")

                # C.LW
                elif opcode3 == 0b010:
                    uimm = bits(instr, 12, 10) << 3
                    uimm += bit(instr, 6) << 2
                    uimm += bit(instr, 5) << 6
                    rs1 = bits(instr, 9, 7) + 8
                    rd = bits(instr, 4, 2) + 8
                    self.log.write(f"C.LW x{rd}, 0x{uimm:02X}\n")
                    addr = signed32(self.read_arf(rs1) + uimm)
                    value = self.mem.read_data(addr, 4)
                    self.write_arf(rd, value)
                    self.incr_pc(2)
                    self.perf_counters.incr("ldu instr")

                # C.SW
                elif opcode3 == 0b110:
                    uimm = bits(instr, 12, 10) << 3
                    uimm += bit(instr, 6) << 2
                    uimm += bit(instr, 5) << 6
                    rs1 = bits(instr, 9, 7) + 8
                    rs2 = bits(instr, 4, 2) + 8
                    self.log.write(f"C.SW x{rs2}, 0x{uimm:02X}\n")
                    addr = signed32(self.read_arf(rs1) + uimm)
                    self.mem.write_data(addr, self.read_arf(rs2), 4)
                    self.incr_pc(2)
                    self.perf_counters.incr("stamofu instr")

                else:
                    self.log.write(f"illegal compressed instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False
            
            elif opcode2 == 0b01:
                
                # C.NOP/C.ADDI
                if opcode3 == 0b000:
                    imm = bit(instr, 12) << 5
                    imm += bits(instr, 6, 2)
                    imm32 = signed32(imm, 6)
                    rd = bits(instr, 11, 7)
                    self.log.write(f"C.ADDI x{rd}, 0x{imm:02X}\n")
                    result = signed32(self.read_arf(rd) + imm32)
                    self.write_arf(rd, result)
                    self.incr_pc(2)
                    self.perf_counters.incr("alu_imm instr")

                # C.JAL
                elif opcode3 == 0b001:
                    imm = bit(instr, 12) << 11
                    imm += bit(instr, 11) << 4
                    imm += bits(instr, 10, 9) << 8
                    imm += bit(instr, 8) << 10
                    imm += bit(instr, 7) << 6
                    imm += bit(instr, 6) << 7
                    imm += bits(instr, 5, 3) << 1
                    imm += bit(instr, 2) << 5
                    imm32 = signed32(imm, 12)
                    self.log.write(f"C.JAL 0x{imm:03X}\n")
                    result = signed32(self.pc + 2)
                    self.write_arf(1, result)
                    self.incr_pc(imm32)
                    self.perf_counters.incr("bru instr")

                # C.LI
                elif opcode3 == 0b010:
                    imm = bit(instr, 12) << 5
                    imm += bits(instr, 6, 2)
                    imm32 = signed32(imm, 6)
                    rd = bits(instr, 11, 7)
                    self.log.write(f"C.LI x{rd}, 0x{imm:02X}\n")
                    result = imm32
                    self.write_arf(rd, result)
                    self.incr_pc(2)
                    self.perf_counters.incr("alu_imm instr")

                # C.ADDI16SP/C.LUI
                elif opcode3 == 0b011:

                    # C.ADDI16SP
                    if bits(instr, 11, 7) == 2:
                        imm = bit(instr, 12) << 9
                        imm += bit(instr, 6) << 4
                        imm += bit(instr, 5) << 6
                        imm += bits(instr, 4, 3) << 7
                        imm += bit(instr, 2) << 5
                        imm32 = signed32(imm, 10)
                        self.log.write(f"C.ADDI16SP 0x{imm:03X}\n")
                        result = signed32(self.read_arf(2) + imm32)
                        self.write_arf(2, result)
                        self.perf_counters.incr("alu_imm instr")

                    # C.LUI
                    else:
                        imm = bit(instr, 12) << 17
                        imm += bits(instr, 6, 2) << 12
                        imm32 = signed32(imm, 18)
                        rd = bits(instr, 11, 7)
                        self.log.write(f"C.LUI x{rd}, 0x{imm >> 12:02X}\n")
                        result = imm32
                        self.write_arf(rd, result)
                        self.perf_counters.incr("bru instr")

                    self.incr_pc(2)

                # C.SRLI/C.SRAI/C.ANDI/C.SUB/C.XOR/C.OR/C.AND
                elif opcode3 == 0b100:
                    funct2 = bits(instr, 11, 10)
                    rd = bits(instr, 9, 7) + 8

                    # C.SRLI
                    if funct2 == 0b00:
                        shamt = bits(instr, 6, 2)
                        self.log.write(f"C.SRLI x{rd}, 0x{shamt:02X}\n")
                        result = signed32(self.read_arf(rd) >> shamt)
                        self.perf_counters.incr("alu_imm instr")

                    # C.SRAI
                    elif funct2 == 0b01:
                        shamt = bits(instr, 6, 2)
                        self.log.write(f"C.SRAI x{rd}, 0x{shamt:02X}\n")
                        result = signed32(self.read_arf(rd) >> shamt, 32-shamt)
                        self.perf_counters.incr("alu_imm instr")

                    # C.ANDI
                    elif funct2 == 0b10:
                        imm = bit(instr, 12) << 5
                        imm += bits(instr, 6, 2)
                        imm32 = signed32(imm, 6)
                        self.log.write(f"C.ANDI x{rd}, 0x{imm:02X}\n")
                        result = signed32(self.read_arf(rd) & imm32)
                        self.perf_counters.incr("alu_imm instr")

                    # C.SUB/C.XOR/C.OR/C.AND
                    elif funct2 == 0b11:
                        funct2_2 = bits(instr, 6, 5)
                        rs2 = bits(instr, 4, 2) + 8
                        
                        # C.SUB
                        if funct2_2 == 0b00:
                            self.log.write(f"C.SUB x{rd}, x{rs2}\n")
                            result = signed32(self.read_arf(rd) - self.read_arf(rs2))

                        # C.XOR
                        elif funct2_2 == 0b01:
                            self.log.write(f"C.XOR x{rd}, x{rs2}\n")
                            result = signed32(self.read_arf(rd) ^ self.read_arf(rs2))

                        # C.OR
                        elif funct2_2 == 0b10:
                            self.log.write(f"C.OR x{rd}, x{rs2}\n")
                            result = signed32(self.read_arf(rd) | self.read_arf(rs2))

                        # C.AND
                        elif funct2_2 == 0b11:
                            self.log.write(f"C.AND x{rd}, x{rs2}\n")
                            result = signed32(self.read_arf(rd) & self.read_arf(rs2))

                        else:
                            self.log.write(f"illegal compressed instr\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            return False

                        self.perf_counters.incr("alu_reg instr")

                    else:
                        self.log.write(f"illegal compressed instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False

                    self.write_arf(rd, result)
                    self.incr_pc(2)

                # C.J
                elif opcode3 == 0b101:
                    imm = bit(instr, 12) << 11
                    imm += bit(instr, 11) << 4
                    imm += bits(instr, 10, 9) << 8
                    imm += bit(instr, 8) << 10
                    imm += bit(instr, 7) << 6
                    imm += bit(instr, 6) << 7
                    imm += bits(instr, 5, 3) << 1
                    imm += bit(instr, 2) << 5
                    imm32 = signed32(imm, 12)
                    self.log.write(f"C.J 0x{imm:03X}\n")
                    self.incr_pc(imm32)
                    self.perf_counters.incr("bru instr")
                
                # C.BEQZ
                elif opcode3 == 0b110:
                    imm = bit(instr, 12) << 8
                    imm += bits(instr, 11, 10) << 3
                    imm += bits(instr, 6, 5) << 6
                    imm += bits(instr, 4, 3) << 1
                    imm += bit(instr, 2) << 5
                    imm32 = signed32(imm, 9)
                    rs1 = bits(instr, 9, 7) + 8
                    self.log.write(f"C.BEQZ x{rs1}, 0x{imm:03X}\n")
                    if self.read_arf(rs1) == 0:
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(2)
                    self.perf_counters.incr("bru instr")

                # C.BNEZ
                elif opcode3 == 0b111:
                    imm = bit(instr, 12) << 8
                    imm += bits(instr, 11, 10) << 3
                    imm += bits(instr, 6, 5) << 6
                    imm += bits(instr, 4, 3) << 1
                    imm += bit(instr, 2) << 5
                    imm32 = signed32(imm, 9)
                    rs1 = bits(instr, 9, 7) + 8
                    self.log.write(f"C.BNEZ x{rs1}, 0x{imm:03X}\n")
                    if self.read_arf(rs1) != 0:
                        self.incr_pc(imm32)
                    else:
                        self.incr_pc(2)
                    self.perf_counters.incr("bru instr")

                else:
                    self.log.write(f"illegal compressed instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False

            elif opcode2 == 0b10:

                # C.SLLI
                if opcode3 == 0b000:
                    shamt = bits(instr, 6, 2)
                    rd = bits(instr, 11, 7)
                    self.log.write(f"C.SLLI x{rd}, 0x{shamt:02X}\n")
                    result = signed32(self.read_arf(rd) << shamt)
                    self.write_arf(rd, result)
                    self.incr_pc(2)
                    self.perf_counters.incr("alu_imm instr")

                # C.LWSP
                elif opcode3 == 0b010:
                    uimm = bit(instr, 12) << 5
                    uimm += bits(instr, 6, 4) << 2
                    uimm += bits(instr, 3, 2) << 6
                    rd = bits(instr, 11, 7)
                    self.log.write(f"C.LWSP x{rd}, 0x{uimm:02X}\n")
                    addr = signed32(self.read_arf(2) + uimm)
                    result = self.mem.read_data(addr, 4)
                    self.write_arf(rd, result)
                    self.incr_pc(2)
                    self.perf_counters.incr("ldu instr")

                # C.JR/C.MV/C.EBREAK/C.JALR/C.ADD
                elif opcode3 == 0b100:
                    rd_rs1 = bits(instr, 11, 7)
                    rs2 = bits(instr, 6, 2)

                    # C.JR/C.MV
                    if bit(instr, 12) == 0b0:

                        # C.JR
                        if rs2 == 0:
                            self.log.write(f"C.JR x{rd_rs1}\n")
                            npc = self.read_arf(rd_rs1)
                            self.write_pc(npc)
                            self.perf_counters.incr("bru instr")

                        # C.MV:
                        else:
                            self.log.write(f"C.MV x{rd_rs1}, x{rs2}\n")
                            self.write_arf(rd_rs1, self.read_arf(rs2))
                            self.incr_pc(2)
                            self.perf_counters.incr("alu_reg instr")

                    # C.EBREAK/C.JALR/C.ADD
                    elif bit(instr, 12) == 0b1:

                        # C.EBREAK
                        if rd_rs1 == 0 and rs2 == 0:
                            self.log.write(f"C.EBREAK\n")
                            self.log.write(f"\n< Exiting Execution >\n")
                            self.perf_counters.incr("sysu instr")
                            return False

                        # C.JALR
                        elif rs2 == 0:
                            self.log.write(f"C.JALR\n")
                            result = signed32(self.pc + 2)
                            self.write_arf(1, result)
                            self.write_pc(self.read_arf(rd_rs1))
                            self.perf_counters.incr("bru instr")

                        # C.ADD
                        else:
                            self.log.write(f"C.ADD\n")
                            result = signed32(self.read_arf(rd_rs1) + self.read_arf(rs2))
                            self.write_arf(rd_rs1, result)
                            self.incr_pc(2)
                            self.perf_counters.incr("alu_reg instr")

                    else:
                        self.log.write(f"illegal compressed instr\n")
                        self.log.write(f"\n< Exiting Execution >\n")
                        return False
                    
                # C.SWSP
                elif opcode3 == 0b110:
                    uimm = bits(instr, 12, 9) << 2
                    uimm += bits(instr, 8, 7) << 6
                    rs2 = bits(instr, 6, 2)
                    self.log.write(f"C.SWSP x{rs2}, 0x{uimm:02X}\n")
                    addr = signed32(self.read_arf(2) + uimm)
                    result = self.read_arf(rs2)
                    self.mem.write_data(addr, result, 4)
                    self.incr_pc(2)
                    self.perf_counters.incr("stamofu instr")
                
                else:
                    self.log.write(f"illegal compressed instr\n")
                    self.log.write(f"\n< Exiting Execution >\n")
                    return False
                
            else:
                self.log.write(f"illegal compressed instr\n")
                self.log.write(f"\n< Exiting Execution >\n")
                return False

        self.instret += 1
        self.perf_counters.incr("any instr")
        if self.trace:
            self.log.print()
        return True
    
    def read_arf(self, rs):
        self.log.write(f"    ARF[x{rs}] => 0x{self.arf[rs]:016X}\n")
        return self.arf[rs]

    def read_farf(self, frs):
        self.log.write(f"    FARF[f{frs}] => {self.farf[rs]}\n")
        return self.farf[frs]
    
    def write_arf(self, dest, value):
        if dest == 0:
            self.log.write(f"    ARF[x0] => 0x00000000_00000000 <=/= 0x{value:016X}\n")
        else:
            self.log.write(f"    ARF[x{dest}] <= 0x{value:016X}\n")
            self.arf[dest] = value

    def write_farf(self, dest, value):
        self.log.write(f"    FARF[f{dest}] <= {value}\n")
        self.farf[dest] = value

    def write_pc(self, value):
        self.log.write(f"    PC <= 0x{value:016X}\n")
        self.pc = signed64(value)
    
    def incr_pc(self, incr):
        self.write_pc(signed64(self.pc + incr))

    def print(self):
        print(f"Hart {self.hart_id}:")
        print(f"    PC = 0x{self.pc:016X}")
        print(f"    instret = {self.instret}")
        print(f"    ARF:")
        for ar, value in enumerate(self.arf):
            print(f"        x{ar:2d}: 0x{value:016X}")
        print(f"    FARF:")
        for far, value in enumerate(self.farf):
            print(f"        f{far:2d}: {value}")

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
    perf_counters = PerfCounters()
    mem = Mem(args.input_mem_file_path, log)
    hart = Hart(0, args.start_pc, log, perf_counters, mem, not args.silent)

    if not args.silent:
        mem.print()

    try:
        # execute program
        while hart.exec_instr():
            continue
    
    except KeyboardInterrupt:
        log.write(f"\nUser Stopped Execution Early\n")

    if not args.silent:
        log.print()
        hart.print()
        mem.print()
        perf_counters.print()

    mem.write_mem_file(args.output_mem_file_path)
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

def print_mem(mem):
    
    word_list = get_word_list(mem)

    print("\nmem:")
    for word_addr, word_value in word_list:
        word_value_str = " ".join([f"{x:02X}" for x in word_value])
        print(f"    0x{word_addr << 2:08X}: {word_value_str}")
    print()

class ArchState:
    def __init__(self, start_pc, mem):
        self.pc = start_pc
        self.arf = [0x0 for x in range(32)]
        self.instret = 0
        self.mem = mem
        self.log = ""

    def exec_instr(self):
        instr = 0
        instr += self.mem[self.pc+0]
        instr += self.mem[self.pc+1]
        instr += self.mem[self.pc+2]
        instr += self.mem[self.pc+3]

        # uncompressed
        if instr & 0b11:
            self.log += f"PC = 0x{self.pc:08X} -> 0x{instr:08X}: "
            opcode5 = instr >> 2 & 0b11111
            rd = instr >> 7 & 0b11111
            rs1 = instr >> 15 & 0b11111
            rs2 = instr >> 20 & 0b11111

            if opcode5 == 0b01101:
                imm = 0
                self.log += f"LUI {rd}, {imm}"
                self.arf[rd] = 0

        # compressed
        else:
            self.log += f"PC = 0x{self.pc:08X} -> 0x{instr:04X}: "

        return True
    
    def incr_pc(self, compressed=False):
        if compressed:
            self.pc += 2
        else:
            self.pc += 4
        self.log += f"PC <= {self.pc:08X}"

    def print_log(self):
        print(self.log)

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

    # print(mem)
    print_mem(mem)

    # init arch state
    arch_state = ArchState(args.start_pc, mem)

    # execute program
    exception = False
    while not exception:
        exception = arch_state.exec_instr()

    arch_state.print_log()

    # print(mem)
    print_mem(mem)

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
import sys
import argparse

def get_word_list(mem):
    word_dict = dict()
    for byte_addr, byte_value in mem.items():
        try:
            word_dict[byte_addr >> 2][byte_addr & 2**2-1] = byte_value
        except KeyError:
            word_dict[byte_addr >> 2] = [0x0, 0x0, 0x0, 0x0]
            word_dict[byte_addr >> 2][byte_addr & 2**2-1] = byte_value

    word_list = []
    for word_addr, word_value in word_dict.items():
        if any(word_value):
            word_list.append((word_addr, word_value))

    return sorted(word_list, key=lambda x: x[0])

def print_mem(mem):
    
    word_list = get_word_list(mem)

    print("\nmem:")
    for word_addr, word_value in word_list:
        word_value_str = " ".join(reversed([f"{x:02X}" for x in word_value]))
        print(f"    0x{word_addr << 2:08X}: {word_value_str}")
    print()

class ArchState:
    def __init__(self, start_pc, mem):
        self.pc = args.start_pc
        self.reg_file = [0x0 for x in range(32)]
        self.instret = 0
        self.mem = mem

    def exec_instr(self):
        instr = 0
        instr += self.mem[self.pc+0]
        instr += self.mem[self.pc+1]
        instr += self.mem[self.pc+2]
        instr += self.mem[self.pc+3]

        if instr:
            return True

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
        if "/" in mem_line:
            mem_line = mem_line[:mem_line.index("/")]
        mem_line = mem_line.lstrip().rstrip()

        # ptr change
        if mem_line.startswith("@"):
            ptr = int(mem_line[1:], 16)

        # byte fill
        elif mem_line:
            byte_value_list = []
            while mem_line:
                byte_value_list.insert(0, int(mem_line[:2], 16))
                mem_line = mem_line[2:]
            # print(byte_value_list)
            for byte_value in byte_value_list:
                mem[ptr] = byte_value
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

    # print(mem)
    print_mem(mem)

    # write output mem
    with open(args.output_mem_file_path, "w") as fp:
        word_list = get_word_list(mem)

        first = True
        ptr_word_addr = -1
        for word_addr, word_value in word_list:
            word_value_str = "".join(reversed([f"{x:02X}" for x in word_value]))
            if word_addr != ptr_word_addr:
                if not first:
                    fp.write("\n")
                else:
                    first = False
                fp.write(f"@{word_addr << 2:0x}\n")
                ptr_word_addr = word_addr
            fp.write(word_value_str + "\n")
            ptr_word_addr += 1
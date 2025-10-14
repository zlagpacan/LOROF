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
        word_list.append((word_addr, word_value))

    word_list.sort(key=lambda x: x[0])

    return word_list

def print_mem(mem):
    
    word_list = get_word_list(mem)

    print("\nmem:")
    for word_addr, word_value in word_list:
        print(f"    0x{word_addr << 2:08X}: {word_value[0]:02X} {word_value[1]:02X} {word_value[2]:02X} {word_value[3]:02X}")
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
    pc = args.start_pc
    reg_file = [0x0 for x in range(32)]

    # execute program


    # print(mem)
    print_mem(mem)

    # # write output mem
    # with open(args.output_mem_file_path, "w") as fp:
    #     word_mem = get_word_mem(mem)

    #     fp.writeline(f"@{word_mem}")
        
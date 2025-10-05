#!/usr/bin/python3

import sys
import argparse
import re

reg_name_map = dict()
for i in range(32):
    reg_name_map[f"x{i}"] = i
reg_name_map.update({"zero": 0, "Zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7, "s0": 8, "fp": 8, "s1": 9, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17, "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23, "s8": 24, "s9": 25, "s10": 26, "s11": 27, "t3": 28, "t4": 29, "t5": 30, "t6": 31,})

def instr_to_hex(instr_str):
    # print(instr_str)

    binary = 0
    interpreted_instr = ""
    if instr_str.startswith("LUI "):
        binary += 0b_01101_11
        interpreted_instr += "LUI "

    elif instr_str.startswith("SW "):
        binary += 0b_01000_11
        interpreted_instr += "SW "
        binary += 

    elif instr_str.startswith("ADDI "):
        binary += 0b_00100_11
        interpreted_instr += "ADDI "

    else:
        raise Exception(f"ERROR: unrecognized instruction: {instr_str}")

    return f"{binary:X}    // {interpreted_instr}"

if __name__ == "__main__":
    print(" ".join(sys.argv))

    parser = argparse.ArgumentParser()
    parser.add_argument("input_asm_file_path")
    parser.add_argument("output_mem_file_path")
    args = parser.parse_args()
    # print(args)

    # read asm
    with open(args.input_asm_file_path, "r") as fp:
        input_asm_lines = fp.readlines()

    # parse asm
    output_mem_lines = []
    for asm_line in input_asm_lines:
        asm_line.lstrip().rstrip()

        # preserved lines
        if not asm_line or asm_line.startswith("@") or asm_line.startswith("//") or asm_line[0].isdigit():
            output_mem_lines.append(asm_line)

        # instr lines
        elif asm_line[0].isalpha():
            comment_index = asm_line.find("/")
            output_mem_lines.append(instr_to_hex(asm_line[:comment_index].upper().rstrip()) + asm_line[comment_index:] + "\n")

        # unrecognized lines
        else:
            raise Exception(f"ERROR: unrecognized line format: {asm_line}")

    # write mem
    with open(args.output_mem_file_path, "w") as fp:
        fp.writelines(output_mem_lines)
#!/usr/bin/python3

import sys
import argparse
import re

reg_name_map = dict()
for i in range(32):
    reg_name_map[f"x{i}"] = i
reg_name_map.update({"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7, "s0": 8, "fp": 8, "s1": 9, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17, "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23, "s8": 24, "s9": 25, "s10": 26, "s11": 27, "t3": 28, "t4": 29, "t5": 30, "t6": 31,})

def get_reg(reg_str):
    return reg_name_map[reg_str.lstrip("(), ").rstrip("(), ")]

def get_imm(imm_str, align=1):
    return int(imm_str.lstrip("(), ").rstrip("(), "), 0) * align // 1

def only(instr):
    return instr[instr.index(" "):]

def first(instr):
    return instr[instr.index(" "):instr.index(",")]

def second(instr):
    return instr[instr.index(","):instr[instr.index(",")+1:].index(",")]

def last(instr):
    instr = instr[::-1]
    val = instr[:instr.index(",")]
    return val[::-1]

def paren_prefix(instr):
    instr = instr[::-1]
    val = instr[instr.index("("):instr.index(",")]
    return val[::-1]

def in_paren(instr):
    return instr[instr.index("("):instr.index(")")]

def bin_rd(rd):
    return rd << 7

def bin_rs1(rs1):
    return rs1 << 15

def bin_rs2(rs2):
    return rs2 << 20

def instr_to_hex(instr):
    # print(instr)

    binary = 0
    interpreted_instr = ""
    compressed = False

    if instr.startswith("lui "):
        binary += 0b_01101_11
        interpreted_instr += "LUI "
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_imm(last(instr))
        binary += imm << 12
        interpreted_instr += f", {imm:#x}"

    elif instr.startswith("auipc "):
        binary += 0b_00101_11
        interpreted_instr += "AUIPC "
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_imm(last(instr))
        binary += imm << 12
        interpreted_instr += f", {imm:#x}"

    elif instr.startswith("jal "):
        binary += 0b_1101_11
        interpreted_instr += "JAL "
        rd = get_reg(first(instr))



    elif instr.startswith("sw "):
        binary += 0b_01000_11
        interpreted_instr += "SW "

    elif instr.startswith("addi "):
        binary += 0b_00100_11
        interpreted_instr += "ADDI "



    elif instr.startswith("c.addi16sp "):
        compressed = True
        binary += 0b_011_0_00010_00000_01
        interpreted_instr += "C.ADDI16SP "



    else:
        raise Exception(f"ERROR: unrecognized instruction: {instr}")

    if compressed:
        return f"{binary:04X}        // {interpreted_instr}"
    else:
        return f"{binary:08X}    // {interpreted_instr}"

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
        asm_line = asm_line.lstrip().rstrip()

        # preserved lines
        if not asm_line or asm_line.startswith("@") or asm_line.startswith("//") or asm_line[0].isdigit():
            output_mem_lines.append(asm_line)

        # instr lines
        elif asm_line[0].isalpha():
            try:
                comment_index = asm_line.index("/")
                output_mem_lines.append(instr_to_hex(asm_line[:comment_index].lower().rstrip()) + " " + asm_line[comment_index:])
            except ValueError:
                output_mem_lines.append(instr_to_hex(asm_line.lower()))

        # unrecognized lines
        else:
            raise Exception(f"ERROR: unrecognized line format: {asm_line}")

    for line in output_mem_lines:
        print(line)

    # write mem
    with open(args.output_mem_file_path, "w") as fp:
        fp.writelines("\n".join(output_mem_lines))
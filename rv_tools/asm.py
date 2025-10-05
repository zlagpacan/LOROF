import sys
import argparse
from math import ceil

reg_name_map = dict()
for i in range(32):
    reg_name_map[f"x{i}"] = i
reg_name_map.update({"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7, "s0": 8, "fp": 8, "s1": 9, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17, "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23, "s8": 24, "s9": 25, "s10": 26, "s11": 27, "t3": 28, "t4": 29, "t5": 30, "t6": 31,})

def get_reg(reg_str):
    return reg_name_map[reg_str.lstrip("(), ").rstrip("(), ")]

def get_num(imm_str, align=1):
    return int(imm_str.lstrip("(), ").rstrip("(), "), 0) // align * align

def only(instr):
    return instr[instr.index(" "):]

def first(instr):
    return instr[instr.index(" "):instr.index(",")]

def second(instr):
    return instr[instr.index(","):instr[instr.index(",")+1:].index(",") + instr.index(",")+1]

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

def bit(num, index):
    return (num >> index) & 1

def bits(num, upper_index, lower_index):
    return ((2**(upper_index+1) - 1) & num) >> lower_index

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
        imm = get_num(last(instr))
        binary += bits(imm, 31-12, 0) << 12
        interpreted_instr += f", {bits(imm, 31-12, 0)}"

    elif instr.startswith("auipc "):
        binary += 0b_00101_11
        interpreted_instr += "AUIPC "
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_num(last(instr))
        binary += bits(imm, 31-12, 0) << 12
        interpreted_instr += f", {bits(imm, 31-12, 0)}"

    elif instr.startswith("jal "):
        binary += 0b_11011_11
        interpreted_instr += "JAL "
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_num(last(instr), 2)
        binary += bits(imm, 19, 12) << 12
        binary += bit(imm, 11) << 20
        binary += bits(imm, 10, 1) << 21
        binary += bit(imm, 20) << 31
        interpreted_instr += f", {bits(imm, 20, 0)}"

    elif instr.startswith("jalr "):
        binary += 0b_11001_11
        interpreted_instr += "JALR "
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("beq "):
        binary += 0b_11000_11
        interpreted_instr += "BEQ "
        binary += 0b000 << 12
        rs1 = get_reg(first(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"x{rs1}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(last(instr), 2)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {bits(imm, 12, 0)}"

    elif instr.startswith("bne "):
        binary += 0b_11000_11
        interpreted_instr += "BNE "
        binary += 0b001 << 12
        rs1 = get_reg(first(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"x{rs1}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(last(instr), 2)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {bits(imm, 12, 0)}"

    elif instr.startswith("blt "):
        binary += 0b_11000_11
        interpreted_instr += "BLT "
        binary += 0b100 << 12
        rs1 = get_reg(first(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"x{rs1}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(last(instr), 2)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {bits(imm, 12, 0)}"

    elif instr.startswith("bge "):
        binary += 0b_11000_11
        interpreted_instr += "BGE "
        binary += 0b101 << 12
        rs1 = get_reg(first(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"x{rs1}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(last(instr), 2)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {bits(imm, 12, 0)}"

    elif instr.startswith("bltu "):
        binary += 0b_11000_11
        interpreted_instr += "BLTU "
        binary += 0b110 << 12
        rs1 = get_reg(first(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"x{rs1}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(last(instr), 2)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {bits(imm, 12, 0)}"

    elif instr.startswith("bgeu "):
        binary += 0b_11000_11
        interpreted_instr += "BGEU "
        binary += 0b111 << 12
        rs1 = get_reg(first(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"x{rs1}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(last(instr), 2)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {bits(imm, 12, 0)}"

    elif instr.startswith("lb "):
        binary += 0b_00000_11
        interpreted_instr += "LB "
        binary += 0b000 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lh "):
        binary += 0b_00000_11
        interpreted_instr += "LH "
        binary += 0b001 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lw "):
        binary += 0b_00000_11
        interpreted_instr += "LW "
        binary += 0b010 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lbu "):
        binary += 0b_00000_11
        interpreted_instr += "LBU "
        binary += 0b100 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lhu "):
        binary += 0b_00000_11
        interpreted_instr += "LHU "
        binary += 0b101 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("sb "):
        binary += 0b_01000_11
        interpreted_instr += "SB "
        binary += 0b000 << 12
        rs2 = get_reg(first(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f"x{rs2}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("sh "):
        binary += 0b_01000_11
        interpreted_instr += "SH "
        binary += 0b001 << 12
        rs2 = get_reg(first(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f"x{rs2}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("sw "):
        binary += 0b_01000_11
        interpreted_instr += "SW "
        binary += 0b010 << 12
        rs2 = get_reg(first(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f"x{rs2}"
        imm = get_num(paren_prefix(instr))
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {bits(imm, 11, 0)}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("addi "):
        binary += 0b_00100_11
        interpreted_instr += "ADDI "
        binary += 0b000 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("slli "):
        binary += 0b_00100_11
        interpreted_instr += "SLLI "
        binary += 0b001 << 12
        binary += 0b0000000 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 4, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("slti "):
        binary += 0b_00100_11
        interpreted_instr += "SLTI "
        binary += 0b010 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("sltiu "):
        binary += 0b_00100_11
        interpreted_instr += "SLTIU "
        binary += 0b011 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("xori "):
        binary += 0b_00100_11
        interpreted_instr += "XORI "
        binary += 0b100 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("srli "):
        binary += 0b_00100_11
        interpreted_instr += "SRLI "
        binary += 0b101 << 12
        binary += 0b0000000 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 4, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("srai "):
        binary += 0b_00100_11
        interpreted_instr += "SRAI "
        binary += 0b101 << 12
        binary += 0b0100000 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 4, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("ori "):
        binary += 0b_00100_11
        interpreted_instr += "ORI "
        binary += 0b110 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("andi "):
        binary += 0b_00100_11
        interpreted_instr += "ANDI "
        binary += 0b111 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(last(instr))
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("add "):
        binary += 0b_01100_11
        interpreted_instr += "ADD "
        binary += 0b000 << 12
        binary += 0b0000000 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sub "):
        binary += 0b_01100_11
        interpreted_instr += "SUB "
        binary += 0b000 << 12
        binary += 0b0100000 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sll "):
        binary += 0b_01100_11
        interpreted_instr += "SLL "
        binary += 0b001 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("slt "):
        binary += 0b_01100_11
        interpreted_instr += "SLT "
        binary += 0b010 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sltu "):
        binary += 0b_01100_11
        interpreted_instr += "SLTU "
        binary += 0b011 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("xor "):
        binary += 0b_01100_11
        interpreted_instr += "XOR "
        binary += 0b100 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("srl "):
        binary += 0b_01100_11
        interpreted_instr += "SRL "
        binary += 0b101 << 12
        binary += 0b0000000 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sra "):
        binary += 0b_01100_11
        interpreted_instr += "SRA "
        binary += 0b101 << 12
        binary += 0b0100000 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("or "):
        binary += 0b_01100_11
        interpreted_instr += "OR "
        binary += 0b110 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("and "):
        binary += 0b_01100_11
        interpreted_instr += "AND "
        binary += 0b111 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("fence "):
        binary += 0b_00011_11
        interpreted_instr += "FENCE "
        if "i" in first(instr):
            binary += 1 << 27
            interpreted_instr += "i"
        if "o" in first(instr):
            binary += 1 << 26
            interpreted_instr += "o"
        if "r" in first(instr):
            binary += 1 << 25
            interpreted_instr += "r"
        if "w" in first(instr):
            binary += 1 << 24
            interpreted_instr += "w"
        interpreted_instr += ", "
        if "i" in last(instr):
            binary += 1 << 23
            interpreted_instr += "i"
        if "o" in last(instr):
            binary += 1 << 22
            interpreted_instr += "o"
        if "r" in last(instr):
            binary += 1 << 21
            interpreted_instr += "r"
        if "w" in last(instr):
            binary += 1 << 20
            interpreted_instr += "w"

    elif instr.startswith("fence.tso"):
        binary += 0b_00011_11
        interpreted_instr += "FENCE.TSO"
        binary += 0b_1000_0011_0011 << 20

    elif instr.startswith("ecall"):
        binary += 0b_11100_11
        interpreted_instr += "ECALL"
    
    elif instr.startswith("ebreak"):
        binary += 0b_11100_11
        interpreted_instr += "EBREAK"
        binary += 0b00001 << 20

    elif instr.startswith("fence.i"):
        binary += 0b_00011_11
        interpreted_instr += "FENCE.I"
        binary += 0b001 << 12

    elif instr.startswith("csrrw "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRW "
        binary += 0b001 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        csr = get_num(second(instr))
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(last(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("csrrs "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRS "
        binary += 0b010 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        csr = get_num(second(instr))
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(last(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("csrrc "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRC "
        binary += 0b011 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        csr = get_num(second(instr))
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(last(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("csrrwi "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRWI "
        binary += 0b101 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        csr = get_num(second(instr))
        binary += csr << 20
        interpreted_instr += f", {csr}"
        uimm = get_num(last(instr))
        binary += bits(uimm, 4, 0) << 15
        interpreted_instr += f", {bits(uimm, 4, 0)}"

    elif instr.startswith("csrrsi "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRSI "
        binary += 0b110 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        csr = get_num(second(instr))
        binary += csr << 20
        interpreted_instr += f", {csr}"
        uimm = get_num(last(instr))
        binary += bits(uimm, 4, 0) << 15
        interpreted_instr += f", {bits(uimm, 4, 0)}"

    elif instr.startswith("csrrci "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRCI "
        binary += 0b111 << 12
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        csr = get_num(second(instr))
        binary += csr << 20
        interpreted_instr += f", {csr}"
        uimm = get_num(last(instr))
        binary += bits(uimm, 4, 0) << 15
        interpreted_instr += f", {bits(uimm, 4, 0)}"

    elif instr.startswith("mul "):
        binary += 0b_01100_11
        interpreted_instr += "MUL "
        binary += 0b000 << 12
        binary += 0b0000001 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("mulh "):
        binary += 0b_01100_11
        interpreted_instr += "MULH "
        binary += 0b001 << 12
        binary += 0b0000001 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("mulhsu "):
        binary += 0b_01100_11
        interpreted_instr += "MULHSU "
        binary += 0b010 << 12
        binary += 0b0000001 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("mulhu "):
        binary += 0b_01100_11
        interpreted_instr += "MULHU "
        binary += 0b011 << 12
        binary += 0b0000001 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("div "):
        binary += 0b_01100_11
        interpreted_instr += "DIV "
        binary += 0b100 << 12
        binary += 0b0000001 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("divu "):
        binary += 0b_01100_11
        interpreted_instr += "DIVU "
        binary += 0b101 << 12
        binary += 0b0000001 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("rem "):
        binary += 0b_01100_11
        interpreted_instr += "REM "
        binary += 0b110 << 12
        binary += 0b0000001 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("remu "):
        binary += 0b_01100_11
        interpreted_instr += "REMU "
        binary += 0b111 << 12
        binary += 0b0000001 << 25
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f"x{rd}"
        rs1 = get_reg(second(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("lr.w"):
        binary += 0b_01011_11
        interpreted_instr += "LR.W"
        binary += 0b010 << 12
        binary += 0b00010 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("sc.w"):
        binary += 0b_01011_11
        interpreted_instr += "SC.W"
        binary += 0b010 << 12
        binary += 0b00011 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoswap.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOSWAP.W"
        binary += 0b010 << 12
        binary += 0b00001 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoadd.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOADD.W"
        binary += 0b010 << 12
        binary += 0b00000 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoxor.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOXOR.W"
        binary += 0b010 << 12
        binary += 0b00100 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoand.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOAND.W"
        binary += 0b010 << 12
        binary += 0b01100 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoor.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOOR.W"
        binary += 0b010 << 12
        binary += 0b01000 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amomin.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOMIN.W"
        binary += 0b010 << 12
        binary += 0b10000 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amomax.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOMAX.W"
        binary += 0b010 << 12
        binary += 0b10100 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amominu.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOMINU.W"
        binary += 0b010 << 12
        binary += 0b11000 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amomaxu.w"):
        binary += 0b_01011_11
        interpreted_instr += "AMOMAXU.W"
        binary += 0b010 << 12
        binary += 0b11100 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
        if ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(first(instr))
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(second(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(in_paren(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    # TODO: compressed instructions

    elif instr.startswith("c.addi16sp "):
        compressed = True
        binary += 0b_011_0_00010_00000_01
        interpreted_instr += "C.ADDI16SP "



    elif instr.startswith("mret"):
        binary += 0b_11100_11
        interpreted_instr += "MRET"
        binary += 0b0011000_00010 << 20

    elif instr.startswith("wfi"):
        binary += 0b_11100_11
        interpreted_instr += "WFI"
        binary += 0b0001000_00101 << 20

    elif instr.startswith("sret"):
        binary += 0b_11100_11
        interpreted_instr += "SRET"
        binary += 0b0001000_00010 << 20

    elif instr.startswith("sfence.vma "):
        binary += 0b_11100_11
        interpreted_instr += "SFENCE.VMA "
        binary += 0b0001001 << 25
        rs1 = get_reg(first(instr))
        binary += bin_rs1(rs1)
        interpreted_instr += f"x{rs1}"
        rs2 = get_reg(last(instr))
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    else:
        raise Exception(f"unrecognized instruction: {instr}")

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

        # manually inserted hex or binary
        if asm_line.startswith("0x"):
            output_mem_lines.append(f"{int(asm_line, 0):0{ceil((len(asm_line)-2) / 2) * 2}X}")

        elif asm_line.startswith("0b"):
            output_mem_lines.append(f"{int(asm_line, 0):0{ceil((len(asm_line)-2) / 8) * 2}X}")

        # preserved lines
        elif not asm_line or asm_line.startswith("@") or asm_line.startswith("//"):
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
            raise Exception(f"unrecognized line format: {asm_line}")

    for line in output_mem_lines:
        print(line)

    # write mem
    with open(args.output_mem_file_path, "w") as fp:
        fp.writelines("\n".join(output_mem_lines))
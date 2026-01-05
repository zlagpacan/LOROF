import sys
import argparse
from math import ceil

reg_name_map = dict()
for i in range(32):
    reg_name_map[f"x{i}"] = i
reg_name_map.update({"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7, "s0": 8, "fp": 8, "s1": 9, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17, "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23, "s8": 24, "s9": 25, "s10": 26, "s11": 27, "t3": 28, "t4": 29, "t5": 30, "t6": 31,})

freg_name_map = dict()
for i in range(32):
    freg_name_map[f"f{i}"] = i
freg_name_map.update({"ft0": 0, "ft1": 1, "ft2": 2, "ft3": 3, "ft4": 4, "ft5": 5, "ft6": 6, "ft7": 7, "fs0": 8, "fs1": 9, "fa0": 10, "fa1": 11, "fa2": 12, "fa3": 13, "fa4": 14, "fa5": 15, "fa6": 16, "fa7": 17, "fs2": 18, "fs3": 19, "fs4": 20, "fs5": 21, "fs6": 22, "fs7": 23, "fs8": 24, "fs9": 25, "fs10": 26, "fs11": 27, "ft8": 28, "ft9": 29, "ft10": 30, "ft11": 31})

def get_reg(instr, func_ptr):
    try:
        return reg_name_map[func_ptr(instr).lstrip("(), ").rstrip("(), ")]
    except KeyError as e:
        print(func_ptr)
        raise Exception(f"\nBad reg from \"{func_ptr(instr)}\" @ {func_ptr.__name__}() for instr:\n{instr}")
    except ValueError as e:
        raise Exception(f"\nError getting reg @ {func_ptr.__name__}() for instr:\n{instr}")

def get_freg(instr, func_ptr):
    try:
        return freg_name_map[func_ptr(instr).lstrip("(), ").rstrip("(), ")]
    except KeyError as e:
        print(func_ptr)
        raise Exception(f"\nBad freg from \"{func_ptr(instr)}\" @ {func_ptr.__name__}() for instr:\n{instr}")
    except ValueError as e:
        raise Exception(f"\nError getting freg @ {func_ptr.__name__}() for instr:\n{instr}")

def get_regp(instr, func_ptr):
    try:
        regp = reg_name_map[func_ptr(instr).lstrip("(), ").rstrip("(), ")]
        assert 8 <= regp <= 15, f"\nERROR: reg must be in x8:x15 @ {func_ptr.__name__}() instr:\n{instr}"
        return regp
    except KeyError as e:
        print(func_ptr)
        raise Exception(f"\nBad regp from \"{func_ptr(instr)}\" @ {func_ptr.__name__}() for instr:\n{instr}")
    except ValueError as e:
        raise Exception(f"\nError getting regp @ {func_ptr.__name__}() for instr:\n{instr}")

def get_fregp(instr, func_ptr):
    try:
        fregp = freg_name_map[func_ptr(instr).lstrip("(), ").rstrip("(), ")]
        assert 8 <= fregp <= 15, f"\nERROR: freg must be in x8:x15 @ {func_ptr.__name__}() instr:\n{instr}"
        return fregp
    except KeyError as e:
        print(func_ptr)
        raise Exception(f"\nBad fregp from \"{func_ptr(instr)}\" @ {func_ptr.__name__}() for instr:\n{instr}")
    except ValueError as e:
        raise Exception(f"\nError getting fregp @ {func_ptr.__name__}() for instr:\n{instr}")

def get_num(instr, func_ptr, upper_index, lower_index, unsigned=False, signed=False):
    try:
        num = int(func_ptr(instr).lstrip("(), ").rstrip("(), "), 0)
        check_imm_bits(instr, num, upper_index, lower_index, unsigned, signed)
        return num
    except ValueError as e:
        raise Exception(f"\nError getting num @ {func_ptr.__name__}() for instr:\n{instr}")

def get_rm(instr, func_ptr):
    try:
        rm_str = func_ptr(instr).lstrip("(), ").rstrip("(), ").upper()
        if rm_str == "RNE": return 0b000, rm_str
        elif rm_str == "RTZ": return 0b001, rm_str
        elif rm_str == "RDN": return 0b010, rm_str
        elif rm_str == "RUP": return 0b011, rm_str
        elif rm_str == "RMM": return 0b100, rm_str
        elif rm_str == "DYN": return 0b111, rm_str
        else:
            raise Exception(f"\nUnrecognized rm value @ {func_ptr.__name__}() for instr: \n{instr}")
    except ValueError as e:
        raise Exception(f"\nError getting rm @ {func_ptr.__name__}() for instr:\n{instr}")

def only(instr):
    return instr[instr.index(" "):]

def first(instr):
    return instr[instr.index(" "):instr.index(",")]

def second(instr):
    return instr.split(",")[1]

def third(instr):
    return instr.split(",")[2]

def fourth(instr):
    return instr.split(",")[3]

def last(instr):
    instr = instr[::-1]
    val = instr[:instr.index(",")]
    return val[::-1]

def before_paren(instr):
    instr = instr[::-1]
    val = instr[instr.index("("):instr.index(",")]
    return val[::-1]

def in_paren(instr):
    return instr[instr.index("("):instr.index(")")]

def bin_rd(rd):
    return rd << 7
bin_frd = bin_rd

def bin_rs1(rs1):
    return rs1 << 15
bin_frs1 = bin_rs1

def bin_rs2(rs2):
    return rs2 << 20
bin_frs2 = bin_rs2

def bin_frs3(frs3):
    return frs3 << 27

def bit(num, index):
    return (num >> index) & 1

def bits(num, upper_index, lower_index):
    return ((2**(upper_index+1) - 1) & num) >> lower_index

def check_imm_bits(instr, num, upper_index, lower_index, unsigned=False, signed=False):
    if unsigned:
        assert 0 <= num <= (2**(upper_index+1))-(2**lower_index), f"\nimm={num} out of range: [0, {(2**(upper_index+1))-(2**lower_index)}] for instr:\n{instr}"
    elif signed:
        assert -(2**upper_index) <= num <= (2**upper_index)-(2**lower_index), f"\nimm={num} out of range: [{-(2**upper_index)}, {(2**upper_index)-(2**lower_index)}] for instr:\n{instr}"
    else:
        assert -(2**upper_index) <= num <= (2**(upper_index+1))-(2**lower_index), f"\nimm={num} out of range: [{-(2**upper_index)}, {(2**(upper_index+1))-(2**lower_index)}] for instr:\n{instr}"
    assert lower_index == 0 or bits(num, lower_index-1, 0) == 0, f"\nimm={num} not aligned to multiple of {2**lower_index} for instr:\n{instr}"

def make_little_endian(input_str):
    output_str = ""
    ptr = len(input_str)
    while ptr > 0:
        output_str += input_str[ptr-2:ptr] + " "
        ptr -= 2
    return output_str[:-1]

def instr_to_hex(instr):
    # print(instr)

    binary = 0
    interpreted_instr = ""
    compressed = False

    if instr.startswith("lui "):
        binary += 0b_01101_11
        interpreted_instr += "LUI"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, last, 19, 0)
        binary += bits(imm, 19, 0) << 12
        interpreted_instr += f", 0x{imm:05X}"

    elif instr.startswith("auipc "):
        binary += 0b_00101_11
        interpreted_instr += "AUIPC"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, last, 19, 0)
        binary += bits(imm, 19, 0) << 12
        interpreted_instr += f", 0x{imm:05X}"

    elif instr.startswith("jal "):
        binary += 0b_11011_11
        interpreted_instr += "JAL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, last, 20, 1, signed=True)
        binary += bits(imm, 19, 12) << 12
        binary += bit(imm, 11) << 20
        binary += bits(imm, 10, 1) << 21
        binary += bit(imm, 20) << 31
        interpreted_instr += f", {imm}"

    elif instr.startswith("jalr "):
        binary += 0b_11001_11
        interpreted_instr += "JALR"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("beq "):
        binary += 0b_11000_11
        interpreted_instr += "BEQ"
        binary += 0b000 << 12
        rs1 = get_reg(instr, first)
        binary += bin_rs1(rs1)
        interpreted_instr += f" x{rs1}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(instr, last, 12, 1, signed=True)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {imm}"

    elif instr.startswith("bne "):
        binary += 0b_11000_11
        interpreted_instr += "BNE"
        binary += 0b001 << 12
        rs1 = get_reg(instr, first)
        binary += bin_rs1(rs1)
        interpreted_instr += f" x{rs1}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(instr, last, 12, 1, signed=True)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {imm}"

    elif instr.startswith("blt "):
        binary += 0b_11000_11
        interpreted_instr += "BLT"
        binary += 0b100 << 12
        rs1 = get_reg(instr, first)
        binary += bin_rs1(rs1)
        interpreted_instr += f" x{rs1}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(instr, last, 12, 1, signed=True)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {imm}"

    elif instr.startswith("bge "):
        binary += 0b_11000_11
        interpreted_instr += "BGE"
        binary += 0b101 << 12
        rs1 = get_reg(instr, first)
        binary += bin_rs1(rs1)
        interpreted_instr += f" x{rs1}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(instr, last, 12, 1, signed=True)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {imm}"

    elif instr.startswith("bltu "):
        binary += 0b_11000_11
        interpreted_instr += "BLTU"
        binary += 0b110 << 12
        rs1 = get_reg(instr, first)
        binary += bin_rs1(rs1)
        interpreted_instr += f" x{rs1}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(instr, last, 12, 1, signed=True)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {imm}"

    elif instr.startswith("bgeu "):
        binary += 0b_11000_11
        interpreted_instr += "BGEU"
        binary += 0b111 << 12
        rs1 = get_reg(instr, first)
        binary += bin_rs1(rs1)
        interpreted_instr += f" x{rs1}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        imm = get_num(instr, last, 12, 1, signed=True)
        binary += bit(imm, 11) << 7
        binary += bits(imm, 4, 1) << 8
        binary += bits(imm, 10, 5) << 25
        binary += bit(imm, 12) << 31
        interpreted_instr += f", {imm}"

    elif instr.startswith("lb "):
        binary += 0b_00000_11
        interpreted_instr += "LB"
        binary += 0b000 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lh "):
        binary += 0b_00000_11
        interpreted_instr += "LH"
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lw "):
        binary += 0b_00000_11
        interpreted_instr += "LW"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("ld "):
        binary += 0b_00000_11
        interpreted_instr += "LD"
        binary += 0b011 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lbu "):
        binary += 0b_00000_11
        interpreted_instr += "LBU"
        binary += 0b100 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lhu "):
        binary += 0b_00000_11
        interpreted_instr += "LHU"
        binary += 0b101 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("lwu "):
        binary += 0b_00000_11
        interpreted_instr += "LWU"
        binary += 0b110 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("sb "):
        binary += 0b_01000_11
        interpreted_instr += "SB"
        binary += 0b000 << 12
        rs2 = get_reg(instr, first)
        binary += bin_rs2(rs2)
        interpreted_instr += f" x{rs2}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("sh "):
        binary += 0b_01000_11
        interpreted_instr += "SH"
        binary += 0b001 << 12
        rs2 = get_reg(instr, first)
        binary += bin_rs2(rs2)
        interpreted_instr += f" x{rs2}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("sw "):
        binary += 0b_01000_11
        interpreted_instr += "SW"
        binary += 0b010 << 12
        rs2 = get_reg(instr, first)
        binary += bin_rs2(rs2)
        interpreted_instr += f" x{rs2}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("sd "):
        binary += 0b_01000_11
        interpreted_instr += "SD"
        binary += 0b011 << 12
        rs2 = get_reg(instr, first)
        binary += bin_rs2(rs2)
        interpreted_instr += f" x{rs2}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("addi "):
        binary += 0b_00100_11
        interpreted_instr += "ADDI"
        binary += 0b000 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(instr, last, 11, 0)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("slli "):
        binary += 0b_00100_11
        interpreted_instr += "SLLI"
        binary += 0b001 << 12
        binary += 0b000000 << 26
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        shamt = get_num(instr, last, 5, 0, unsigned=True)
        binary += bits(shamt, 5, 0) << 20
        interpreted_instr += f", {shamt}"

    elif instr.startswith("slti "):
        binary += 0b_00100_11
        interpreted_instr += "SLTI"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(instr, last, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("sltiu "):
        binary += 0b_00100_11
        interpreted_instr += "SLTIU"
        binary += 0b011 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(instr, last, 11, 0, unsigned=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("xori "):
        binary += 0b_00100_11
        interpreted_instr += "XORI"
        binary += 0b100 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(instr, last, 11, 0)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("srli "):
        binary += 0b_00100_11
        interpreted_instr += "SRLI"
        binary += 0b101 << 12
        binary += 0b000000 << 26
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        shamt = get_num(instr, last, 5, 0, unsigned=True)
        binary += bits(shamt, 5, 0) << 20
        interpreted_instr += f", {shamt}"

    elif instr.startswith("srai "):
        binary += 0b_00100_11
        interpreted_instr += "SRAI"
        binary += 0b101 << 12
        binary += 0b010000 << 26
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        shamt = get_num(instr, last, 5, 0, unsigned=True)
        binary += bits(shamt, 5, 0) << 20
        interpreted_instr += f", {shamt}"

    elif instr.startswith("ori "):
        binary += 0b_00100_11
        interpreted_instr += "ORI"
        binary += 0b110 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(instr, last, 11, 0)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("andi "):
        binary += 0b_00100_11
        interpreted_instr += "ANDI"
        binary += 0b111 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(instr, last, 11, 0)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("addiw "):
        binary += 0b_00110_11
        interpreted_instr += "ADDIW"
        binary += 0b000 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        imm = get_num(instr, last, 11, 0)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"

    elif instr.startswith("slliw "):
        binary += 0b_00110_11
        interpreted_instr += "SLLIW"
        binary += 0b001 << 12
        binary += 0b0000000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        shamt = get_num(instr, last, 4, 0, unsigned=True)
        binary += bits(shamt, 4, 0) << 20
        interpreted_instr += f", {shamt}"

    elif instr.startswith("srliw "):
        binary += 0b_00110_11
        interpreted_instr += "SRLIW"
        binary += 0b101 << 12
        binary += 0b0000000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        shamt = get_num(instr, last, 4, 0, unsigned=True)
        binary += bits(shamt, 4, 0) << 20
        interpreted_instr += f", {shamt}"

    elif instr.startswith("sraiw "):
        binary += 0b_00110_11
        interpreted_instr += "SRAIW"
        binary += 0b101 << 12
        binary += 0b0100000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        shamt = get_num(instr, last, 4, 0, unsigned=True)
        binary += bits(shamt, 4, 0) << 20
        interpreted_instr += f", {shamt}"

    elif instr.startswith("add "):
        binary += 0b_01100_11
        interpreted_instr += "ADD"
        binary += 0b000 << 12
        binary += 0b0000000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sub "):
        binary += 0b_01100_11
        interpreted_instr += "SUB"
        binary += 0b000 << 12
        binary += 0b0100000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sll "):
        binary += 0b_01100_11
        interpreted_instr += "SLL"
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("slt "):
        binary += 0b_01100_11
        interpreted_instr += "SLT"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sltu "):
        binary += 0b_01100_11
        interpreted_instr += "SLTU"
        binary += 0b011 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("xor "):
        binary += 0b_01100_11
        interpreted_instr += "XOR"
        binary += 0b100 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("srl "):
        binary += 0b_01100_11
        interpreted_instr += "SRL"
        binary += 0b101 << 12
        binary += 0b0000000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sra "):
        binary += 0b_01100_11
        interpreted_instr += "SRA"
        binary += 0b101 << 12
        binary += 0b0100000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("or "):
        binary += 0b_01100_11
        interpreted_instr += "OR"
        binary += 0b110 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("and "):
        binary += 0b_01100_11
        interpreted_instr += "AND"
        binary += 0b111 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("addw "):
        binary += 0b_01110_11
        interpreted_instr += "ADDW"
        binary += 0b000 << 12
        binary += 0b0000000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("subw "):
        binary += 0b_01110_11
        interpreted_instr += "SUBW"
        binary += 0b000 << 12
        binary += 0b0100000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sllw "):
        binary += 0b_01110_11
        interpreted_instr += "SLLW"
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("srlw "):
        binary += 0b_01110_11
        interpreted_instr += "SRLW"
        binary += 0b101 << 12
        binary += 0b0000000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("sraw "):
        binary += 0b_01110_11
        interpreted_instr += "SRAW"
        binary += 0b101 << 12
        binary += 0b0100000 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("fence "):
        binary += 0b_00011_11
        interpreted_instr += "FENCE"
        interpreted_instr += " "
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
        binary += 0b_1000_0011_0011 << 20
        interpreted_instr += "FENCE.TSO"

    elif instr.startswith("ecall"):
        binary += 0b_11100_11
        interpreted_instr += "ECALL"
    
    elif instr.startswith("ebreak"):
        binary += 0b_11100_11
        binary += 0b00001 << 20
        interpreted_instr += "EBREAK"

    elif instr.startswith("fence.i"):
        binary += 0b_00011_11
        binary += 0b001 << 12
        interpreted_instr += "FENCE.I"

    elif instr.startswith("csrrw "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRW"
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = get_num(instr, second, 11, 0, unsigned=True)
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(instr, last)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("csrrs "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRS"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = get_num(instr, second, 11, 0, unsigned=True)
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(instr, last)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("csrrc "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRC"
        binary += 0b011 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = get_num(instr, second, 11, 0, unsigned=True)
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(instr, last)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("csrrwi "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRWI"
        binary += 0b101 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = get_num(instr, second, 11, 0, unsigned=True)
        binary += csr << 20
        interpreted_instr += f", {csr}"
        uimm = get_num(instr, last, 4, 0, unsigned=True)
        binary += bits(uimm, 4, 0) << 15
        interpreted_instr += f", {bits(uimm, 4, 0)}"

    elif instr.startswith("csrrsi "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRSI"
        binary += 0b110 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = get_num(instr, second, 11, 0, unsigned=True)
        binary += csr << 20
        interpreted_instr += f", {csr}"
        uimm = get_num(instr, last, 4, 0, unsigned=True)
        binary += bits(uimm, 4, 0) << 15
        interpreted_instr += f", {bits(uimm, 4, 0)}"

    elif instr.startswith("csrrci "):
        binary += 0b_11100_11
        interpreted_instr += "CSRRCI"
        binary += 0b111 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = get_num(instr, second, 11, 0, unsigned=True)
        binary += csr << 20
        interpreted_instr += f", {csr}"
        uimm = get_num(instr, last, 4, 0, unsigned=True)
        binary += bits(uimm, 4, 0) << 15
        interpreted_instr += f", {bits(uimm, 4, 0)}"

    elif instr.startswith("rdcycle "):
        # CSRRS rd, 0xC00, x0
        binary += 0b_11100_11
        interpreted_instr += "RDCYCLE: CSRRS"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0xC00
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = 0
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("rdtime "):
        # CSRRS rd, 0xC01, x0
        binary += 0b_11100_11
        interpreted_instr += "RDTIME: CSRRS"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0xC01
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = 0
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("rdinstret "):
        # CSRRS rd, 0xC02, x0
        binary += 0b_11100_11
        interpreted_instr += "RDINSTRET: CSRRS"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0xC02
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = 0
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("frflags "):
        # CSRRS rd, 0x001, x0
        binary += 0b_11100_11
        interpreted_instr += "FRFLAGS: CSRRS"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0x001
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = 0
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("fsflags "):
        # CSRRW rd, 0x001, rs1
        binary += 0b_11100_11
        interpreted_instr += "FSFLAGS: CSRRW"
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0x001
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(instr, last)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("frrm "):
        # CSRRS rd, 0x002, x0
        binary += 0b_11100_11
        interpreted_instr += "FRRM: CSRRS"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0x002
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = 0
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("fsrm "):
        # CSRRW rd, 0x002, rs1
        binary += 0b_11100_11
        interpreted_instr += "FSRM: CSRRW"
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0x002
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(instr, last)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("frcsr "):
        # CSRRS rd, 0x003, x0
        binary += 0b_11100_11
        interpreted_instr += "FRCSR: CSRRS"
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0x003
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = 0
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("fscsr "):
        # CSRRW rd, 0x003, rs1
        binary += 0b_11100_11
        interpreted_instr += "FSCSR: CSRRW"
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        csr = 0x003
        binary += csr << 20
        interpreted_instr += f", {csr}"
        rs1 = get_reg(instr, last)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("mul "):
        binary += 0b_01100_11
        interpreted_instr += "MUL"
        binary += 0b000 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("mulh "):
        binary += 0b_01100_11
        interpreted_instr += "MULH"
        binary += 0b001 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("mulhsu "):
        binary += 0b_01100_11
        interpreted_instr += "MULHSU"
        binary += 0b010 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("mulhu "):
        binary += 0b_01100_11
        interpreted_instr += "MULHU"
        binary += 0b011 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("div "):
        binary += 0b_01100_11
        interpreted_instr += "DIV"
        binary += 0b100 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("divu "):
        binary += 0b_01100_11
        interpreted_instr += "DIVU"
        binary += 0b101 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("rem "):
        binary += 0b_01100_11
        interpreted_instr += "REM"
        binary += 0b110 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("remu "):
        binary += 0b_01100_11
        interpreted_instr += "REMU"
        binary += 0b111 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("mulw "):
        binary += 0b_01110_11
        interpreted_instr += "MULW"
        binary += 0b000 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("divw "):
        binary += 0b_01110_11
        interpreted_instr += "DIVW"
        binary += 0b100 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("divuw "):
        binary += 0b_01110_11
        interpreted_instr += "DIVUW"
        binary += 0b101 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("remw "):
        binary += 0b_01110_11
        interpreted_instr += "REMW"
        binary += 0b110 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("remuw "):
        binary += 0b_01110_11
        interpreted_instr += "REMUW"
        binary += 0b111 << 12
        binary += 0b0000001 << 25
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rs2 = get_reg(instr, last)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
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
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("lr.d"):
        binary += 0b_01011_11
        interpreted_instr += "LR.D"
        binary += 0b011 << 12
        binary += 0b00010 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("sc.d"):
        binary += 0b_01011_11
        interpreted_instr += "SC.D"
        binary += 0b011 << 12
        binary += 0b00011 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoswap.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOSWAP.D"
        binary += 0b011 << 12
        binary += 0b00001 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoadd.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOADD.D"
        binary += 0b011 << 12
        binary += 0b00000 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoxor.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOXOR.d"
        binary += 0b011 << 12
        binary += 0b00100 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoand.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOAND.D"
        binary += 0b011 << 12
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
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amoor.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOOR.D"
        binary += 0b011 << 12
        binary += 0b01000 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amomin.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOMIN.D"
        binary += 0b011 << 12
        binary += 0b10000 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amomax.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOMAX.D"
        binary += 0b011 << 12
        binary += 0b10100 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amominu.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOMINU.D"
        binary += 0b011 << 12
        binary += 0b11000 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("amomaxu.d"):
        binary += 0b_01011_11
        interpreted_instr += "AMOMAXU.D"
        binary += 0b011 << 12
        binary += 0b11100 << 27
        if ".aq" in instr:
            binary += 1 << 26
            interpreted_instr += ".AQ"
            if "rl" in instr:
                binary += 1 << 25
                interpreted_instr += "RL"
        elif ".rl" in instr:
            binary += 1 << 25
            interpreted_instr += ".RL"
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, second)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f", (x{rs1})"

    elif instr.startswith("flw "):
        binary += 0b_00001_11
        interpreted_instr += "FLW"
        binary += 0b010 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("fsw "):
        binary += 0b_01001_11
        interpreted_instr += "FSW"
        binary += 0b010 << 12
        frs2 = get_freg(instr, first)
        binary += bin_frs2(frs2)
        interpreted_instr += f" x{rs2}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("fmadd.s "):
        binary += 0b_10000_11
        interpreted_instr += "FMADD.S"
        binary += 0b00 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        frs3 = get_freg(instr, fourth)
        binary += bin_frs3(frs3)
        interpreted_instr += f", f{frs3}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"

    elif instr.startswith("fmsub.s "):
        binary += 0b_10001_11
        interpreted_instr += "FMSUB.S"
        binary += 0b00 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        frs3 = get_freg(instr, fourth)
        binary += bin_frs3(frs3)
        interpreted_instr += f", f{frs3}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"

    elif instr.startswith("fnmsub.s "):
        binary += 0b_10010_11
        interpreted_instr += "FNMSUB.S"
        binary += 0b00 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        frs3 = get_freg(instr, fourth)
        binary += bin_frs3(frs3)
        interpreted_instr += f", f{frs3}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"

    elif instr.startswith("fnmadd.s "):
        binary += 0b_10011_11
        interpreted_instr += "FNMADD.S"
        binary += 0b00 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        frs3 = get_freg(instr, fourth)
        binary += bin_frs3(frs3)
        interpreted_instr += f", f{frs3}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fadd.s "):
        binary += 0b_10100_11
        interpreted_instr += "FADD.S"
        binary += 0b0000000 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fsub.s "):
        binary += 0b_10100_11
        interpreted_instr += "FSUB.S"
        binary += 0b0000100 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fmul.s "):
        binary += 0b_10100_11
        interpreted_instr += "FMUL.S"
        binary += 0b0001000 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fdiv.s "):
        binary += 0b_10100_11
        interpreted_instr += "FDIV.S"
        binary += 0b0001100 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fsqrt.s "):
        binary += 0b_10100_11
        interpreted_instr += "FSQRT.S"
        binary += 0b0001100 << 25
        binary += 0b00000 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fsgnj.s "):
        binary += 0b_10100_11
        interpreted_instr += "FSGNJ.S"
        binary += 0b0010000 << 25
        binary += 0b000 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fsgnjn.s "):
        binary += 0b_10100_11
        interpreted_instr += "FSGNJN.S"
        binary += 0b0010000 << 25
        binary += 0b001 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fsgnjx.s "):
        binary += 0b_10100_11
        interpreted_instr += "FSGNJX.S"
        binary += 0b0010000 << 25
        binary += 0b010 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fmin.s "):
        binary += 0b_10100_11
        interpreted_instr += "FMIN.S"
        binary += 0b0010100 << 25
        binary += 0b000 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fmax.s "):
        binary += 0b_10100_11
        interpreted_instr += "FMAX.S"
        binary += 0b0010100 << 25
        binary += 0b001 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fcvt.w.s "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.W.S"
        binary += 0b1100000 << 25
        binary += 0b00000 << 20
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.wu.s "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.WU.S"
        binary += 0b1100000 << 25
        binary += 0b00001 << 20
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.l.s "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.L.S"
        binary += 0b1100000 << 25
        binary += 0b00010 << 20
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.lu.s "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.LU.S"
        binary += 0b1100000 << 25
        binary += 0b00011 << 20
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fmv.x.w ") or instr.startswith("fmv.x.s "):
        binary += 0b_10100_11
        interpreted_instr += "FMV.X.W"
        binary += 0b1110000 << 25
        binary += 0b00000 << 20
        binary += 0b000 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, last)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
    
    elif instr.startswith("feq.s "):
        binary += 0b_10100_11
        interpreted_instr += "FEQ.S"
        binary += 0b1010000 << 25
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("flt.s "):
        binary += 0b_10100_11
        interpreted_instr += "FLT.S"
        binary += 0b1010000 << 25
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fle.s "):
        binary += 0b_10100_11
        interpreted_instr += "FLE.S"
        binary += 0b1010000 << 25
        binary += 0b000 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fclass.s "):
        binary += 0b_10100_11
        interpreted_instr += "FCLASS.S"
        binary += 0b1110000 << 25
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, last)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
    
    elif instr.startswith("fcvt.s.w "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.S.W"
        binary += 0b1101000 << 25
        binary += 0b00000 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.s.wu "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.S.WU"
        binary += 0b1101000 << 25
        binary += 0b00001 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.s.l "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.S.L"
        binary += 0b1101000 << 25
        binary += 0b00010 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.s.lu "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.S.LU"
        binary += 0b1101000 << 25
        binary += 0b00011 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fmv.w.x ") or instr.startswith("fmv.s.x "):
        binary += 0b_10100_11
        interpreted_instr += "FMV.W.X"
        binary += 0b1111000 << 25
        binary += 0b00000 << 20
        binary += 0b000 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, last)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("fld "):
        binary += 0b_00001_11
        interpreted_instr += "FLD"
        binary += 0b011 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 11, 0) << 20
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("fsd "):
        binary += 0b_01001_11
        interpreted_instr += "FSD"
        binary += 0b011 << 12
        frs2 = get_freg(instr, first)
        binary += bin_frs2(frs2)
        interpreted_instr += f" x{rs2}"
        imm = get_num(instr, before_paren, 11, 0, signed=True)
        binary += bits(imm, 4, 0) << 7
        binary += bits(imm, 11, 5) << 25
        interpreted_instr += f", {imm}"
        rs1 = get_reg(instr, in_paren)
        binary += bin_rs1(rs1)
        interpreted_instr += f"(x{rs1})"

    elif instr.startswith("fmadd.d "):
        binary += 0b_10000_11
        interpreted_instr += "FMADD.D"
        binary += 0b01 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        frs3 = get_freg(instr, fourth)
        binary += bin_frs3(frs3)
        interpreted_instr += f", f{frs3}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"

    elif instr.startswith("fmsub.d "):
        binary += 0b_10001_11
        interpreted_instr += "FMSUB.D"
        binary += 0b01 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        frs3 = get_freg(instr, fourth)
        binary += bin_frs3(frs3)
        interpreted_instr += f", f{frs3}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"

    elif instr.startswith("fnmsub.d "):
        binary += 0b_10010_11
        interpreted_instr += "FNMSUB.D"
        binary += 0b01 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        frs3 = get_freg(instr, fourth)
        binary += bin_frs3(frs3)
        interpreted_instr += f", f{frs3}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"

    elif instr.startswith("fnmadd.d "):
        binary += 0b_10011_11
        interpreted_instr += "FNMADD.D"
        binary += 0b01 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        frs3 = get_freg(instr, fourth)
        binary += bin_frs3(frs3)
        interpreted_instr += f", f{frs3}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fadd.d "):
        binary += 0b_10100_11
        interpreted_instr += "FADD.D"
        binary += 0b0000001 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fsub.d "):
        binary += 0b_10100_11
        interpreted_instr += "FSUB.D"
        binary += 0b0000101 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fmul.d "):
        binary += 0b_10100_11
        interpreted_instr += "FMUL.D"
        binary += 0b0001001 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fdiv.d "):
        binary += 0b_10100_11
        interpreted_instr += "FDIV.D"
        binary += 0b0001101 << 25
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, third)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fsqrt.d "):
        binary += 0b_10100_11
        interpreted_instr += "FSQRT.D"
        binary += 0b0001101 << 25
        binary += 0b00000 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fsgnj.d "):
        binary += 0b_10100_11
        interpreted_instr += "FSGNJ.D"
        binary += 0b0010001 << 25
        binary += 0b000 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fsgnjn.d "):
        binary += 0b_10100_11
        interpreted_instr += "FSGNJN.D"
        binary += 0b0010001 << 25
        binary += 0b001 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fsgnjx.d "):
        binary += 0b_10100_11
        interpreted_instr += "FSGNJX.D"
        binary += 0b0010001 << 25
        binary += 0b010 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fmin.d "):
        binary += 0b_10100_11
        interpreted_instr += "FMIN.D"
        binary += 0b0010101 << 25
        binary += 0b000 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fmax.d "):
        binary += 0b_10100_11
        interpreted_instr += "FMAX.D"
        binary += 0b0010101 << 25
        binary += 0b001 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fcvt.w.d "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.W.D"
        binary += 0b1100001 << 25
        binary += 0b00000 << 20
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.wu.d "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.WU.D"
        binary += 0b1100001 << 25
        binary += 0b00001 << 20
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.l.d "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.L.D"
        binary += 0b1100001 << 25
        binary += 0b00010 << 20
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.lu.d "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.LU.D"
        binary += 0b1100001 << 25
        binary += 0b00011 << 20
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.s.d "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.S.D"
        binary += 0b0100000 << 25
        binary += 0b00001 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.d.s "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.D.S"
        binary += 0b0100001 << 25
        binary += 0b00000 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fmv.x.d "):
        binary += 0b_10100_11
        interpreted_instr += "FMV.X.D"
        binary += 0b1110001 << 25
        binary += 0b00000 << 20
        binary += 0b000 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, last)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
    
    elif instr.startswith("feq.d "):
        binary += 0b_10100_11
        interpreted_instr += "FEQ.D"
        binary += 0b1010001 << 25
        binary += 0b010 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("flt.d "):
        binary += 0b_10100_11
        interpreted_instr += "FLT.D"
        binary += 0b1010001 << 25
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fle.d "):
        binary += 0b_10100_11
        interpreted_instr += "FLE.D"
        binary += 0b1010001 << 25
        binary += 0b000 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, second)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
        frs2 = get_freg(instr, last)
        binary += bin_frs2(frs2)
        interpreted_instr += f", f{frs2}"
    
    elif instr.startswith("fclass.d "):
        binary += 0b_10100_11
        interpreted_instr += "FCLASS.D"
        binary += 0b1110001 << 25
        binary += 0b001 << 12
        rd = get_reg(instr, first)
        binary += bin_rd(rd)
        interpreted_instr += f" x{rd}"
        frs1 = get_freg(instr, last)
        binary += bin_frs1(frs1)
        interpreted_instr += f", f{frs1}"
    
    elif instr.startswith("fcvt.d.w "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.D.W"
        binary += 0b1101001 << 25
        binary += 0b00000 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.d.wu "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.D.WU"
        binary += 0b1101001 << 25
        binary += 0b00001 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.d.l "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.D.L"
        binary += 0b1101001 << 25
        binary += 0b00010 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fcvt.d.lu "):
        binary += 0b_10100_11
        interpreted_instr += "FCVT.D.LU"
        binary += 0b1101001 << 25
        binary += 0b00011 << 20
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, second)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"
        rm_num, rm_str = get_rm(instr, last)
        binary += rm << 12
        interpreted_instr += f", {rm_str}"
    
    elif instr.startswith("fmv.d.x "):
        binary += 0b_10100_11
        interpreted_instr += "FMV.D.X"
        binary += 0b1111001 << 25
        binary += 0b00000 << 20
        binary += 0b000 << 12
        frd = get_freg(instr, first)
        binary += bin_frd(frd)
        interpreted_instr += f" f{frd}"
        rs1 = get_reg(instr, last)
        binary += bin_rs1(rs1)
        interpreted_instr += f", x{rs1}"

    elif instr.startswith("c.addi4spn "):
        compressed = True
        binary += 0b00
        binary += 0b000 << 13
        interpreted_instr += "C.ADDI4SPN"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 2
        interpreted_instr += f" x{rdp}"
        uimm = get_num(instr, last, 9, 2, unsigned=True)
        binary += bits(uimm, 5, 4) << 11
        binary += bits(uimm, 9, 6) << 7
        binary += bit(uimm, 2) << 6
        binary += bit(uimm, 3) << 5
        interpreted_instr += f", {uimm}"

    elif instr.startswith("c.fld "):
        compressed = True
        binary += 0b00
        binary += 0b001 << 13
        interpreted_instr += "C.FLD"
        frdp = get_fregp(instr, first)
        binary += bits(frdp, 2, 0) << 2
        interpreted_instr += f" f{frdp}"
        uimm = get_num(instr, before_paren, 7, 3, unsigned=True)
        binary += bits(uimm, 5, 3) << 10
        binary += bit(uimm, 7, 6) << 5
        interpreted_instr += f", {uimm}"
        rs1p = get_regp(instr, in_paren)
        binary += bits(rs1p, 2, 0) << 7
        interpreted_instr += f"(x{rs1p})"

    elif instr.startswith("c.lw "):
        compressed = True
        binary += 0b00
        binary += 0b010 << 13
        interpreted_instr += "C.LW"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 2
        interpreted_instr += f" x{rdp}"
        uimm = get_num(instr, before_paren, 6, 2, unsigned=True)
        binary += bits(uimm, 5, 3) << 10
        binary += bit(uimm, 2) << 6
        binary += bit(uimm, 6) << 5
        interpreted_instr += f", {uimm}"
        rs1p = get_regp(instr, in_paren)
        binary += bits(rs1p, 2, 0) << 7
        interpreted_instr += f"(x{rs1p})"

    elif instr.startswith("c.ld "):
        compressed = True
        binary += 0b00
        binary += 0b011 << 13
        interpreted_instr += "C.LD"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 2
        interpreted_instr += f" x{rdp}"
        uimm = get_num(instr, before_paren, 7, 3, unsigned=True)
        binary += bits(uimm, 5, 3) << 10
        binary += bit(uimm, 7, 6) << 5
        interpreted_instr += f", {uimm}"
        rs1p = get_regp(instr, in_paren)
        binary += bits(rs1p, 2, 0) << 7
        interpreted_instr += f"(x{rs1p})"

    elif instr.startswith("c.fsd "):
        compressed = True
        binary += 0b00
        binary += 0b101 << 13
        interpreted_instr += "C.FSD"
        frs2p = get_fregp(instr, first)
        binary += bits(frs2p, 2, 0) << 2
        interpreted_instr += f" f{frs2p}"
        uimm = get_num(instr, before_paren, 7, 3, unsigned=True)
        binary += bits(uimm, 5, 3) << 10
        binary += bit(uimm, 7, 6) << 5
        interpreted_instr += f", {uimm}"
        rs1p = get_regp(instr, in_paren)
        binary += bits(rs1p, 2, 0) << 7
        interpreted_instr += f"(x{rs1p})"

    elif instr.startswith("c.sw "):
        compressed = True
        binary += 0b00
        binary += 0b110 << 13
        interpreted_instr += "C.SW"
        rs2p = get_regp(instr, first)
        binary += bits(rs2p, 2, 0) << 2
        interpreted_instr += f" x{rs2p}"
        uimm = get_num(instr, before_paren, 6, 2, unsigned=True)
        binary += bits(uimm, 5, 3) << 10
        binary += bit(uimm, 2) << 6
        binary += bit(uimm, 6) << 5
        interpreted_instr += f", {uimm}"
        rs1p = get_regp(instr, in_paren)
        binary += bits(rs1p, 2, 0) << 7
        interpreted_instr += f"(x{rs1p})"

    elif instr.startswith("c.sd "):
        compressed = True
        binary += 0b00
        binary += 0b101 << 13
        interpreted_instr += "C.SD"
        rs2p = get_regp(instr, first)
        binary += bits(rs2p, 2, 0) << 2
        interpreted_instr += f" x{rs2p}"
        uimm = get_num(instr, before_paren, 7, 3, unsigned=True)
        binary += bits(uimm, 5, 3) << 10
        binary += bit(uimm, 7, 6) << 5
        interpreted_instr += f", {uimm}"
        rs1p = get_regp(instr, in_paren)
        binary += bits(rs1p, 2, 0) << 7
        interpreted_instr += f"(x{rs1p})"

    elif instr.startswith("c.nop"):
        compressed = True
        binary += 0b01
        binary += 0b000 << 13
        interpreted_instr += "C.NOP"

    elif instr.startswith("c.addi "):
        compressed = True
        binary += 0b01
        binary += 0b000 << 13
        interpreted_instr += "C.ADDI"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, last, 5, 0)
        binary += bit(imm, 5) << 12
        binary += bits(imm, 4,0) << 2
        interpreted_instr += f", {imm}"

    elif instr.startswith("c.addiw "):
        compressed = True
        binary += 0b01
        binary += 0b001 << 13
        interpreted_instr += "C.ADDIW"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, last, 5, 0)
        binary += bit(imm, 5) << 12
        binary += bits(imm, 4,0) << 2
        interpreted_instr += f", {imm}"

    elif instr.startswith("c.li "):
        compressed = True
        binary += 0b01
        binary += 0b010 << 13
        interpreted_instr += "C.LI"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, last, 5, 0)
        binary += bit(imm, 5) << 12
        binary += bits(imm, 4, 0) << 2
        interpreted_instr += f", {imm}"

    elif instr.startswith("c.addi16sp "):
        compressed = True
        binary += 0b01
        binary += 0b011 << 13
        binary += 0b00010 << 7
        interpreted_instr += "C.ADDI16SP"
        imm = get_num(instr, only, 9, 4, signed=True)
        binary += bit(imm, 9) << 12
        binary += bit(imm, 4) << 6
        binary += bit(imm, 6) << 5
        binary += bits(imm, 8, 7) << 3
        binary += bit(imm, 5) << 2
        interpreted_instr += f" {imm}"

    elif instr.startswith("c.lui "):
        compressed = True
        binary += 0b01
        binary += 0b011 << 13
        interpreted_instr += "C.LUI"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        imm = get_num(instr, last, 5, 0)
        binary += bit(imm, 5) << 12
        binary += bits(imm, 4, 0) << 2
        interpreted_instr += f", {imm}"

    elif instr.startswith("c.srli "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b00 << 10
        interpreted_instr += "C.SRLI"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        shamt = get_num(instr, last, 5, 0, unsigned=True)
        binary += bit(shamt, 5) << 12
        binary += bits(shamt, 4, 0) << 2
        interpreted_instr += f", {shamt}"

    elif instr.startswith("c.srai "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b01 << 10
        interpreted_instr += "C.SRAI"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        shamt = get_num(instr, last, 5, 0, unsigned=True)
        binary += bit(shamt, 5) << 12
        binary += bits(shamt, 4, 0) << 2
        interpreted_instr += f", {shamt}"

    elif instr.startswith("c.andi "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b0 << 12
        binary += 0b10 << 10
        interpreted_instr += "C.ANDI"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        imm = get_num(instr, last, 5, 0)
        binary += bit(imm, 5) << 12
        binary += bits(imm, 4, 0) << 2
        interpreted_instr += f", {imm}"
    
    elif instr.startswith("c.sub "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b0 << 12
        binary += 0b11 << 10
        binary += 0b00 << 5
        interpreted_instr += "C.SUB"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        rs2p = get_regp(instr, last)
        binary += bits(rs2p, 2, 0) << 2
        interpreted_instr += f", x{rs2p}"

    elif instr.startswith("c.xor "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b0 << 12
        binary += 0b11 << 10
        binary += 0b01 << 5
        interpreted_instr += "C.XOR"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        rs2p = get_regp(instr, last)
        binary += bits(rs2p, 2, 0) << 2
        interpreted_instr += f", x{rs2p}"

    elif instr.startswith("c.or "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b0 << 12
        binary += 0b11 << 10
        binary += 0b10 << 5
        interpreted_instr += "C.OR"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        rs2p = get_regp(instr, last)
        binary += bits(rs2p, 2, 0) << 2
        interpreted_instr += f", x{rs2p}"

    elif instr.startswith("c.and "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b0 << 12
        binary += 0b11 << 10
        binary += 0b11 << 5
        interpreted_instr += "C.AND"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        rs2p = get_regp(instr, last)
        binary += bits(rs2p, 2, 0) << 2
        interpreted_instr += f", x{rs2p}"

    elif instr.startswith("c.subw "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b1 << 12
        binary += 0b11 << 10
        binary += 0b00 << 5
        interpreted_instr += "C.SUBW"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        rs2p = get_regp(instr, last)
        binary += bits(rs2p, 2, 0) << 2
        interpreted_instr += f", x{rs2p}"

    elif instr.startswith("c.addw "):
        compressed = True
        binary += 0b01
        binary += 0b100 << 13
        binary += 0b1 << 12
        binary += 0b11 << 10
        binary += 0b01 << 5
        interpreted_instr += "C.ADDW"
        rdp = get_regp(instr, first)
        binary += bits(rdp, 2, 0) << 7
        interpreted_instr += f" x{rdp}"
        rs2p = get_regp(instr, last)
        binary += bits(rs2p, 2, 0) << 2
        interpreted_instr += f", x{rs2p}"

    elif instr.startswith("c.j "):
        compressed = True
        binary += 0b01
        binary += 0b101 << 13
        interpreted_instr += "C.J"
        imm = get_num(instr, only, 11, 1, signed=True)
        binary += bit(imm, 11) << 12
        binary += bit(imm, 4) << 11
        binary += bits(imm, 9, 8) << 9
        binary += bit(imm, 10) << 8
        binary += bit(imm, 6) << 7
        binary += bit(imm, 7) << 6
        binary += bits(imm, 3, 1) << 3
        binary += bit(imm, 5) << 2

    elif instr.startswith("c.beqz "):
        compressed = True
        binary += 0b01
        binary += 0b110 << 13
        interpreted_instr += "C.BEQZ"
        rs1p = get_regp(instr, first)
        binary += bits(rs1p, 2, 0) << 7
        interpreted_instr += f" x{rs1p}"
        imm = get_num(instr, last, 8, 1, signed=True)
        binary += bit(imm, 8) << 12
        binary += bits(imm, 4, 3) << 10
        binary += bits(imm, 7, 6) << 5
        binary += bits(imm, 2, 1) << 3
        binary += bit(imm, 5) << 2
        interpreted_instr += f", {imm}"

    elif instr.startswith("c.bnez "):
        compressed = True
        binary += 0b01
        binary += 0b111 << 13
        interpreted_instr += "C.BNEZ"
        rs1p = get_regp(instr, first)
        binary += bits(rs1p, 2, 0) << 7
        interpreted_instr += f" x{rs1p}"
        imm = get_num(instr, last, 8, 1, signed=True)
        binary += bit(imm, 8) << 12
        binary += bits(imm, 4, 3) << 10
        binary += bits(imm, 7, 6) << 5
        binary += bits(imm, 2, 1) << 3
        binary += bit(imm, 5) << 2
        interpreted_instr += f", {imm}"

    elif instr.startswith("c.slli "):
        compressed = True
        binary += 0b10
        binary += 0b000 << 13
        interpreted_instr += "C.SLLI"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        shamt = get_num(instr, last, 5, 0, unsigned=True)
        binary += bit(shamt, 5) << 12
        binary += bits(shamt, 4, 0) << 2
        interpreted_instr += f", {shamt}"

    elif instr.startswith("c.fldsp "):
        compressed = True
        binary += 0b10
        binary += 0b001 << 13
        interpreted_instr += "C.FLDSP"
        frd = get_freg(instr, first)
        binary += frd << 7
        interpreted_instr += f" f{frd}"
        uimm = get_num(instr, last, 8, 3, unsigned=True)
        binary += bit(uimm, 5) << 12
        binary += bits(uimm, 4, 3) << 5
        binary += bits(uimm, 8, 6) << 2
        interpreted_instr += f", {uimm}"

    elif instr.startswith("c.lwsp "):
        compressed = True
        binary += 0b10
        binary += 0b010 << 13
        interpreted_instr += "C.LWSP"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        uimm = get_num(instr, last, 7, 2, unsigned=True)
        binary += bit(uimm, 5) << 12
        binary += bits(uimm, 4, 2) << 4
        binary += bits(uimm, 7, 6) << 2
        interpreted_instr += f", {uimm}"

    elif instr.startswith("c.ldsp "):
        compressed = True
        binary += 0b10
        binary += 0b011 << 13
        interpreted_instr += "C.LDSP"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        uimm = get_num(instr, last, 8, 3, unsigned=True)
        binary += bit(uimm, 5) << 12
        binary += bits(uimm, 4, 3) << 5
        binary += bits(uimm, 8, 6) << 2
        interpreted_instr += f", {uimm}"

    elif instr.startswith("c.jr "):
        compressed = True
        binary += 0b10
        binary += 0b100 << 13
        binary += 0b0 << 12
        interpreted_instr += "C.JR"
        rs1 = get_reg(instr, only)
        binary += rs1 << 7
        interpreted_instr += f" x{rs1}"

    elif instr.startswith("c.mv "):
        compressed = True
        binary += 0b10 
        binary += 0b100 << 13
        binary += 0b0 << 12
        interpreted_instr += "C.MV"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, last)
        binary += rs2 << 2
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("c.ebreak"):
        compressed = True
        binary += 0b10
        binary += 0b100 << 13
        binary += 0b1 << 12
        interpreted_instr += "C.EBREAK"

    elif instr.startswith("c.jalr "):
        compressed = True
        binary += 0b10
        binary += 0b100 << 13
        binary += 0b1 << 12
        interpreted_instr += "C.JALR"
        rs1 = get_reg(instr, only)
        binary += rs1 << 7
        interpreted_instr += f" x{rs1}"

    elif instr.startswith("c.add "):
        compressed = True
        binary += 0b10
        binary += 0b100 << 13
        binary += 0b1 << 12
        interpreted_instr += "C.ADD"
        rd = get_reg(instr, first)
        binary += rd << 7
        interpreted_instr += f" x{rd}"
        rs2 = get_reg(instr, last)
        binary += rs2 << 2
        interpreted_instr += f", x{rs2}"

    elif instr.startswith("c.fsdsp "):
        compressed = True
        binary += 0b10
        binary += 0b101 << 13
        interpreted_instr += "C.FSDSP"
        frs2 = get_freg(instr, first)
        binary += frs2 << 2
        interpreted_instr += f" f{frs2}"
        uimm = get_num(instr, last, 8, 3, unsigned=True)
        binary += bits(uimm, 5, 3) << 10
        binary += bits(uimm, 8, 6) << 7
        interpreted_instr += f", {uimm}"

    elif instr.startswith("c.swsp "):
        compressed = True
        binary += 0b10
        binary += 0b110 << 13
        interpreted_instr += "C.SWSP"
        rs2 = get_reg(instr, first)
        binary += rs2 << 2
        interpreted_instr += f" x{rs2}"
        uimm = get_num(instr, last, 7, 2, unsigned=True)
        binary += bits(uimm, 5, 2) << 9
        binary += bits(uimm, 7, 6) << 7
        interpreted_instr += f", {uimm}"

    elif instr.startswith("c.sdsp "):
        compressed = True
        binary += 0b10
        binary += 0b111 << 13
        interpreted_instr += "C.SDSP"
        rs2 = get_reg(instr, first)
        binary += rs2 << 2
        interpreted_instr += f" x{rs2}"
        uimm = get_num(instr, last, 8, 3, unsigned=True)
        binary += bits(uimm, 5, 3) << 9
        binary += bits(uimm, 8, 6) << 7
        interpreted_instr += f", {uimm}"

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
        rs1 = get_reg(instr, first)
        binary += bin_rs1(rs1)
        interpreted_instr += f"x{rs1}"
        rs2 = get_reg(instr, last)
        binary += bin_rs2(rs2)
        interpreted_instr += f", x{rs2}"

    else:
        raise Exception(f"\nUnrecognized instr:\n{instr}")

    if compressed:
        return make_little_endian(f"{binary:04X}") + f"       //     0x{binary:04X}: {interpreted_instr}"
    else:
        return make_little_endian(f"{binary:08X}") + f" // 0x{binary:08X}: {interpreted_instr}"

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
            output_mem_lines.append(make_little_endian(f"{int(asm_line, 0):0{ceil((len(asm_line)-2) / 2) * 2}X}"))

        elif asm_line.startswith("0b"):
            output_mem_lines.append(make_little_endian(f"{int(asm_line, 0):0{ceil((len(asm_line)-2) / 8) * 2}X}"))

        # preserved lines
        elif not asm_line or asm_line.startswith("@") or asm_line.startswith("//"):
            output_mem_lines.append(asm_line)

        # instr lines
        elif asm_line[0].isalpha():
            if "//" in asm_line:
                comment_index = asm_line.index("//")
                output_mem_lines.append(instr_to_hex(asm_line[:comment_index].lower().rstrip()) + " " + asm_line[comment_index:])
            else:
                output_mem_lines.append(instr_to_hex(asm_line.lower()))

        # unrecognized lines
        else:
            raise Exception(f"\nUnrecognized line format:\n{asm_line}")

    for line in output_mem_lines:
        print(line)

    # write mem
    with open(args.output_mem_file_path, "w") as fp:
        fp.writelines("\n".join(output_mem_lines))
@0000

// Error Cases:
// beezy x14, 12
// c.lw x4, 24(x15)
// JAL 15
// c.addi4spn 33
// c.addi4spn x9, 33
// c.addi4spn x10, -4
// addi x4, x5, x6
// c.sw 15, 16(x17)
// c.jal x13
// csrrw x15, 7
// lui x1, 0x100000
// jal x16, 47
// c.addi16sp 8
// slli x6, x7, 34
// srai x31, x20, -5
// beq t6, t7, -14
// beq t6, t5, 8190
// C.SW x12, -60(x11)
// c.lwsp a8, 4
// c.lwsp a5, -1
// c.swsp s5, 256
// CSRRW x20, 4096, x8
// CSRRWI x15, -1, 1
// csrrsi ra, 16, zero
// csrrsi ra, 16, -1
// csrrci ra, 16, 32

lui a0, 15566
AUIPC t3, 0xfffff
JAL sp, 88
JALR t3, 15(gp)
beq t1, a1, -0x62
BNE a3, a7, 4094
blt s3, x8, -4096
bge x3, zero, 2216
BLTU ra, tp, -488
BGEU gp, fp, 0
LB ra, 13(x31)
lh x5, -14(x22)
LW s1, -2047(t6)
lbu s2, 2047(zero)
LHU s3, -0x800(s3)
sb s4, -2048(t5)
SH s5, 0x7ff(t4)
sw x29, 0x104(zero) // whoa
ADDI x1, t2, 0x123
slli x0, x1, 31
SLTI x2, x3, -10
sltiu x4, x5, 4095
XORI x6, x7, 0xFFF
srai s5, s11, 14
ORI x8, x9, 0x876
andi x10, x11, 0x9ab
ADD x12, x13, x14
SUB x6, s6, t6
sll x15, x16, x17
SLT x18, x19, x20
sltu x21, x22, x23
XOR x24, x25, x26
srl a1, t1, x1
SRA x27, x28, x29
or x30, x31, x30
AND x29, x28, x27

// inserted hex
0xdeadbeef
0x00ff
0x000ff

FENCE iw, or
fence ORW, IOR
fence.tso
ecall
EBREAK
fence.i
csrrw t5, 0x731, s4
CSRRS x26, 0xfff, x25
csrrc x24, 0b0, x23
CSRRWI x22, 1233, 30
csrrsi x21, 0x808, 0
CSRRCI tp, 0x99, 9

// inserted binary
0b10100101
0b0111101011010

mul x20, x19, x18
MULH x17, x16, x15
mulhsu x3, x4, s5
MULHU x14, x13, x12
div x11, x10, x9
DIVU t1, fp, s8
rem x8, x7, x6
REMU x5, x4, x3
lr.w.rl x4, (sp)
SC.W t4, t4, (s1)
amoswap.w.rl x2, x1, (x0)
AMOADD.W x0, x1, (x2)
amoxor.w.aqrl x3, x4, (x5)
AMOAND.W.AQRL x4, t3, (s0)
amoor.w.AQ x6, x7, (x8)
AMOMIN.W.RL x9, x10, (x11)
amomax.w x12, x13, (x14)
amominu.W.aq s1, ra, (sp)
AMOMAXU.W x15, x16, (x17)

@1644 // segment 2

C.ADDI4SPN x15, 8
c.lw x14, 20(x13)
C.SW x12, 0(x11)
C.NOP 12
c.addi s11, 63
c.jal -0b1000_0000_0000
C.LI ra, -32
C.ADDI16SP 32
c.lui x28, 0x3F
C.SRLI x9, 16
c.srai x12, 1
C.ANDI x10, 0b110110
c.sub x11, x13
C.XOR x15, x14
c.or x13, x12
C.AND x11, x10
c.j -2
C.BEQZ x9, 254
c.bnez x8, -256
C.SLLI x7, 63
C.LWSP x19, 8
c.jr x26
c.MV sp, s9
c.ebreak
C.JALR s10
c.add x5, x30
C.SWSP t0, 252

// TODO: why do compressed shifts have 6-bit shamt?
    // maybe because sharing encoding for RV64I

mret
WFI
SRET
sfence.VMA s3, a0

0x0000
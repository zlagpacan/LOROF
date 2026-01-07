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
ld t3, 0x546(a3)
lbu s2, 2047(zero)
LHU s3, -0x800(s3)
LWU s2, -23(x30)
sb s4, -2048(t5)
SH s5, 0x7ff(t4)
sw x29, 0x104(zero) // whoa
sd x0, 63(sp)
ADDI x1, t2, 0x123
slli x0, x1, 63
SLTI x2, x3, -10
sltiu x4, x5, 4095
XORI x6, x7, 0xFFF
srli t2, fp, 32
srai s5, s11, 14
ORI x8, x9, 0x876
andi x10, x11, 0x9ab
ADDIW x3, s11, 0x3f3
slliw t1, a0, 12
SRLIW s0, s10, 31
sraiw a3, t6, 4
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
addw s1, x0, s2
SUBW t1, t2, s4
sllw a0, s6, gp
SRLW a2, s2, s2
sraw t0, x5, x24

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
rdcycle t1
RDTIME x0
rdinstret x18
FRFLAGS s4
fsflags t4, a1
FRRM x6
fsrm s9, t5
FRCSR x24
fscsr s10, t3

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
mulw t0, t1, t2
DIVW t3, t4, t5
divuw a6, a0, a1
REMW a2, a3, s0
REMUW s1, s2, s3
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
lr.d t4, x16, (zero)
SC.D.aqrl s3, x3, (t0)
amoswap.d.rl x4, x9, (t5)
AMOADD.D sp, x22, (s4)
amoxor.d.aq x27, a2, (gp)
AMOAND.D s8, fp, (x14)
amoor.d.aqrl x12, s6, (t3)
AMOMIN.D.aq x23, x1, (s0)
amomax.d.aqrl x20, s10, (x10)
AMOMINU.D x0, s1, (t0)
amomaxu.d.rl x13, s9, (x8)

flw f0, 0x7ff(x1)
FSW f2, -0x800(x3)
fmadd.s f4, f5, f6, f7, RNE
FMSUB.S f8, f9, f10, f11, rtz
fmsub.s f12, f13, f14, f15, RDN
FNMSUB.S f16, f17, f18, f19, rup
FADD.S f24, f25, f26, dyn
fsub.s f27, f28, f29, rne
FMUL.S f30, f31, ft0, RTZ
fdiv.s ft1, ft2, ft3, rdn
fsqrt.s ft4, ft5, rup
FSGNJ.S ft6, ft7, ft8
fsgnjn.s ft9, ft10, ft11
FSGNJX.s fs0, fs1, fs2
fmin.s fs3, fs4, fs5
FMAX.S fs6, fs7, fs8
fcvt.w.s s9, fs10, rup
FCVT.WU.S a0, fa1, RMM
fcvt.l.s a2, fa3, dyn
FCVT.LU.S a4, fa5, RNE
fmv.x.w a6, fa7
FEQ.S a7, fs5, f11
flt.s x5, ft1, fa2
FLE.S t6, fs0, ft0
fclass.s s4, ft8
FCVT.S.W ft3, a3, RTZ
fcvt.s.wu fa3, s11, rdn
FCVT.S.L ft0, sp, RUP
fcvt.s.lu fa6, gp, rmm
FMV.W.X fs8, x24

fld f2, -0x800(x3)
FSD f0, 0x7ff(x1)
fmadd.d f20, f21, f22, f23, RMM
FMSUB.D f12, f13, f14, f15, RDN
fmsub.d f8, f9, f10, f11, rtz
FNMSUB.D f16, f17, f18, f19, rup
FADD.D ft1, ft2, ft3, rdn
fsub.d f30, f31, ft0, rtz
FMUL.D f27, f28, f29, rne
fdiv.d f24, f25, f26, dyn
fsqrt.d ft4, ft5, rup
FSGNJ.D fs6, fs7, fs8
fsgnjn.d fs3, fs4, fs5
FSGNJX.d fs0, fs1, fs2
fmin.d ft9, ft10, ft11
FMAX.D ft6, ft7, ft8
fcvt.w.d a4, fa5, RNE
FCVT.WU.D a2, fa3, dyn
fcvt.l.d a0, fa1, RMM
FCVT.LU.D s9, fs10, rup
fcvt.s.d f0, f1, RUP
FCVT.D.S f2, f3, RTZ
fmv.x.d a6, fa7
FEQ.D t6, fs0, ft0
flt.d x5, ft1, fa2
FLE.D a7, fs5, f11
fclass.d s4, ft8
FCVT.D.W fa6, gp, rmm
fcvt.d.wu ft0, sp, RUP
FCVT.D.L fa3, s11, rdn
fcvt.d.lu ft3, a3, RTZ
FMV.D.X fs8, x24

@1644 // segment 2

C.ADDI4SPN x15, 8
C.FLD fa5, 24(a5)
c.lw x14, 20(x13)
C.LD s0, 216(fp)
c.fsd fs0, 8(a0)
C.SW x12, 0(x11)
c.sd a3, 136(a0)
C.NOP
c.addi s11, 63
// c.jal -0b1000_0000_0000
c.addiw a4, 0x3f
C.LI ra, -32
C.ADDI16SP 32
c.lui x28, 0x3F
C.SRLI x9, 32
c.srai x12, 1
C.ANDI x10, 0b110110
c.sub x11, x13
C.XOR x15, x14
c.or x13, x12
C.AND x11, x10
c.subw a3, x9
C.ADDW a5, fp
c.j -2
C.BEQZ x9, 254
c.bnez x8, -256
C.SLLI x7, 49
c.fldsp fa3, 0x1f0
C.LWSP x19, 0xfc
c.ldsp t2, 104
c.jr x26
c.MV sp, s9
c.ebreak
C.JALR s10
c.add x5, x30
C.FSDSP ft2, 0x1f8
C.SWSP t0, 252
c.sdsp a7, 0

mret
WFI
SRET
sfence.VMA s3, a0

0x0000
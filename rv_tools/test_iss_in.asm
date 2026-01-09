// setup
@0000
addi a3, zero, -15
sw a3, 0x78(sp)
lui s6, 0xabcde
c.swsp a3, 0x84
addi sp, a3, 24
c.swsp s6, 0x88
addi zero, s6, 246
ld a1, 0x702(s0)
addi s4, a1, -222
sd s4, 0x723(s1)
jal x0, 0x1000

@2000
0x01234567
0x00000000
0xFF00EE11

@700
0x76543210
0x0000
0xf0e1
0x1

@3000
0x0f0f0f0f

0x1e1e1e1e

0x2d2d2d2d

0x3c3c3c3c
0x4b4b4b4b
0x5a5a5a5a
0x69696969
0x78787878
0x87878787
0x96969696
0xa5a5a5a5
0xb4b4b4b4

// RV64I (32b)
@1024
lui x1, 0xfedcb
auipc x2, 0xa9876
jal x3, 24 // 0
blt x3, x4, 12 // 4
beq x0, x1, 16 // 2
bne x0, x1, -8 // 3
bge x3, x4, 24 // 5
bltu x0, x1, 8 // 6
jalr x4, 4(x3) // 1
bgeu x0, x1, -16 // 7
addi x5, x0, 0x300
lb x6, 0x406(x5)
lh x7, 0x405(x5)
lw x8, 0x403(x5)
lbu x9, 0x406(x5)
lhu x10, 0x405(x5)
sb x8, 0x500(x5)
sh x8, 0x501(x5)
sw x8, 0x503(x5)
addi x11, x8, 0x012
slli x12, x11, 3
slti x13, x12, 0x678
sltiu x14, x13, 0x9ab
xori x15, x14, 0xcde
srai x16, x15, 5
srli x17, x16, 4
ori x18, x17, 0x567
andi x19, x18, 0x89a
add x20, x19, x18
sub x21, x20, x19
sll x22, x21, x20
slt x23, x22, x21
sltu x24, x23, x22
xor x25, x22, x20
srl x26, x8, x16
sra x27, x8, x16
or x28, x27, x8
and x29, x27, x8

FENCE iw, or
fence ORW, IOR
fence.tso
// ecall
// EBREAK
fence.i
// csrrw t5, 0x731, s4
// CSRRS x26, 0xfff, x25
// csrrc x24, 0b0, x23
// CSRRWI x22, 1233, 30
// csrrsi x21, 0x808, 0
// CSRRCI tp, 0x99, 9
// mret
// WFI
// SRET
// sfence.vma t5, a5

sw x1, 0x600(x5)
sw x2, 0x604(x5)
sw x3, 0x608(x5)
sw x4, 0x60C(x5)
sw x5, 0x610(x5)
sw x6, 0x614(x5)
sw x7, 0x618(x5)
sw x8, 0x61C(x5)
sw x9, 0x620(x5)
sw x10, 0x624(x5)
sw x11, 0x628(x5)
sw x12, 0x62C(x5)
sw x13, 0x630(x5)
sw x14, 0x634(x5)
sw x15, 0x638(x5)
sw x16, 0x63C(x5)
sw x17, 0x640(x5)
sw x18, 0x644(x5)
sw x19, 0x648(x5)
sw x20, 0x64C(x5)
sw x21, 0x650(x5)
sw x22, 0x654(x5)
sw x23, 0x658(x5)
sw x24, 0x65C(x5)
sw x25, 0x660(x5)
sw x26, 0x664(x5)
sw x27, 0x668(x5)
sw x28, 0x66C(x5)
sw x29, 0x670(x5)

// M-Ext (32b)
add x1, x0, x10
add x2, x0, x28
sub x3, x0, x10
mul x4, x2, x1
mulh x5, x2, x1
mulhsu x6, x2, x1
mulhsu x7, x1, x2
mulhu x8, x2, x1
mul x9, x2, x3
mulh x10, x2, x3
mulhsu x11, x2, x3
mulhsu x12, x3, x2
mulhu x13, x2, x3
div x14, x2, x1
divu x15, x2, x1
rem x16, x2, x1
remu x17, x2, x1
div x18, x2, x3
divu x19, x2, x3
rem x20, x2, x3
remu x21, x2, x3

addi x22, x0, 0x300
sw x1, 0x700(x22)
sw x2, 0x704(x22)
sw x3, 0x708(x22)
sw x4, 0x70C(x22)
sw x5, 0x710(x22)
sw x6, 0x714(x22)
sw x7, 0x718(x22)
sw x8, 0x71C(x22)
sw x9, 0x720(x22)
sw x10, 0x724(x22)
sw x11, 0x728(x22)
sw x12, 0x72C(x22)
sw x13, 0x730(x22)
sw x14, 0x734(x22)
sw x15, 0x738(x22)
sw x16, 0x73C(x22)
sw x17, 0x740(x22)
sw x18, 0x744(x22)
sw x19, 0x748(x22)
sw x20, 0x74C(x22)
sw x21, 0x750(x22)

// A-Ext (32b)
lui x2, 0x3

lr.w.aq x3, (x2)
addi x4, x3, 1
sc.w.rl x5, x4, (x2)

addi x2, x2, 4
lr.w.aqrl x6, (x2)
sw x1, 0(x2)
sc.w x7, x4, (x2)

lr.w x8, (x2)
addi x2, x2, 4
addi x9, x8, 1
sc.w x10, x9, (x2)

addi x2, x2, 4
amoswap.w x11, x1, (x2)
addi x2, x2, 4
amoadd.w x12, x1, (x2)
addi x2, x2, 4
amoxor.w x13, x1, (x2)
addi x2, x2, 4
amoand.w x14, x1, (x2)
addi x2, x2, 4
amoor.w x15, x1, (x2)
addi x2, x2, 4
amomin.w x16, x1, (x2)
addi x2, x2, 4
amomax.w x17, x1, (x2)
addi x2, x2, 4
amominu.w x18, x1, (x2)
addi x2, x2, 4
amomaxu.w x19, x1, (x2)

addi x20, x0, 0x400
sw x1, 0x700(x20)
sw x2, 0x704(x20)
sw x3, 0x708(x20)
sw x4, 0x70C(x20)
sw x5, 0x710(x20)
sw x6, 0x714(x20)
sw x7, 0x718(x20)
sw x8, 0x71C(x20)
sw x9, 0x720(x20)
sw x10, 0x724(x20)
sw x11, 0x728(x20)
sw x12, 0x72C(x20)
sw x13, 0x730(x20)
sw x14, 0x734(x20)
sw x15, 0x738(x20)
sw x16, 0x73C(x20)
sw x17, 0x740(x20)
sw x18, 0x744(x20)
sw x19, 0x748(x20)

// C-Ext (32b)
addi x8, x0, 0x6FE
c.addi4spn x9, 0x3B4
c.lw x10, 0x4(x8)
c.sw x10, 0x34(x8)
c.nop
c.addi x2, 15
c.j 6
addi x1, x1, 0x123
c.li x3, 0x21
c.addi16sp -496
c.lui x4, 0x3A
c.srli x11, 5
c.srai x12, 5
c.andi x13, 0xA

addi x20, x0, 0x500
sw x1, 0x700(x20)
sw x2, 0x704(x20)
sw x3, 0x708(x20)
sw x4, 0x70C(x20)
sw x5, 0x710(x20)
sw x6, 0x714(x20)
sw x7, 0x718(x20)
sw x8, 0x71C(x20)
sw x9, 0x720(x20)
sw x10, 0x724(x20)
sw x11, 0x728(x20)
sw x12, 0x72C(x20)
sw x13, 0x730(x20)

c.sub x9, x8
c.xor x10, x9
c.or x11, x10
c.and x12, x11
c.j 10
addi x14, x0, -1
c.beqz x14, -254
c.bnez x14, 10
addi x13, x0, 0
c.bnez x13, 126
c.beqz x13, -14
c.slli x16, 11
addi sp, x0, 0x6FE
c.lwsp x17, 0x4
lui x18, 0x4
c.jalr x18
c.add x20, x19
c.swsp x20, 0x30

addi x21, x0, 0x600
sw x1, 0x700(x21)
sw x2, 0x704(x21)
sw x3, 0x708(x21)
sw x4, 0x70C(x21)
sw x5, 0x710(x21)
sw x6, 0x714(x21)
sw x7, 0x718(x21)
sw x8, 0x71C(x21)
sw x9, 0x720(x21)
sw x10, 0x724(x21)
sw x11, 0x728(x21)
sw x12, 0x72C(x21)
sw x13, 0x730(x21)
sw x14, 0x734(x21)
sw x15, 0x738(x21)
sw x16, 0x73C(x21)
sw x17, 0x740(x21)
sw x18, 0x744(x21)
sw x19, 0x748(x21)
sw x20, 0x74C(x21)

// go to RV64GC section
addi x21, zero, 0x64
slli x21, x21, 32
sd x21, 0(x21)
lui x22, 0x00005
jalr x0, 4(x22)

@4000
c.mv x19, x18
// c.ebreak
c.jr x1

// RV64GC section:

// RV64I (64b)
@5000
sd x16, 8(x21)
lui x23, 0x00001
addi x23, x23, 0x030
ld x1, 0x000(x23)
ld x2, 0x008(x23)
ld x3, 0x010(x23)
ld x4, 0x018(x23)
ld x5, 0x020(x23)
ld x6, 0x028(x23)
ld x7, 0x030(x23)
ld x8, 0x038(x23)
ld x9, 0x040(x23)
ld x10, 0x048(x23)
ld x11, 0x050(x23)
ld x12, 0x058(x23)
ld x13, 0x060(x23)
ld x14, 0x068(x23)
ld x15, 0x070(x23)
ld x16, 0x078(x23)
ld x17, 0x080(x23)
ld x18, 0x088(x23)
ld x19, 0x090(x23)
ld x20, 0x098(x23)

addiw x1, x1, 0x111
slliw x2, x2, 2
srliw x3, x3, 3
sraiw x4, x4, 4
addw x5, x5, x6
subw x6, x6, x7
sllw x7, x7, x8
srlw x8, x2, x9
sraw x9, x2, x9

// M-Ext (64b)
mulw x10, x10, x10
divw x11, x11, x12
divuw x12, x13, x12
remw x13, x13, x14
remuw x14, x14, x15

lui x24, 0x7000
sd x1, 0x000(x24)
sd x2, 0x008(x24)
sd x3, 0x010(x24)
sd x4, 0x018(x24)
sd x5, 0x020(x24)
sd x6, 0x028(x24)
sd x7, 0x030(x24)
sd x8, 0x038(x24)
sd x9, 0x040(x24)
sd x10, 0x048(x24)
sd x11, 0x050(x24)
sd x12, 0x058(x24)
sd x13, 0x060(x24)
sd x14, 0x068(x24)

// A-Ext (64b)
lr.d.aq x25, (x23)
addi x23, x23, 8
sc.d.rl x25, x26, (x23)

lr.d x15, (x24)
xor x15, x15, x16
sc.d.aq x16, x15, (x24)
addi x24, x24, 8
amoswap.d.rl x1, x1, (x24)
addi x24, x24, 8
amoadd.d.aqrl x2, x2, (x24)
addi x24, x24, 8
amoxor.d x3, x3, (x24)
addi x24, x24, 8
amoand.d.aq x4, x4, (x24)
addi x24, x24, 8
amoor.d.rl x5, x5, (x24)
addi x24, x24, 8
amomin.d.aqrl x6, x6, (x24)
addi x24, x24, 8
amomax.d x7, x7, (x24)
addi x24, x24, 8
amominu.d.aq x8, x8, (x24)
addi x24, x24, 8
amomaxu.d.rl x9, x9, (x24)

// F-Ext
flw f0, 0x15(x24)
flw f1, 0x18(x24)
flw f2, 0x0D(x24)
flw f3, 0x20(x24)
fcvt.s.w f4, x4, rne
fcvt.s.wu f5, x5, rtz
fcvt.s.l f6, x6, rdn
fcvt.s.lu f7, x7, rup
fmv.w.x f8, x17

fmadd.s f9, f0, f1, f5, rmm
fmsub.s f10, f6, f7, f8, dyn
fnmsub.s f11, f6, f7, f8, rne
fnmadd.s f12, f0, f1, f5, rtz

fadd.s f13, f0, f1, rdn
fsub.s f14, f1, f5, rup
fmul.s f15, f5, f6, rmm
fsqrt.s f16, f7, rne
fdiv.s f17, f13, f16, dyn

fsgnj.s f18, f0, f0
fsgnj.s f19, f0, f1
fsgnj.s f20, f1, f0
fsgnj.s f21, f1, f1

fsgnjn.s f22, f0, f0
fsgnjn.s f23, f0, f1
fsgnjn.s f24, f1, f0
fsgnjn.s f25, f1, f1

fsgnjx.s f26, f0, f0
fsgnjx.s f27, f0, f1
fsgnjx.s f28, f1, f0
fsgnjx.s f29, f1, f1

fmin.s f30, f5, f6
fmax.s f31, f7, f8

fsw f0, 0x100(x24)
fsw f1, 0x104(x24)
fsw f2, 0x108(x24)
fsw f3, 0x10C(x24)
fsw f4, 0x110(x24)
fsw f5, 0x114(x24)
fsw f6, 0x118(x24)
fsw f7, 0x11C(x24)
fsw f8, 0x120(x24)
fsw f9, 0x124(x24)
fsw f10, 0x128(x24)
fsw f11, 0x12C(x24)
fsw f12, 0x130(x24)
fsw f13, 0x134(x24)
fsw f14, 0x138(x24)
fsw f15, 0x13C(x24)
fsw f16, 0x140(x24)
fsw f17, 0x144(x24)
fsw f18, 0x148(x24)
fsw f19, 0x14C(x24)
fsw f20, 0x150(x24)
fsw f21, 0x154(x24)
fsw f22, 0x158(x24)
fsw f23, 0x15C(x24)
fsw f24, 0x160(x24)
fsw f25, 0x164(x24)
fsw f26, 0x168(x24)
fsw f27, 0x16C(x24)
fsw f28, 0x170(x24)
fsw f29, 0x174(x24)
fsw f30, 0x178(x24)
fsw f31, 0x17C(x24)

fcvt.w.s x10, f17, rdn
fcvt.wu.s x11, f17, rup
fcvt.l.s x12, f11, rmm
fcvt.lu.s x13, f11, dyn
fmv.x.w x14, f14

feq.s x15, f17, f17
feq.s x16, f17, f18
feq.s x17, f18, f17
flt.s x18, f17, f17
flt.s x19, f17, f18
flt.s x20, f18, f17
fle.s x21, f17, f17
fle.s x22, f17, f18
fle.s x23, f18, f17
// fclass.s x24, f18

sd x10, 0x200(x24)
sd x11, 0x208(x24)
sd x12, 0x210(x24)
sd x13, 0x218(x24)
sd x14, 0x220(x24)
sd x15, 0x228(x24)
sd x16, 0x230(x24)
sd x17, 0x238(x24)
sd x18, 0x240(x24)
sd x19, 0x248(x24)
sd x20, 0x250(x24)
sd x21, 0x258(x24)
sd x22, 0x260(x24)
sd x23, 0x268(x24)

// D-Ext
fld f0, 0x100(x24)
fld f1, 0x104(x24)
fld f2, 0x108(x24)
fld f3, 0x10C(x24)
fcvt.d.w f4, x4, rne
fcvt.d.wu f5, x5, rtz
fcvt.d.l f6, x6, rdn
fcvt.d.lu f7, x7, rup

lui x1, 0xC0573
addi x1, x1, 0x5a5
slli x1, x1, 32
addi x1, x1, 0xa5a
fmv.d.x f0, x1
slli x2, x1, 1
srli x2, x2, 1
srli x3, x2, 7
xor x2, x3, x2
fmv.d.x f1, x2

fmadd.d f9, f4, f5, f6, rmm
fmsub.d f10, f6, f7, f8, dyn
fnmsub.d f11, f6, f7, f8, rne
fnmadd.d f12, f4, f5, f6, rtz

fadd.d f13, f0, f1, rdn
fsub.d f14, f1, f5, rup
fmul.d f15, f5, f6, rmm
fsqrt.d f16, f7, rne
fdiv.d f17, f13, f16, dyn

fsgnj.d f18, f0, f0
fsgnj.d f19, f0, f1
fsgnj.d f20, f1, f0
fsgnj.d f21, f1, f1

fsgnjn.d f22, f0, f0
fsgnjn.d f23, f0, f1
fsgnjn.d f24, f1, f0
fsgnjn.d f25, f1, f1

fsgnjx.d f26, f0, f0
fsgnjx.d f27, f0, f1
fsgnjx.d f28, f1, f0
fsgnjx.d f29, f1, f1

fmin.d f30, f5, f6
fmax.d f31, f7, f8

fsd f0, 0x300(x24)
fsd f1, 0x308(x24)
fsd f2, 0x310(x24)
fsd f3, 0x318(x24)
fsd f4, 0x320(x24)
fsd f5, 0x328(x24)
fsd f6, 0x330(x24)
fsd f7, 0x338(x24)
fsd f8, 0x340(x24)
fsd f9, 0x348(x24)
fsd f10, 0x350(x24)
fsd f11, 0x358(x24)
fsd f12, 0x360(x24)
fsd f13, 0x368(x24)
fsd f14, 0x370(x24)
fsd f15, 0x378(x24)
fsd f16, 0x380(x24)
fsd f17, 0x388(x24)
fsd f18, 0x390(x24)
fsd f19, 0x398(x24)
fsd f20, 0x3A0(x24)
fsd f21, 0x3A8(x24)
fsd f22, 0x3B0(x24)
fsd f23, 0x3B8(x24)
fsd f24, 0x3C0(x24)
fsd f25, 0x3C8(x24)
fsd f26, 0x3D0(x24)
fsd f27, 0x3D8(x24)
fsd f28, 0x3E0(x24)
fsd f29, 0x3E8(x24)
fsd f30, 0x3F0(x24)
fsd f31, 0x3F8(x24)

fcvt.w.d x10, f17, rdn
fcvt.wu.d x11, f17, rup
fcvt.l.d x12, f11, rmm
fcvt.lu.d x13, f11, dyn
fmv.x.d x14, f14

feq.d x15, f17, f17
feq.d x16, f17, f18
feq.d x17, f18, f17
flt.d x18, f17, f17
flt.d x19, f17, f18
flt.d x20, f18, f17
fle.d x21, f17, f17
fle.d x22, f17, f18
fle.d x23, f18, f17
// fclass.d x24, f18

sd x10, 0x400(x24)
sd x11, 0x408(x24)
sd x12, 0x410(x24)
sd x13, 0x418(x24)
sd x14, 0x420(x24)
sd x15, 0x428(x24)
sd x16, 0x430(x24)
sd x17, 0x438(x24)
sd x18, 0x440(x24)
sd x19, 0x448(x24)
sd x20, 0x450(x24)
sd x21, 0x458(x24)
sd x22, 0x460(x24)
sd x23, 0x468(x24)

lui x1, 0xC0573
addi x1, x1, 0x5a5
fmv.s.x f0, x1

lui x2, 0xC0573
addi x2, x2, 0x5a5
slli x2, x2, 32
addi x2, x2, 0xa5a
slli x2, x2, 1
srli x2, x2, 1
srli x3, x2, 7
xor x2, x3, x2
fmv.d.x f1, x2

fcvt.d.s f2, f0, rup
fcvt.s.d f3, f1, rdn

// TODO: new C-Ext

csrrw x0, 0x000, s0
csrrs x1, 0x111, t1
csrrc x2, 0x222, s2
csrrwi x3, 0x333, 0x3
csrrsi x4, 0x444, 0x4
csrrci x5, 0x555, 0x5
rdcycle x6
rdtime x7
rdinstret x8
frflags x9
fsflags x10, x11
frrm x12
fsrm x13, x14
frcsr x15
fscsr x16, x17
@0000
jal x0, 0x1000
addi a3, zero, -15
sw a3, 0x78(sp)
lui s6, 0xabcde
c.swsp a3, 0x84
addi sp, a3, 24
c.swsp s6, 0x88
addi zero, s6, 246
lw a1, 0x702(s0)
addi s4, a1, -222
sw s4, 0x723(s1)

@2000
0x01234567
0x00000000
0xFF00EE11

@700
0x76543210
0x0000
0xf0e1
0x1

@1000
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
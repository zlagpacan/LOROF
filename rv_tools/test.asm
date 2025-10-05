@0000
lui a0, 15566
JAL sp, 89
JALR t3, 15(gp)
beq t1, a1, -0x61
LB ra, 13(x31)
sw x29, 0x104(zero) // whoa
ADDI x1, t2, 0x123
srai s5, s11, 14
SUB x6, s6, t6
srl a1, t1, x1

// inserted hex
0xdeadbeef
0x00ff
0x000ff

FENCE iw, or
fence.tso
EBREAK
fence.i
csrrw t5, 0x731, s4
CSRRCI tp, 0x99, 9

// inserted binary
0b10100101
0b0111101011010

mulhsu x3, x4, s5
DIVU t1, fp, s8
lr.w.rl x4, (sp)
SC.W t4, t4, (s1)
AMOAND.W.AQRL x4, t3, (s0)
amominu.W.aq s1, ra, (sp)

C.ADDI16SP 17

mret
WFI
SRET
sfence.VMA s3, a0

0x0000
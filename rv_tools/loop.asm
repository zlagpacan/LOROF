@0000

lui x1, x1, 0x00002
addi x1, x1, -4
addi x2, x2, 4
addi x3, x3, 1
bne x2, x1, -8
sw x2, 0x100(zero)
ecall
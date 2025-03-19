# bru_pipeline
- Branch Resolution Unit Pipeline
- backend functional unit for conditional branch, unconditional jump, and LUI and AUIPC operations
    - see [Targeted Instructions](#targeted-instructions)
    - see [core_basics.md](../../basics/core_basics.md) for the basic purpose of a functional unit in the backend of the core


# RTL Diagram
![bru_pipeline](bru_pipeline_rtl.png)


# Parameters


# Interfaces


# Pipeline Stages


# Example Operation

see [bru_pipeline_example.md](bru_pipeline_example.md)


# Assertions


# Test Ideas and Coverpoints


# Targeted Instructions

### Branches
- BEQ
    - issue_op = 4'b1000
- BNE
    - issue_op = 4'b1001
- BLT
    - issue_op = 4'b1100
- BGE
    - issue_op = 4'b1101
- BLTU
    - issue_op = 4'b1110
- BGEU
    - issue_op = 4'b1111

### Compressed Branches
- C.BEQZ
    - issue_op = 4'b1010
- C.BNEZ
    - issue_op = 4'b1011

### Jumps
- JAL
    - issue_op = 4'b0010
- JALR
    - issue_op = 4'b0000

### Compressed Jumps
- C.JAL
    - issue_op = 4'b0011
- C.J
    - issue_op = 4'b0100
- C.JR
    - issue_op = 4'b0101
- C.JALR
    - issue_op = 4'b0001

### U-Type
- LUI
    - issue_op = 4'b0110
- AUIPC
    - issue_op = 4'b0111

### Compressed U-Type
- C.LUI
    - issue_op = 4'b0110
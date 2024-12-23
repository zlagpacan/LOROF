# alu_pipeline
- backend pipeline for ALU operations
- accepts ALU ops from ALU Issue Queue, waiting for operands to be ready via forwarding or register reads from the Physical Register File, or immediates from the ALU Issue Queue
- bandwidth of 1 ALU op per cycle
- stalls when required operands not all ready

## RTL Diagram:
![alu_pipeline RTL Diagram](alu_pipeline_rtl.png)

## Interfaces:
- ALU op issue from ALU IQ
- reg read info and data from PRF
- forward data from PRF
- ready feedback to ALU IQ
- writeback data to PRF

## Pipeline Stages:

### Operand Collection (OC)
- 

### Execute (EX)
- 

### Writeback (WB)
- 

## Supported ops:
- 4'b0000: Out = A + B
- 4'b0001: Out = A << B[4:0]
- 4'b0010: Out = signed(A) < signed(B)
- 4'b0011: Out = A < B
- 4'b0100: Out = A ^ B
- 4'b0101: Out = A >> B[4:0]
- 4'b0110: Out = A | B
- 4'b0111: Out = A & B
- 4'b1000: Out = A - B
- 4'b1101: Out = signed(A) >>> B[4:0]
- 4'b1111: Out = B

## Targeted Instructions:
- LUI
    - op_in = 4'b1111
    - A_unneeded_in = 1
    - is_imm_in = 1
- ADDI
    - op_in = 4'b0000
    - is_imm_in = 1
- SLTI
    - op_in = 4'b0010
    - is_imm_in = 1
- SLTIU
    - op_in = 4'b0011
    - is_imm_in = 1
- XORI
    - op_in = 4'b0100
    - is_imm_in = 1
- ORI
    - op_in = 4'b0110
    - is_imm_in = 1
- ANDI
    - op_in = 4'b0111
    - is_imm_in = 1
- SLLI
    - op_in = 4'b0001
    - is_imm_in = 1
- SRLI
    - op_in = 4'b0101
    - is_imm_in = 1
- SRAI
    - op_in = 4'b1101
    - is_imm_in = 1
- ADD
    - op_in = 4'b0000
- SUB
    - op_in = 4'b1000
- SLL
    - op_in = 4'b0001
- SLT
    - op_in = 4'b0010
- SLTU
    - op_in = 4'b0011
- XOR
    - op_in = 4'b0100
- SRL
    - op_in = 4'b0101
- SRA
    - op_in = 4'b1101
- OR
    - op_in = 4'b0110
- AND
    - op_in = 4'b0111

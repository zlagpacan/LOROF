# alu
- Arithmetic and Logic Unit
- fully-combinational
- 32-bit
- 2 operands
- no flags

<img src="alu_rtl.png" alt="alu RTL Diagram" width="300">

## IO
- op
    - [3:0]
    - see [Supported Ops](#supported-ops)

- A
    - [31:0]
    - first 32-bit operand

- B
    - [31:0]
    - second 32-bit operand

- out
    - [31:0]
    - 32-bit output

## Supported Ops
- 4'b0000: out = A + B
- 4'b0001: out = A << B[4:0]
- 4'b0010: out = signed(A) < signed(B) ? 1 : 0
- 4'b0011: out = unsigned(A) < unsigned(B) ? 1 : 0
- 4'b0100: out = A ^ B
- 4'b0101: out = A >> B[4:0]
- 4'b0110: out = A | B
- 4'b0111: out = A & B
- 4'b1000: out = A - B
- 4'b1001: out = A << B[4:0]
- 4'b1010: out = signed(A) < signed(B) ? 1 : 0
- 4'b1011: out = unsigned(A) < unsigned(B) ? 1 : 0
- 4'b1100: out = A ^ B
- 4'b1101: out = signed(A) >>> B[4:0]
- 4'b1110: out = A | B
- 4'b1111: out = A & B
# alu_pipeline
- backend pipeline for ALU operations
- bandwidth of up to 1 ALU op executed per cycle
- up to 1 issued ALU op accepted per cycle
- accepts ALU ops from ALU Issue Queue, waiting for operands to be ready via forwarding or register reads from the Physical Register File, or immediates from the ALU Issue Queue
- stalls when required operands not all ready
    - only OC Stage is stalled
    - EX and WB Stages of pipeline are always guaranteed to continue forward

## RTL Diagram
![alu_pipeline RTL Diagram](alu_pipeline_rtl.png)

## Interfaces
- these signals are interdependent on functionality described in [Operand Collection (OC) Stage](#operand-collection-oc)

### ALU op issue from ALU IQ
- valid_in
    - indicate that there is a new op issuing from the ALU IQ for this pipeline to accept
    - ignore the incoming op issue even if this signal is high if OC stage is stalled on a valid op
        - essentially, ignore if ready_out is low
- op_in
    - see [Supported Ops](#supported-ops)
- is_imm_in
    - indicate if op should use the immediate data value for operand B
- imm_in
    - immediate data value
- A_unneeded_in
    - indicate if op does not require operand A (and so does not need to wait for it to be ready)
- A_forward_in
    - indicate if operand A should take the forward data on the next cycle
- A_bank_in
    - indicate which bank operand A should take its forward or reg data from
- B_forward_in
    - indicate if operand B should take the forward data on the next cycle
- B_bank_in
    - indicate which bank operand B should take its forward or reg data from
- dest_PR_in
    - indicate which Physical Register to writeback to

### reg read info and data from PRF
- A_reg_read_valid_in
    - indicate if op should use the current reg read data this cycle for operand A
        - whether an op is waiting on this signal can be inferred by operand being needed/not immediate and not being forwarded
        - this can be valid at earliest on the cycle after the op is issued and the pipeline is ready
            - essentially, at earliest on the cycle the op first enters Operand Collection stage
        - this can be valid at latest after any delay
- B_reg_read_valid_in
    - indicate if op should use the current reg read data this cycle for operand B
- reg_read_data_by_bank_in
    - reg read data values for each bank
    - select data value of interest using previous A_bank_in/B_bank_in value

### forward data from PRF
- forward_data_by_bank_in
    - forward data values for each bank
    - select data value of interest using previous A_bank_in/B_bank_in value

### ready feedback to ALU IQ
- ready_out
    - indicate that pipeline is ready for a new op to be issued into it
    - this is true if the OC Stage does not have an op or the op is not stalled
    - ON RESET: 1'b1

### writeback data to PRF
- WB_valid_out
    - indicate if writeback is to be performed
    - this should be high for as many cycles as valid ops issued into the pipeline
    - ON RESET: 1'b0
- WB_data_out
    - writeback data value to write
    - ON RESET: 32'h0
- WB_PR_out
    - Physical Register to writeback data value to
    - ON RESET: 6'h0

## Pipeline Stages

### Operand Collection (OC)
- collect operand data values
- track which operands have been collected
- determine if pipeline needs to stall (valid op, operands not ready)
    - operand A ready conditions (stimulus guarantees to be mutually exclusive):
        - operand not needed
        - have saved value
            - from previous cycle forwarded value or reg read value
        - have forwarded value
            - on this cycle
                - previous cycle during issue input, was told to collect value
        - have reg read value
            - on this cycle
    - operand B ready conditions (stimulus guarantees to be mutually exclusive)
        - operand is immediate
        - have saved value
        - have forwarded value
        - have reg read value
    - on a stall, the operands collected on the cycle of interest where the operands are valid must be saved
        - signals like A_reg_read_valid_in + reg_read_data_by_bank_in are allowed to change after the cycle A_reg_read_valid_in is high
    - if there is no stall, pipeline can accept next new op from IQ (if valid)
    - essentially, the pipeline stalls whenever there is an operand that must come from a reg read, and the associated reg read has not been triggered yet
- determine if pipeline is ready for new op (invalid op or operands ready)

### Execute (EX)
- perform ALU op on A and B operands
- pass on if op is valid
- valid op here if had valid op in OC stage which had operands ready on the previous cycle

### Writeback (WB)
- present ALU op output info to writeback if op is valid
- valid op here if had valid op in EX stage on the previous cycle

## Supported Ops
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

## Targeted Instructions
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

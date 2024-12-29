# alu_iq
- backend issue queue for ALU operations
- bandwidth of up to 1 ALU op issued per cycle
- up to 4 dispatched ALU ops accepted per cycle
- accepts dispatched ALU ops from Frontend, waiting for operands values to be ready or forwardable
- on a given cycle, the oldest ALU op with ready or forwardable operands is launched to the ALU pipeline if the pipeline is ready
- watches the writeback bus and uses dispatch info to determine when operands are ready or forwardable

## RTL Diagram
![alu_iq RTL Diagram](alu_iq_rtl.png)

## Interfaces

### ALU op dispatch by entry
- dispatch_valid_by_entry
    - indicate that there is a new op dispatching from the Frontend for this issue queue to accept
    - indexed by IQ entry
    - IDLE VALUE: {1'b0, 1'b0, 1'b0, 1'b0}
- dispatch_op_by_entry
    - see [Supported Ops](#supported-ops)
    - essentially a pass-through value to the output of the issue queue
    - indexed by IQ entry
    - IDLE VALUE: {4'bx, 4'bx, 4'bx, 4'bx}
- dispatch_imm_by_entry
    - immediate data value
    - essentially a pass-through value to the output of the issue queue
    - indexed by IQ entry
    - IDLE VALUE: {32'hx, 32'hx, 32'hx, 32'hx}
- dispatch_A_PR_by_entry
    - indicate which physical register operand A uses
    - indexed by IQ entry 
    - IDLE VALUE: {6'hx, 6'hx, 6'hx, 6'hx}
- dispatch_A_unneeded_by_entry
    - indicate if op does not require operand A (and so does not need to wait for it to be ready)
    - indexed by IQ entry
    - IDLE VALUE: {1'bx, 1'bx, 1'bx, 1'bx}
- dispatch_A_ready_by_entry
    - indicate if operand A is ready for register read
    - indexed by IQ entry
    - IDLE VALUE: {1'bx, 1'bx, 1'bx, 1'bx}
- dispatch_B_PR_by_entry
    - indicate which physical register operand B uses
    - indexed by IQ entry
    - IDLE VALUE: {6'hx, 6'hx, 6'hx, 6'hx}
- dispatch_is_imm_by_entry
    - indicate if op should use the immediate data value for operand B (and so does not need to wait for the operand B register to be ready)
    - IDLE VALUE: {1'bx, 1'bx, 1'bx, 1'bx}
- dispatch_B_ready_by_entry
    - indicate if operand B is ready for register read
    - indexed by IQ entry
    - IDLE VALUE: {1'bx, 1'bx, 1'bx, 1'bx}
- dispatch_dest_PR_by_entry
    - indicate which physical register to writeback to
    - essentially a pass-through value to the output of the issue queue
    - indexed by IQ entry
    - IDLE VALUE: {6'hx, 6'hx, 6'hx, 6'hx}
- dispatch_ROB_index_by_entry
    - indicate which ROB index to set as complete
    - essentially a pass-through value to the output of the issue queue
    - IDLE VALUE: {6'hx, 6'hx, 6'hx, 6'hx}

### ALU op dispatch feedback by entry
- dispatch_open_by_entry
    - indicate which issue queue entries are open for dispatch
    - indexed by IQ entry
    - RESET VALUE: 4'b1111

### ALU pipeline feedback
- pipeline_ready
    - indicate that pipeline is ready for a new op to be issued into it
    - IDLE VALUE: 1'b1

### writeback bus
- WB_valid_by_bank
    - indicate that writeback is being performed on the associated bank
        - a writeback indicates that the value is available for forwarding on the next cycle. an op is a contender for issue if its operands are all ready or forwardable on the next cycle.
        - if an op cannot be issued on this cycle but it sees an operand PR writeback, then the operand's status becomes ready
    - IDLE VALUE: 4'b0000
- WB_upper_PR_by_bank
    - indicate the upper PR bits which writeback is being performed on by the associated bank
        - PR's are identified by 6 bits
        - there are 4 banks, and the 2 lowest bits of a PR indicate the bank it belongs to
        - a PR can be uniquely identified as being written back to by going to the bank it belongs to and checking waiting for the associated upper 4 bits to receive a writeback
    - simultaneous writeback is allowed for different PR's if there are no bank conflicts
    - IDLE VALUE: {4'x, 4'x, 4'x, 4'x}

### ALU op issue to ALU pipeline
- issue_valid
    - indicate that an op is being issued into the ALU pipeline
    - if issue_valid is low, the remaining signals in this "ALU op issue to ALU pipeline" interface are don't-cares. this implementation chooses the values from issue queue entry 0
    - RESET VALUE: 1'b0
- issue_op
    - see [Supported Ops](#supported-ops)
    - RESET VALUE: 4'b0000
- issue_is_imm
    - indicate if op should use the immediate data value for operand B
    - RESET VALUE: 1'b0
- issue_imm
    - immediate data value
    - RESET VALUE: 32'h0
- issue_A_unneeded
    - indicate if op does not require operand A (and so does not need to wait for it to be ready)
    - RESET VALUE: 1'b0
- issue_A_forward
    - indicate if operand A should take the forward data on the next cycle
    - RESET VALUE: 1'b0
- issue_A_bank
    - indicate which bank operand A should take its forward or reg data from
    - RESET VALUE: 2'h0
- issue_B_forward
    - indicate if operand B should take the forward data on the next cycle
    - RESET VALUE: 1'b0
- issue_B_bank
    - indicate which bank operand B should take its forward or reg data from
    - RESET VALUE: 2'h0
- issue_dest_PR
    - indicate which Physical Register to writeback to
    - RESET VALUE: 6'h0
- issue_ROB_index
    - indicate which ROB index to set as complete
    - RESET VALUE: 6'h0

### reg read req to PRF
- PRF_req_A_valid
    - indicate request to PRF to read operand A
    - RESET VALUE: 1'b0
- PRF_req_A_PR
    - operand A physical register
    - RESET VALUE: 6'h0
- PRF_req_B_valid
    - indicate request to PRF to read operand B
    - RESET VALUE: 1'b0
- PRF_req_B_PR
    - operand B physical register
    - RESET VALUE: 6'h0

## Issue Queue Entries
- Frontend dispatch is responsible for dispatching valid ops into this issue queue from the oldest/closest to 0 open/invalid entry first, as advertised by dispatch_open_by_entry
- This issue queue is responsible for maintaining a contiguous order of valid ops from oldest to youngest, starting from entry 0, whilst entries are issued out of the issue queue cycle by cycle, one at a time
- Issue queue entries track if their ops are contenders for issue, when all of their operands are either unneeded, an immediate, ready, or forwardable next cycle.

## Example Operation

### Cycle 0
<!-- ![alu_iq Cycle 0 Diagram](alu_iq_cycle_0.png) -->
<img src="alu_iq_cycle_0.png" alt="alu_iq Cycle 0 Diagram" width="600">

- all issue queue entries are empty/invalid
- no ops are being dispatched
- no op is being issued as none are valid
- since all issue queue entries are empty, all entries are open for dispatch. externally, the Frontend has decided not to dispatch any ops.

### Cycle 1
<!-- ![alu_iq Cycle 1 Diagram](alu_iq_cycle_1.png) -->
<img src="alu_iq_cycle_1.png" alt="alu_iq Cycle 1 Diagram" width="600">

- all issue queue entries are empty/invalid
- 3 ops are being dispatched, the oldest to entry 0 (ADD), the second oldest to entry 1 (SLTI), and the youngest to entry 2 (SRL)
- no op is being issued as none are valid
- since all issue queue entries are empty, all entries are open for dispatch. externally, the Frontend has decided to dispatch 3 ops, which must be at the oldest 3 entries, 0:2. 

### Cycle 2
<!-- ![alu_iq Cycle 2 Diagram](alu_iq_cycle_2.png) -->
<img src="alu_iq_cycle_2.png" alt="alu_iq Cycle 2 Diagram" width="600">

- issue queue entries 0:2 are valid
    - issue queue entry 0 (ADD) has p2 not ready, so it is NOT a contender to be issued
    - issue queue entry 1 (SLTI) has p4 ready and an imm, so it is a contender to be issued
    - issue queue entry 2 (SRL) has p7 not ready, so it is NOT a contender to be issued
- the op in entry 1 (SLTI) is being issued as it is the oldest (and only) contender which can be issued. this op requires a reg read for p4.
    - issue queue entry 2 will be shifted to entry 1
- 1 op (ORI) is being dispatched to entry 2, which is the oldest available entry open as advertised by dispatch_open_by_entry. The Frontend could have chosen to also dispatch into entry 3 but did not. 

### Cycle 3
<!-- ![alu_iq Cycle 3 Diagram](alu_iq_cycle_3.png) -->
<img src="alu_iq_cycle_3.png" alt="alu_iq Cycle 3 Diagram" width="600">

- issue queue entries 0:2 are valid
    - issue queue entry 0 (ADD) has p2 not ready, so it is NOT a contender to be issued
    - issue queue entry 1 (SRL) has p7 not ready, so it is NOT a contender to be issued
    - issue queue entry 2 (ORI) has p9 not ready, so it is NOT a contender to be issued
- no op is being issued as there are no contenders which can be issued. 
- 1 op (SUB) is being dispatched to entry 3, which is the oldest and only available entry open as advertised by dispatch_open_by_entry

### Cycle 4
<!-- ![alu_iq Cycle 4 Diagram](alu_iq_cycle_4.png) -->
<img src="alu_iq_cycle_4.png" alt="alu_iq Cycle 4 Diagram" width="600">

- issue queue entries 0:3 are valid
    - issue queue entry 0 (ADD) has p2 not ready, so it is NOT a contender to be issued
    - issue queue entry 1 (SRL) has p7 not ready, so it is NOT a contender to be issued
    - issue queue entry 2 (ORI) has p9 not ready, so it is NOT a contender to be issued
    - issue queue entry 3 (SUB) has p11 and p12 ready, so it is a contender to be issued
- no op is being issued as even though there is at least one contender, pipeline_ready = 1'b0 indicates that the pipeline is not ready for an op issue.
- no ops can be dispatched as there are no available issue queue entries, as advertised by dispatch_open_by_entry

### Cycle 5
<!-- ![alu_iq Cycle 5 Diagram](alu_iq_cycle_5.png) -->
<img src="alu_iq_cycle_5.png" alt="alu_iq Cycle 5 Diagram" width="600">

- issue queue entries 0:3 are valid
    - issue queue entry 0 (ADD) has p1 ready and p2 forwardable as there is a p2 writeback, so it is a contender to be issued
    - issue queue entry 1 (SRL) has p7 not ready, so it is NOT a contender to be issued
    - issue queue entry 2 (ORI) has p9 forwardable as there is a p9 writeback, so it is a contender to be issued
    - issue queue entry 3 (SUB) has p11 and p12 ready, so it is a contender to be issued
- the op in entry 0 (ADD) is being issued as it is the oldest contender which can be issued. this op requires a reg read for p1 but p2 can be forwarded.
    - issue queue entry 1 will be shifted to entry 0
    - issue queue entry 2 will be shifted to entry 1
        - p9 was forwardable so it will become ready
    - issue queue entry 3 will be shifted to entry 2
- no op is being dispatched by the Frontend but issue queue entry 3 is available for dispatch as advertised by dispatch_open_by_entry

### Cycle 6
<!-- ![alu_iq Cycle 6 Diagram](alu_iq_cycle_6.png) -->
<img src="alu_iq_cycle_6.png" alt="alu_iq Cycle 6 Diagram" width="600">

- issue queue entries 0:2 are valid
    - issue queue entry 0 (SRL) has p7 not ready, so it is NOT a contender to be issued
    - issue queue entry 1 (ORI) has p9 ready and imm, so it is a contender to be issued
        - p9 became ready on the last cycle when there was a p9 writeback but this op wasn't issued
    - issue queue entry 2 (SUB) has p11 and p12 ready, so it is a contender to be issued
- the op in entry 1 (ORI) is being issued as it is the oldest contender which can be issued. this op requires a reg read for p9.
    - issue queue entry 2 will be shifted to entry 1
- no op is being dispatched by the Frontend but issue queue entries 2:3 are available for dispatch as advertised by dispatch_open_by_entry

### Cycle 7
<!-- ![alu_iq Cycle 7 Diagram](alu_iq_cycle_7.png) -->
<img src="alu_iq_cycle_7.png" alt="alu_iq Cycle 7 Diagram" width="600">

- issue queue entries 0:1 are valid
    - issue queue entry 0 (SRL) has p7 not ready, so it is NOT a contender to be issued
    - issue queue entry 1 (SUB) has p11 and p12 ready, so it is a contender to be issued
- the op in entry 1 (SUB) is being issued as it is the oldest (and only) contender which can be issued. this op requires a reg read for p11 and p12.
- no op is being dispatched by the Frontend but issue queue entries 1:3 are available for dispatch as advertised by dispatch_open_by_entry

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

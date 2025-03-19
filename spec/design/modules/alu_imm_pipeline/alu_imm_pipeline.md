# alu_imm_pipeline
- backend functional unit for ALU register-immediate operations
    - R[dest] <= R[A] op imm
        - see [Targeted Instructions](#targeted-instructions)
    - see [core_basics.md](../../basics/core_basics.md) for the basic purpose of a functional unit in the backend of the core
- example operation: [alu_imm_pipeline_example.md](alu_imm_pipeline_example.md)
- receives issued ALU imm operations, collects the register operand data value, performs the ALU operation, and writes the data back to the PRF
- pipelined with issue, operand collection, execute, and writeback stages
- bandwidth of up to 1 ALU op executed per cycle
    - maintained as long as:
        - operands are immediately gathered on the first cycle in OC stage. see [Operand Collection (OC) Stage](#operand-collection-oc-stage)
        - the PRF is always ready for writeback
        - new ALU ops continue to be issued
- utilizes alu module. see [alu.md](../alu/alu.md)
- operands can be collected through PRF register read responses or forwarded data
    - PRF register read requests were previously initiated by the issue queue. the pipeline's job is to simply collect the register values when they arrive
- operand A is needed for all ops in this pipeline
- the term "op" will be used throughout this spec to describe the unique valid collection of data that flows through the pipeline, inhabiting a single pipeline stage a time, starting from a cycle where issue_valid = 1'b1 and issue_ready = 1'b0. this term "op" is analagous to a unique instruction flowing through a classic in-order 5-stage CPU pipeline


# RTL Diagram
![alu_pipeline RTL Diagram](alu_imm_pipeline_rtl.png)


# Parameters

## Variable Parameters
- none

## Constant Parameters
All of these are constants from core_types_pkg.vh
- LOG_PR_COUNT = 7
- LOG_ROB_ENTRIES = 7
- PRF_BANK_COUNT = 4
- LOG_PRF_BANK_COUNT = 2


# Interfaces
Input interfaces blue. Output interfaces green.
These signals make more sense in combination with the information in the [Pipeline Stages](#pipeline-stages) section.

<span style="color:orange">

## seq

</span>

This is a sequential module utilizing posedge flip flops

- CLK
    - input logic
    - clock signal
- nRST
    - input logic
    - active-low asynchronous reset
    - the entire module state can be reset after a single asynchronous assertion

<span style="color:deepskyblue">

## ALU imm op issue from IQ

</span>

input interface

- issue_valid
    - input logic
    - indicate that an ALU imm op is being issued this cycle
        - or is at least being attempted
    - a valid issue is ignored if issue_ready = 1'b0
        - i.e. the OC stage will stall with its current op instead of accepting the new issue op
    - constraints:
        - utilize as control signal to indicate an issue attempt
    - idle value:
        - 1'b0
- issue_op
    - input logic [3:0]
    - 4-bit op to apply on operands A and imm to create the WB data value
    - this directly translates to the ops used by the alu module. see [alu.md](../alu/alu.md)
    - constraints:
        - none
    - idle value:
        - 4'hx
- issue_imm12
    - input logic [11:0]
    - 12-bit immediate which will be sign extended to 32-bits and used as the second operand in the ALU operation
    - constraints:
        - none
    - idle value:
        - 12'hx
- issue_A_forward
    - input logic
    - == 1'b1:
        - indicate that operand A's data should be collected from the forward data bus on the next cycle when the op is in the OC stage
        - when the op enters OC stage, it utilizes the issue_A_bank signal to select which forward data bus bank to select from
    - == 1'b0:
        - indicate that operand A's data should be collected from a reg read from the PRF when the op is in the OC stage
            - this data can come at the cycle the op first enters OC stage or any cycle after
        - when the op enters OC stage, it utilizes the A_reg_read_ack to know that its reg read data is available, and utilizes A_reg_read_port and previous issue_A_bank to select the data of interest from reg_read_data_by_bank_by_port
    - constraints:
        none
    - idle value:
        - 1'bx
- issue_A_is_zero
    - input logic
    - == 1'b1:
        - indicate that operand A's data should be a 32-bit zero
        - the 32-bit zero operand is always ready in OC stage and does not need to wait on nor be collected via any external signals
    - == 1'b0:
        - follow behavior denoted by issue_A_forward
    - essentially issue_A_is_zero overrides and has priority over issue_A_forward
    - constraints:
        - none
    - idle value:
        - 1'bx
- issue_A_bank
    - input logic [1:0]
        - design uses: input logic [LOG_PRF_BANK_COUNT-1:0]
    - indicate which bank {0, 1, 2, 3} to be used for operand A when collecting data in the OC stage
    - constraints:
        - none
    - idle value:
        - 1'bx
- issue_dest_PR
    - input logic [6:0]
        - design uses: input logic [LOG_PR_COUNT-1:0]
    - indicate which Physical Register [7'h0, 7'h7F] to writeback to in WB stage
    - essentially acts as a pass-through to be assigned to WB_PR when the op arrives in WB stage
    - constraints:
        - none
    - idle value:
        - 7'hx
- issue_ROB_index
    - input logic [6:0]
        - design uses: input logic [LOG_ROB_ENTRIES-1:0]
    - indicate which ROB index [7'h0, 7'h7F] to mark as complete in WB stage
    - essentially acts as a pass-through to be assigned to WB_ROB_index when the op arrives in WB stage
    - constraints:
        - none
    - idle value:
        - 7'hx

<span style="color:chartreuse">

## ready feedback to IQ

</span>

output interface

- issue_ready
    - output logic
    - indicate that the pipeline is not ready for a new op issue
    - must be 1'b0 when there is a valid op in OC stage which does not have operand A either saved from a previous cycle, forwarded this cycle, or arrived through a reg read ack this cycle OR the OC stage is stalled
    - see [Operand Collection (OC) Stage](#operand-collection-oc-stage)
    - reset value:
        - 1'b1

<span style="color:deepskyblue">

## reg read info and data from PRF

</span>

input interface

- A_reg_read_ack
    - input logic
    - acknowledgement signal indicating that operand A's reg read data is available this cycle
    - the OC stage 
    - constraints:
        - utilize as control signal to indicate operand A reg read data is available
        - this signal should never be 1'b1 unless there is an op in OC stage waiting for a reg read for operand A
            - else, undefined behavior
            - this can be made an assertion in an integration-level testbench, where the IQ and PRF together should guarantee this condition
    - idle value:
        - 1'b0
- A_reg_read_port
    - input logic
    - indicate which port {0, 1} of reg_read_data_by_bank_by_port operand A in OC stage should grab its operand data value from when A_reg_read_ack = 1'b1
    - use in combination with the bank previously given by issue_A_bank
    - unused when A_reg_read_ack = 1'b0
    - constraints:
        - none
    - idle value:
        - 1'bx
- reg_read_data_by_bank_by_port
    - input logic [3:0][1:0][31:0]
        - design uses: input logic [PRF_BANK_COUNT-1:0][1:0][31:0]
    - collect a PRF reg read data value of interest
    - 3D array 
        - first dim: bank
            - select which bank operand A is interested in via the previous issue_A_bank signal
        - second dim: port
            - select which port operand A is interested in via the current A_reg_read_port signal
        - third dim: 32-bit operand data value
    - values in this array are ignored by the module if they don't correspond to the OC stage A bank and A_reg_read_port and A_reg_read_ack = 1'b1
    - constraints:
        - none
    - idle value:
        {4{2{32'hx}}}

<span style="color:deepskyblue">

## forward data from PRF

</span>

input interface

- forward_data_by_bank
    - input logic [3:0][31:0]
        - design uses: input logic [PRF_BANK_COUNT-1:0][31:0]
    - collect a PRF forward value of interest
    - 2D array
        - first dim: bank
            - select which bank operand A is interested in via the previous issue_A_bank signal, respectively
        - second dim: 32-bit operand data value
    - values in this array are ignored by the module if they don't correspond to the OC stage A bank and A is looking for a forward value this cycle (issue_A_forward was 1'b1 the previous cycle, when this op was issued)
    - constraints:
        - none
    - idle value:
        - {4{32'hx}}

<span style="color:chartreuse">

## writeback data to PRF

</span>

output interface

- WB_valid
    - output logic
    - indicate ALU op result should be written back to PRF
    - this coincides with there being a valid op in WB stage as all valid ALU ops write back
    - reset value:
        - 1'b0
- WB_data
    - output logic [31:0]
    - 32-bit ALU op result data to be written back to PRF
    - = R[A] op imm
    - don't care when WB_valid = 1'b0
    - reset value:
        - 32'h0
- WB_PR
    - output logic [6:0]
        - design uses: output logic [LOG_PR_COUNT-1:0]
    - indicate which Physical Register [7'h0, 7'h7F] to write back to
    - final passed-through value initially given on issue_dest_PR
    - don't care when WB_valid = 1'b0
    - reset value:
        - 7'h0
- WB_ROB_index
    - output logic [6:0]
        - design uses: output logic [LOG_ROB_ENTRIES-1:0]
    - indicate which ROB index [7'h0, 7'h7F] to mark as complete
    - final passed-through value initially given on issue_ROB_index
    - don't care when WB_valid = 1'b0
    - reset value:
        - 7'h0

<span style="color:deepskyblue">

## writeback feedback from PRF

</span>

input interface

- WB_ready
    - input logic
    - indicate that WB stage needs to stall
    - internal pipeline logic determines how far this stall should propagate backward
    - constraints:
        - utilize as control signal to indicate WB stage should stall
    - idle value:
        - 1'b1


# Pipeline Stages
unique "ops" flow through the pipeline stages in-order from issue to writeback following typical pipeline rules. 
- on reset, the pipeline starts with all stages invalid. 
- valid ops enter the pipeline in IS stage via the [ALU imm op issue from IQ](#alu-reg-op-issue-from-iq) interface as long as issue_ready = 1'b1. 
- the pipeline stages individually move forward when possible, and stall if necessary
- stall conditions propagate backward where relevant. e.g. there is no need to propagate a stall backward before a pipeline bubble (stage where op is not valid). 
- see the stall conditions by stage below, where X stage valid means there is an op in X stage.

## Issue (IS) Stage
Accept new instruction issue via the [ALU imm op issue from IQ](#alu-reg-op-issue-from-iq) interface if the OC stage is signaled to be ready via the issue_ready signal. 

#### Stall Condition
- stall together with OC stage based on issue_ready
- here, stall means [ALU imm op issue from IQ](#alu-reg-op-issue-from-iq) interface is ignored

## Operand Collection (OC) Stage
Collect A operand. If operand A isn't collected (from this cycle or a previous cycle) then OC stage must stall and the issue_ready signal must be 1'b0. A bubble (invalid and all other signals don't cares) is naturally inserted into this stage whenever issue_ready = 1'b1 but issue_valid = 1'b0. 

Potential operand states:
- "forwarding"
    - data is being forwarded on this cycle
    - (issue_ready & issue_valid & issue_A/B_forward) last cycle when this op was issued
    - take data from forward_data_by_bank
- "reg reading"
    - data is being read via the PRF on this cycle
    - (~issue_A/B_forward) when this op was issued, A/B_reg_read_ack on this cycle, sample value from reg_read_data_by_bank_by_port
        - can be an arbitrary number of cycles in the past when the op was issued
        - since this issue cycle, the op had to have either just entered OC stage or been stalled in OC stage as it had an operand which wasn't ready
- "saved"
    - data was saved from a previous cycle
    - data for operand was collected via the operand being in "forwarding" or "reading reg" on a previous cycle with a stall condition
- "waiting"
    - data is not available this cycle and was not saved on a previous cycle
    - this creates an operand stall
- "is zero"
    - data is 32-bit zero to be generated in pipeline on this cycle

#### Stall Condition:
- valid op in EX stage and either:
    - operand A or B in "waiting" state on this cycle
    - EX stage stall and OC stage valid
- a stall in this stage corresponds to issue_ready = 1'b0

### OC Truth Table:
This truth table essentially enumerates all the possible combinations of operand states as achieved by different IS stage inputs, combined with or without propagated WB stall, telling whether an operand stall OC stage stall occurs and what behavior the OC stage op should take

| Description | issue_A_forward on Issue Cycle | A_reg_read_ack on This Cycle | issue_A_is_zero on Issue Cycle | WB Stall Propagated to OC | Operand A State | issue_ready This Cycle | Module Actions |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| issued last cycle, forward A this cycle | 1 | 0 | 0 | 0 | forwarding | 1 | continue to EX with A value from forward_data_by_bank |
| issued last cycle, forward A this cycle, WB stall | 1 | 0 | 0 | 1 | forwarding | 0 | stall due to WB, save A value from forward_data_by_bank |
| issued in any previous cycle, A reg read ack this cycle | 0 | 1 | 0 | 0 | reg reading | 1 | continue to EX with A value from reg_read_data_by_bank_by_port |
| issued in any previous cycle, A reg read ack this cycle, WB stall | 0 | 1 | 0 | 1 | reg reading | 0 | stall due to WB, save A value from reg_read_data_by_bank_by_port |
| issued in any previous cycle, A saved | 0 | 0 | 0 | 0 | saved | 1 | continue to EX with A saved value |
| issued in any previous cycle, A saved, WB stall | 0 | 0 | 0 | 1 | saved | 0 | stall due to WB |
| issued in any previous cycle, A is zero | x | 0 | 1 | 0 | is zero | 1 | continue to EX with A = 32'h0 |
| issued in any previous cycle, A is zero, WB stall | x | 0 | 1 | 1 | is zero | 0 | stall due to WB |
| issued in any previous cycle, A waiting | 0 | 0 | 0 | x | waiting | 0 | operand stall |

When OC stage does not contain a valid op, issue_ready is guaranteed to be 1'b1:
- there are no operands to collect
- a stall originating in WB stage due to WB_ready = 1'b0 which propagates back to EX stage is not propagated backward through an invalid OC stage

## Execute (EX) Stage
Perform the R[A] op imm ALU operation. A bubble (invalid and all other signals don't cares) is inserted into this stage whenever EX stage is not stalled but OC stage is stalled. 

#### Stall Condition:
- WB stage stall and EX stage valid

## Writeback (WB) Stage

#### Stall Condition:
- WB_ready = 1'b0 and WB stage valid


# Example Operation

see [alu_imm_pipeline_example.md](alu_imm_pipeline_example.md)


# Behavioral Model Ideas

### EX Stage Logic
- can just plug in the verified alu module or a predictor for the alu module to determine the results of the op

### OC Stage Operand State Logic
- follow OC stage rules and truth table in [Operand Collection (OC) Stage](#operand-collection-oc-stage)
- essentially, keep operand A and operand B states, and determine if op ready, and if not what operand state transitions to take

### Stall Logic
- this logic determines the pipeline advancement and stalls by stage
- determine what stages should stall in backwards order
    - see the stall conditions in [Pipeline Stages](#pipeline-stages)
    - maintain the known {valid, invalid} and associated op info per 
    - start with WB and EX stage, propagating the WB_ready = 1'b0 stall backwards through valid pipeline stages
    - determine the OC stage stall via the OC stage rules
        - see [OC Stage Operand State Logic](#oc-stage-operand-state-logic)
        - do WB and EX first since this logic needs to know if a WB stall has propagated to OC stage
        - this logic determines OC and IS stage stalls
    - with the stall information collected in the steps above, you can determine the operations that should be performed in each stage and the next {valid, invalid} by stage


# Assertions
- no output x's after reset
- every cycle with (WB_valid == 1'b1 && WB_ready == 1'b1) is associated with a unique previous cycle with (issue_valid == 1'b1 && issue_ready == 1'b1)
    - num cycles with (WB_valid == 1'b1 && WB_ready == 1'b1) <= num cycles with (issue_valid == 1'b1 && issue_ready == 1'b1)
    - cycle with (WB_valid == 1'b1) can only happen at the soonest 3 cycles after the first cycle with (issue_valid == 1'b1 && issue_ready == 1'b1)


# Coverpoints
- every op
- every OC stage truth table case
    - see [OC Truth Table](#oc-truth-table)
- 2^4 possible combinations of {valid, invalid} for each of the 4 pipeline stages, all of which should be reachable
    - ideally, cover all 2^4 * 4 combinations of pipeline stages + pipeline stall
        - {valid, invalid}^4 x {no stall, WB stall, OC stall, WB and OC stall}


# Test Ideas

### Single Op of Interest at a Time in Pipeline
- target basic functionality
- target OC stage truth table coverage
- follow single op of interest through pipeline
    - IS stage cycle
        - issue op
        - issue_valid = 1'b1 with desired [ALU reg op issue from IQ](#alu-reg-op-issue-from-iq) interface signals
    - OC stage cycle(s)
        - create operand states and OC stall as desired
        - give desired [reg read info and data from PRF](#reg-read-info-and-data-from-prf) interface signals
        - give desired [forward data from PRF](#forward-data-from-prf) interface signals
        - if want to force a WB stall to propagate to OC for this op, give 2 dummy ops on previous cycles which will be in EX stage and WB stage on this cycle, along with WB_ready = 1'b0
            - if want to force this case, other ops may be in pipeline but they can be dummy ops which aren't the target of the test
        - issue_valid = 1'b0
            - no new ops
    - EX stage cycle
        - WB_ready = 1'b1
            - pass op and any dummy ops to WB
        - issue_valid = 1'b0
            - no new ops
    - WB stage cycle
        - WB_ready = 1'b1
            - finish WB
        - check [writeback data to PRF](#writeback-data-to-prf) interface signals
        - issue_valid = 1'b0
            - no new ops
    - on next cycle, can start next op of interest in IS stage
- repeat single op (+ any dummy ops) sequence through pipeline for as many ops as needed to achieve coverage

### Steady State Operation
- target op coverage
- after fill and before drain, all pipeline stages valid
- always issue
    - (issue_valid == 1'b1)
- WB always ready
    - (WB_ready == 1'b1)
- operands always collected on-time
    - for operand A, any of:
        - (issue_A_is_zero == 1'b1) when op in IS stage
        - (issue_A_forward == 1'b1) when op in IS stage
        - (issue_A_forward == 1'b0) when op in IS stage and (A_reg_read_ack == 1'b1) when op in OC stage

### Stall Insertions
- target coverage of {valid, invalid} combinations for each pipeline stage
    - as described in [Coverpoints](#coverpoints), ideally combinations of {valid, invalid}^4 x {no stall, WB stall, OC stall, WB and OC stall}
- insert various stalls:
    - no issue
        - (issue_valid == 1'b0) for op in IS stage
            - so essentially no new op given to the pipeline
    - WB stalls
        - (WB_ready == 1'b0)
            - affect of this can vary depending on which pipeline stages are valid, and therefore how far the stall is allowed to propagate
    - operand stalls
        - (issue_A_forward == 1'b0) when op in IS stage and (A_reg_read_ack == 1'b0) when op in OC stage
- dynamically follow stall condition rules in behavioral model to determine how pipeline stages should advance and determine on what {valid, invalid} pipeline stage combinations have been reached


# Targeted Instructions

### ALU Reg-Imm
- ADDI
    - issue_op = 4'b0000
- SLLI
    - issue_op = 4'b0001
- SLTI
    - issue_op = 4'b0010
- SLTIU
    - issue_op = 4'b0011
- XORI
    - issue_op = 4'b0100
- SRLI
    - issue_op = 4'b0101
- SRAI
    - issue_op = 4'b1101
- ORI
    - issue_op = 4'b0110
- ANDI
    - issue_op = 4'b0111

### Compressed ALU Reg-Imm
- C.ADDI
    - issue_op = 4'b0000
- C.LI
    - issue_op = 4'b0000
- C.ADDI16SP
    - issue_op = 4'b0000
- C.ADDI4SPN
    - issue_op = 4'b0000
- C.NOP
    - issue_op = 4'b0000
- C.SLLI
    - issue_op = 4'b0001
- C.SRLI
    - issue_op = 4'b0101
- C.SRAI
    - issue_op = 4'b1101
- C.ANDI
    - issue_op = 4'b0111
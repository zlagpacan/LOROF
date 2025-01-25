# alu_reg_pipeline
- backend functional unit for ALU register-register operations
    - R[A] op R[B]
    - see [core_basics.md](../basics/core_basics.md) for the basic purpose of a functional unit in the backend of the core
- receives issued ALU reg operations, collects the register operand data values, performs the ALU operations, and writes the data back to the PRF
- pipelined with issue, operand collection, execute, and writeback stages
- bandwidth of up to 1 ALU op executed per cycle
    - maintained as long as:
        - operands are immediately gathered on the first cycle in OC stage. see [Operand Collection (OC) Stage](#operand-collection-oc-stage)
        - the PRF is always ready for writeback
        - new ALU ops continue to be issued
- utilizes alu module. see [alu.md](../alu/alu.md)
- operands can be collected through PRF register read responses or forwarded data
    - PRF register read requests were previously initiated by the issue queue. the pipeline's job is to simply collect the register values when they arrive
- operands A and B are needed for all ops in this pipeline
- the term "op" will be used throughout this spec to describe the collection of data that flows through the pipeline, inhabiting a single pipeline stage a time, starting from a cycle where issue_valid = 1'b1 and issue_ready = 1'b0. this term "op" is analagous to an instruction flowing through a simple in-order 5-stage CPU pipeline


# RTL Diagram
![alu_pipeline RTL Diagram](alu_reg_pipeline.png)


# Interfaces
These signals make more sense in combination with the information in the [Pipeline Stages](#pipeline-stages) section.

## seq
This is a sequential module utilizing posedge flip flops

- CLK
    - clock signal
- nRST
    - active-low asynchronous reset

## ALU op issue from IQ
input interface

- issue_valid
    - input logic
    - indicate that an ALU reg op is being issued this cycle
        - or is at least being attempted
    - a valid issue is ignored if issue_ready = 1'b0
        - i.e. the OC stage will stall with its current op instead of accepting the new issue op
    - constraints:
        - utilize as control signal to indicate an issue attempt
- issue_op
    - input logic [3:0]
    - 4-bit op to apply on operands A and B to create the WB data value
    - this directly translates to the ops used by the alu module. see [alu.md](../alu/alu.md)
    - constraints:
        - none
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
- issue_A_bank
    - input logic [1:0]
    - indicate which bank {0, 1, 2, 3} to be used for operand A when collecting data in the OC stage
    - constraints:
        - none
- issue_B_forward
    - input logic
    - same semantics as issue_A_forward but for operand B
- issue_B_bank
    - input logic [1:0]
    - same semantics as issue_A_bank but for operand B
- issue_dest_PR
    - input logic [6:0]
    - indicate which Physical Register [7'h0, 7'h7F] to writeback to in WB stage
    - essentially acts as a pass-through to be assigned to WB_PR when the op arrives in WB stage
    - constraints:
        - none
- issue_ROB_index
    - input logic [6:0]
    - indicate which ROB index [7'h0, 7'h7F] to mark as complete in WB stage
    - essentially acts as a pass-through to be assigned to WB_ROB_index when the op arrives in WB stage
    - constraints:
        - none

## ready feedback to IQ
output interface

- issue_ready
    - output logic
    - indicate that the pipeline is not ready for a new op issue
    - must be 1'b1 when there is a valid op in OC stage which does not have both of its operands A and B either saved from a previous cycle, forwarded this cycle, or arrived through a reg read ack this cycle
    - reset:
        - 1'b1

## reg read info and data from PRF
input interface

- A_reg_read_ack
    - input logic
    - acknowledgement signal indicating that operand A's reg read data is available this cycle
    - the OC stage 
    - constraints:
        - utilize as control signal to indicate operand A reg read data is available
        - this signal should never be 1'b1 unless there is an op in OC stage waiting for a reg read for operand A
            - else, undefined behavior
            - this can be made an assertion in an integration-level testbench, where the IQ and PRF together should guarantee this
- A_reg_read_port
    - input logic
    - indicate which port {0, 1} of reg_read_data_by_bank_by_port operand A in OC stage should grab its operand data value from when A_reg_read_ack = 1'b1
    - use in combination with the bank previously given by issue_A_bank
    - unused when A_reg_read_ack = 1'b0
    - constraints:
        - none
- B_reg_read_ack
    - input logic
    - same semantics as A_reg_read_ack but for operand B
- B_reg_read_port
    - input logic
    - same semantics as A_reg_read_port but for operand B
- reg_read_data_by_bank_by_port
    - input logic [1:0][1:0][31:0]
    - collect a PRF reg read data value of interest
    - 3D array 
        - first dim: bank
            - select which bank operand A/B is interested in via the previous issue_A_bank/issue_B_bank signal, respectively
        - second dim: port
            - select which port operand A/B is interested in via the current A_reg_read_port/B_reg_read_port signal, respectively
        - third dim: 32-bit operand data value
    - values in this array are ignored by the module if they don't correspond to the OC stage A/B bank and A_reg_read_port/B_reg_read_port and A_reg_read_ack/B_reg_read_ack = 1'b1
        - to be clear, the A and B operands are completely independent in their operand ack's and (bank,port) combos
    - constraints:
        - none

## forward data from PRF
input interface

- forward_data_by_bank
    - input logic [1:0][31:0]
    - collect a PRF forward value of interest
    - 2D array
        - first dim: bank
            - select which bank operand A/B is interested in via the previous issue_A_bank/issue_B_bank signal, respectively
        - second dim: 32-bit operand data value
    - values in this array are ignored by the module if they don't correspond to the OC stage A/B bank and A/B needs is looking for a forward value this cycle (issue_A_forward/issue_B_forward was 1'b1 the previous cycle, when this op was issued)
        - to be clear, the A and B operands are completely independent in their operand forwards's and banks
    - constraints:
        - none

## writeback data to PRF
output interface

- WB_valid
    - output logic
    - indicate ALU op result should be written back to PRF
    - this coincides with there being a valid op in WB stage as all valid ALU ops write back
    - reset:
        - 1'b0
- WB_data
    - output logic [31:0]
    - 32-bit ALU op result data to be written back to PRF
    - = R[A] op R[B]
    - don't care when WB_valid = 1'b0
    - reset:
        - 32'h0
- WB_PR
    - output logic [6:0]
    - indicate which Physical Register [7'h0, 7'h7F] to writeback
    - final passed-through value initially given on issue_dest_PR
    - don't care when WB_valid = 1'b0
    - reset:
        - 7'h0
- WB_ROB_index
    - output logic [6:0]
    - indicate which ROB index [7'h0, 7'h7F] to mark as complete
    - final passed-through value initially given on issue_ROB_index
    - don't care when WB_valid = 1'b0
    - reset:
        - 7'h0

## writeback feedback from PRF
input interface

- WB_ready
    - input logic
    - indicate that WB stage needs to stall
    - constraints:
        - utilize as control signal to indicate WB stage should stall


# Pipeline Stages
Unique "ops" flow through the pipeline stages in-order from issue to writeback. The pipeline moves forward when possible, stalling if necessary: PRF WB not being ready or OC stage not being ready. Stall conditions propagate backward where relevant. e.g. there is no need to propagate a stall backward before a pipeline bubble (stage where op is not valid).

## Issue (IS) Stage
Accept new instruction issue via the "ALU op issue from IQ" interface if the OC stage is signaled to be ready via the "ready feedback to IQ" interface. 

## Operand Collection (OC) Stage
- Stall Condition:

## Execute (EX) Stage
- Stall Condition:

## Writeback (WB) Stage
- Stall Condition:


# Assertions
- no output nor internal signal x's after reset


# Test Ideas and Coverpoints
- every op
- every combo of operand {A, B} x {forward, reg read first cycle in OC, reg read second or later cycle in OC}
    - these combos should automatically cover saved forward value and saved reg read value for next cycle on OC stall case where only one operand comes in
- there are 2^4 possible combinations of {valid, invalid} for each of the 4 pipeline stages, all of which should be reachable. ideally, cover all of them with {no stall, WB stall, OC stall, WB and OC stall}
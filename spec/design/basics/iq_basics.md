# Issue Queue Basics
- see [core_basics.md](core_basics.md) for how issue queues are used in an R10K out-of-order core
- see [alu_reg_mdu_iq_example.md](../modules/alu_reg_mdu_iq/alu_reg_mdu_iq_example.md) for an example issue queue in action
- see [reg_rename_basics.md](reg_rename_basics.md) for information on physical registers

issue queues hold the state of dispatched instructions, waiting for the instruction's operands to be ready, so that they can be subsequently issued to the associated FU pipeline

operands are known to be ready on dispatch either by reading a ready flag set in the physical register Ready Table, or they are determined to be newly ready via observing a writeback of the physcial register of interest on the Writeback Bus

the general policy of an issue queue is to issue the oldest instruction(s) whose operands are ready

# LOROF Issue Queues

## Properties
- multiple-dispatch into issue queue from 4-way superscalar frontend
- single-issue out of issue queue per backend pipeline
- most issue queues are in-order dispatch and out-of-order issue
    - ALU reg-reg, ALU reg-imm, branch, load, and mul/div pipelines
    - out of the set of ready instructions, the oldest is issued
    - if no instruction is ready, nothing is issued
- the store, AMO, and system/CSR pipelines require in-order dispatch and in-order issue
    - for these, only the oldest instruction can be issued
    - if the oldest instruction is not ready, nothing is issued
- forwarding is possible via observing a writeback of the physical register of interest and issuing the instruction on the same cycle, where the forwarded data can be collected on the next cycle in the FU pipeline's operand collection stage.

## Issue Queues Used

### alu_reg_mdu_iq
- accepts ALU register-register, multiplication, and division ops
- 8-entry
- out-of-order issue

### alu_imm_ldu_iq
- accepts ALU register-immediate and load ops
- 8-entry
- out-of-order issue

### stamofu_dq
- accepts store, AMO, and fence ops
- 4-entry
- dispatch queue as opposed to issue queue
    - really just acts as a bandwidth converting buffer from the 4-way superscalar frontend to the 1-per-cycle enqueue onto the stamofu queue, where the readiness of instructions is not tested before they are launched into the stamofu queue
        - readiness testing and collection of operands will be done by the stamofu queue
- in-order "issue" out of the dispatch queue

### bru_iq
- accepts branch, jump, LUI, AUIPC ops
- 4-entry
- out-of-order issue

### sys_iq
- accepts CSR and system ops
- 4-entry
- in-order issue

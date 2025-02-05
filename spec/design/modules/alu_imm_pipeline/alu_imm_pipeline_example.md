# alu_imm_pipeline Example Operation

# Key:

### op format
\<ROB index>: \<op> p\<dest PR #>, b\<operand A bank>:{f (forward), r (reg read)}, \<immediate>
- 0: ADDI p1, b2:f, 5
    - issue_ROB_index = 0
    - issue_op = 4'b0000
    - issue_imm12 = 5
    - issue_dest_PR = 1
    - issue_A_forward = 1
    - issue_A_bank = 2
- 1: SLTIU p12, b0:r, 8
    - issue_ROB_index = 1
    - issue_op = 4'b0011
    - issue_imm12 = 8
    - issue_dest_PR = 12
    - issue_A_forward = 0
    - issue_A_bank = 0

# Example Operation

![alu_imm_pipeline Example Operation](alu_imm_pipeline_example.png)
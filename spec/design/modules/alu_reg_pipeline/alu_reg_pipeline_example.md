# alu_reg_pipeline Example Operation

![alu_reg_pipeline Example Operation](alu_reg_pipeline_example.png)

# Key:

### op format
\<ROB index>: \<op> p\<dest PR #>, b\<operand A bank>:{f (forward), r (reg read)}, b\<operand B bank>:{f,r}

Example:
- 0: ADD p1, b2:f, b3:r
    - issue_ROB_index = 0
    - issue_op = 4'b0000
    - issue_dest_PR = 1
    - issue_A_forward = 1
    - issue_A_bank = 2
    - issue_B_forward = 0
    - issue_B_bank = 3
# prf Example Operation

Since the read arbitration and write arbitration are fully independent and individually complex, a read example and a write example are shown separately. 

These examples visualize the test cases from [prf_tb.sv](../../../../tb/prf_tb.sv).

# Example Read Operation

## Key:

### read request format

at each read requestor:
- p\<PR # in hex>
- n

Examples:
- p23
    - read_req_valid_by_rr[rr] = 1'b1
    - read_req_PR_by_rr[rr] = 7'h23
- n
    - read_req_valid_by_rr[rr] = 1'b0
    - read_req_PR_by_rr[rr] = 7'hx

### read response format

at each bank: 
- rr\<acked read requestor # for port 0>:p\<PR # in hex>, rr\<acked read requestor for port 1>:p\<PR # in hex>
- rr\<acked read requestor # for port 0>:p\<PR # in hex>, n
- n, n

Examples:
- rr4:p12, rr6:pA
    - read_resp_ack_by_rr[rr=4] = 1'b1
    - read_resp_port_by_rr[rr=4] = 1'b0
    - read_data_by_bank_by_port[bank=2][port=0] = 32'h<expected value>
        - there will be one of these at each bank visually shown in the example, but here we can infer that the bank is bank 2 as it is taking read requests for registers p12 and pA, where 0x12 % 4 == 2 and 0xA % 4 == 2
        - data values are not important to the example
        - as expected for a memory array, the value follows what was written last to the PR as indicated by the writeback bus by bank interface
    - read_resp_ack_by_rr[rr=6] = 1'b1
    - read_resp_port_by_rr[rr=6] = 1'b1
    - read_data_by_bank_by_port[bank=2][port=1] = 32'h<expected value>
    - other banks and rr's can be independently active this cycle
- rr2:p9, n
    - read_resp_ack_by_rr[rr=2] = 1'b0
    - read_resp_port_by_rr[rr=2] = 1'b0
    - read_data_by_bank_by_port[bank=1][port=0] = 32'h<expected value>
    - read_data_by_bank_by_port[bank=1][port=1] = 32'hx
        - don't care what value is read since port 1 is unused for this bank
    - other banks and rr's can be independently active this cycle
- n, n
    - no ack's contributed by this bank
    - read_data_by_bank_by_port[bank][port=0] = 32'h<expected value>
    - read_data_by_bank_by_port[bank][port=1] = 32'h<expected value>
        - the bank values could be inferred in the previous examples but this one has no register shown so they can't be here. again, the visualization in the example will show the associated bank
    - other banks and rr's can be independently active this cycle

![prf Example Read Operation](prf_read_example.png)

# Example Write Operation

## Key:

### op format
p\<PR # IN HEX>

Examples:
- a

![prf Example Write Operation](prf_write_example.png)

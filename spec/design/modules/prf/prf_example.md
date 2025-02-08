# prf Example Operation

Since the read arbitration and write arbitration are fully independent and individually complex, a read example and a write example are shown separately. 

These examples visualize sections of the tests performed in [prf_tb.sv](../../../../tb/prf_tb.sv).

# Example Read Operation

## Key:

### read request format

Yellow circles at each read requestor:
- p\<PR # in hex>
- n

Examples:
- p23
    - read_req_valid_by_rr[rr] = 1'b1
    - read_req_PR_by_rr[rr] = 7'h23
- n
    - read_req_valid_by_rr[rr] = 1'b0
    - read_req_PR_by_rr[rr] = 7'hx
        - this signal is ignored if read_req_valid_by_rr[rr] = 1'b0

### read response format

Blue ovals at each bank: 
- rr\<acked read requestor # in hex for port 0>:p\<PR # in hex>, rr\<acked read requestor # in hex for port 1>:p\<PR # in hex>
- rr\<acked read requestor # in hex for port 0>:p\<PR # in hex>, n
- n, n

Examples:
- rr4:p12, rr6:pA
    - read_resp_ack_by_rr[rr=4] = 1'b1
    - read_resp_port_by_rr[rr=4] = 1'b0
    - read_data_by_bank_by_port[bank=2][port=0] = 32'h\<expected value>
        - there will be one of these at each bank visually shown in the example, but here we can infer that the bank is bank 2 as it is taking read requests for registers p12 and pA, where 0x12 % 4 == 2 and 0xA % 4 == 2
        - data values are not important to demonstrating the arbitration rules in the example
        - as expected for a memory array, the value follows what was written last to the PR as indicated by the writeback bus by bank interface
    - read_resp_ack_by_rr[rr=6] = 1'b1
    - read_resp_port_by_rr[rr=6] = 1'b1
    - read_data_by_bank_by_port[bank=2][port=1] = 32'h\<expected value>
    - other banks and rr's can be independently active this cycle
- rr2:p9, n
    - read_resp_ack_by_rr[rr=2] = 1'b0
    - read_resp_port_by_rr[rr=2] = 1'b0
    - read_data_by_bank_by_port[bank=1][port=0] = 32'h\<expected value>
    - read_data_by_bank_by_port[bank=1][port=1] = 32'hx
        - don't care what value is read since port 1 is unused for this bank
    - other banks and rr's can be independently active this cycle
- n, n
    - no ack's contributed by this bank
    - read_data_by_bank_by_port[bank][port=0] = 32'hx
    - read_data_by_bank_by_port[bank][port=1] = 32'hx
        - the banks could be inferred in the previous examples but this one has no PR shown so they can't be inferred. again, the visualization in the example will show the associated bank
    - other banks and rr's can be independently active this cycle

![prf Example Read Operation](prf_read_example.png)


# Example Write Operation

## Key:

### write request format

Yellow circles at each write requestor:
- p\<PR # in hex>
- n

Examples:
- p18
    - WB_bus_valid_by_wr[wr] = 1'b1
    - WB_data_by_wr[wr] = 32'h\<tb input vector>
        - data values are not important to demonstrating the arbitration rules in the example
    - WB_PR_by_wr[wr] = 7'h18
    - WB_ROB_index_by_wr[wr] = 7'h\<tb input vector>
        - the specific ROB index value, which is a pass-through to the writeback bus, is not important to demonstrating the arbitration rules in the example
- n
    - WB_bus_valid_by_wr[wr] = 1'b0
    - WB_data_by_wr[wr] = 32'hx
    - WB_PR_by_wr[wr] = 7'hx
    - WB_ROB_index_by_wr[wr] = 7'hx

### write ready feedback format

Orange arrow coming down to the right of the yellow circles at each write requestor:
- arrow present
    - WB_ready_by_wr[wr] = 1'b1
- arrow not present
    - WB_ready_by_wr[wr] = 1'b0

### WB bus format

Blue ovals at each bank: 
- p\<PR # in hex>
- n

Examples:
- wr1:p12
    - WB_bus_valid_by_bank[bank=2] = 1'b1
    - WB_bus_upper_PR_by_bank[bank=2] = 5'h4
    - complete_bus_valid_by_bank[bank=2] = 1'b1
    - complete_bus_ROB_index_by_bank[bank=2] = 5'h\<expected value>
    - the write requestor annotation is only for showing where the request came from for the example. no external interface would give this information
- wr6:p0
    - PR 0 is special as it does not allow writeback. complete should still happen
    - WB_bus_valid_by_bank[bank=0] = 1'b0
    - WB_bus_upper_PR_by_bank[bank=0] = 5'h0
    - complete_bus_valid_by_bank[bank=0] = 1'b1
    - complete_bus_ROB_index_by_bank[bank=0] = 5'h\<expected value>
    - the write requestor annotation is only for showing where the request came from for the example. no external interface would give this information
- n
    - WB_bus_valid_by_bank[bank] = 1'b0
    - WB_bus_upper_PR_by_bank[bank] = 5'hx
    - complete_bus_valid_by_bank[bank] = 1'b0
    - complete_bus_ROB_index_by_bank[bank] = 5'hx
        - the banks could be inferred in the previous examples but this one has no PR shown so they can't be inferred. again, the visualization in the example will show the associated bank

![prf Example Write Operation](prf_write_example.png)
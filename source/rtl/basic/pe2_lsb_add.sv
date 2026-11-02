/*
    Filename: pe2_lsb_add.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing 2x lsb's using add logic
*/

module pe2_lsb_add #(
    parameter int unsigned WIDTH = 8
) (
    input logic [WIDTH-1:0]     req_vec,

    output logic                ack0_valid,
    output logic [WIDTH-1:0]    ack0_one_hot,

    output logic                ack1_valid,
    output logic [WIDTH-1:0]    ack1_one_hot
);

    logic [WIDTH-1:0] req_vec1;

    always_comb begin
        ack0_valid = |req_vec;
        ack0_one_hot = req_vec & (~req_vec + 1);
        req_vec1 = req_vec & ~ack0_one_hot;
        ack1_valid = |req_vec1;
        ack1_one_hot = req_vec1 & (~req_vec1 + 1);
    end

endmodule
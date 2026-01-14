/*
    Filename: pe_lsb_add.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing lsb using add logic
*/

module pe_lsb_add #(
    parameter WIDTH = 8
)(
    input logic [WIDTH-1:0]             req_vec,

    output logic [WIDTH-1:0]            ack_one_hot
);

    always_comb begin
        ack_one_hot = req_vec & (~req_vec + 1);
    end

endmodule
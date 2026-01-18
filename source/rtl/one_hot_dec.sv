/*
    Filename: one_hot_dec.sv
    Author: zlagpacan
    Description: RTL for One-Hot Decoder
*/

module one_hot_dec #(
    parameter WIDTH = 8
) (
    input logic                         valid_in,
    input logic [$clog2(WIDTH)-1:0]     index_in,

    output logic [WIDTH-1:0]            one_hot_out
);
    assign one_hot_out = valid_in << index_in;

endmodule

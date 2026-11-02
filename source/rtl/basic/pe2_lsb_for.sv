/*
    Filename: pe2_lsb_for.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing 2x lsb's using for loop logic
*/

module pe2_lsb_for #(
    parameter int unsigned WIDTH = 8
) (
    input logic [WIDTH-1:0]     req_vec,

    output logic                ack0_valid,
    output logic [WIDTH-1:0]    ack0_one_hot,

    output logic                ack1_valid,
    output logic [WIDTH-1:0]    ack1_one_hot
);

    always_comb begin
        ack0_one_hot = '0;
        ack1_one_hot = '0;
        ack0_valid = 1'b0;
        ack1_valid = 1'b0;

        for (int i = 0; i < WIDTH; i++) begin
            if (~ack0_valid & req_vec[i]) begin
                ack0_one_hot[i] = 1'b1;
                ack0_valid = 1'b1;
            end
            else if (~ack1_valid & req_vec[i]) begin
                ack1_one_hot[i] = 1'b1;
                ack1_valid = 1'b1;
            end
        end
    end

endmodule
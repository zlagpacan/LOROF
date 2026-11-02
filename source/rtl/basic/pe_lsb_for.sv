/*
    Filename: pe_lsb_for.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing lsb using for loop logic
*/

module pe_lsb_for #(
    parameter int unsigned WIDTH = 8
) (
    input logic [WIDTH-1:0]     req_vec,

    output logic [WIDTH-1:0]    ack_one_hot
);

    logic ack;

    always_comb begin
        ack_one_hot = '0;
        ack = 1'b0;

        // go through req vec bits after lsb
        for (int i = 0; i < WIDTH; i++) begin
            if (~ack & req_vec[i]) begin
                ack_one_hot[i] = 1'b1;
                ack = 1'b1;
            end
        end
    end

endmodule
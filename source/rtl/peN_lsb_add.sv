/*
    Filename: peN_lsb_add.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing first N lsb's using for loop logic
*/

module peN_lsb_add #(
    parameter int unsigned WIDTH = 8,
    parameter int unsigned N = 3
) (
    input logic [WIDTH-1:0]             req_vec,

    output logic [N-1:0]                ack_valid_by_n,
    output logic [N-1:0][WIDTH-1:0]     ack_one_hot_by_n
);

    logic [N-1:0][WIDTH-1:0] req_vec_by_n;

    always_comb begin
        req_vec_by_n[0] = req_vec;
        ack_valid_by_n[0] = |req_vec;
        ack_one_hot_by_n[0] = req_vec & (~req_vec + 1);

        for (int i = 1; i < WIDTH; i++) begin
            req_vec_by_n[i] = req_vec_by_n[i-1] & ~ack_one_hot_by_n[i-1];
            ack_valid_by_n[i] = |req_vec_by_n[i];
            ack_one_hot_by_n[i] = req_vec_by_n[i] & (~req_vec_by_n[i] + 1);
        end
    end

endmodule
/*
    Filename: peN_lsb_for.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing first N lsb's using for loop logic
*/

module peN_lsb_for #(
    parameter int unsigned WIDTH = 8,
    parameter int unsigned N = 3
) (
    input logic [WIDTH-1:0]             req_vec,

    output logic [N-1:0]                ack_valid_by_n,
    output logic [N-1:0][WIDTH-1:0]     ack_one_hot_by_n
);

    int unsigned num_acked;

    always_comb begin
        num_acked = 0;

        ack_valid_by_n = '0;
        ack_one_hot_by_n = '0;
        for (int i = 0; i < WIDTH; i++) begin
            if (req_vec[i] & num_acked < N) begin
                ack_valid_by_n[num_acked] = 1'b1;
                ack_one_hot_by_n[num_acked][i] = 1'b1;
                num_acked++;
            end
        end
    end

endmodule
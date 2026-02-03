/*
    Filename: ibuffer_deqer.sv
    Author: zlagpacan
    Description: RTL for Instruction Buffer Dequeuer
    Spec: LOROF/spec/design/ibuffer_deqer.md
*/

module ibuffer_deqer (

    input logic [15:0]          valid_vec,
    input logic [15:0]          uncompressed_vec,

    output logic [15:0][4:0]    count_out_vec
);

    // ----------------------------------------------------------------
    // Signals:



    // ----------------------------------------------------------------
    // Logic:

    always_comb begin
        count_out_vec[0] = valid_vec[0] ? 5'h1 : 5'h0;

        for (int i = 1; i < 14; i++) begin
            count_out_vec[i] = count_out_vec[i-1] + ((valid_vec[i] & (~valid_vec[i-1] | ~uncompressed_vec[i-1])) ? 5'h1 : 5'h0);
        end

        count_out_vec[15] = count_out_vec[14] + ((valid_vec[15] & ~uncompressed_vec[15] & (~valid_vec[14] | ~uncompressed_vec[14])) ? 5'h1 : 5'h0);
    end

endmodule
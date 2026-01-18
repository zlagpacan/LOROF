/*
    Filename: one_hot_enc.sv
    Author: zlagpacan
    Description: RTL for One-Hot Encoder
*/

module one_hot_enc #(
    parameter WIDTH = 8
) (
    input logic [WIDTH-1:0]             one_hot_in,

    output logic                        valid_out,
    output logic [$clog2(WIDTH)-1:0]    index_out
);
    always_comb begin
        valid_out = |one_hot_in;
        
        index_out = 0;
        for (int i = 0; i < WIDTH; i++) begin
            // if (one_hot_in[i]) begin
            //     index_out = i;
            // end
            index_out ^= i[$clog2(WIDTH)-1:0] & {$clog2(WIDTH){one_hot_in[i]}};
        end
    end

endmodule

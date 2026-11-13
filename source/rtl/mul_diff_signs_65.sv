module mul_diff_signs_65 (
    input logic CLK,
    input logic nRST,

    input logic [63:0] A,
    input logic [63:0] B,

    input logic [1:0] sel,

    output logic [127:0] out
);
    logic [64:0] A65;
    logic [64:0] B65;

    always_comb begin
        A65[63:0] = A;
        B65[63:0] = B;

        // MULHU
        if (sel[1] & sel[0]) begin
            A65[64] = 1'b0;
            B65[64] = 1'b0;
        end
        // MULHSU
        else if (sel[1]) begin
            A65[64] = A65[63];
            B65[64] = 1'b0;
        end
        // MUL/MULH
        else begin
            A65[64] = A65[63];
            B65[64] = B65[63];
        end

        out = $signed(A65) * $signed(B65);
    end

endmodule
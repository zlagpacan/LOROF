module mul_diff_signs (
    input logic CLK,
    input logic nRST,

    input logic [31:0] A,
    input logic [31:0] B,

    input logic [1:0] sel,

    output logic [63:0] out
);
    always_comb begin

        // MULHU
        if (sel[1] & sel[0]) begin
            out = A * B;
        end
        // MULHSU
        else if (sel[1]) begin
            out = $signed(A) * B;
        end
        // MUL/MULHU
        else begin
            out = $signed(A) * $signed(B);
        end
    end

endmodule
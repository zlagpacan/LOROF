module mul_diff_signs_33 (
    input logic CLK,
    input logic nRST,

    input logic [31:0] A,
    input logic [31:0] B,

    input logic [1:0] sel,

    output logic [63:0] out
);
    logic [32:0] A33;
    logic [32:0] B33;

    always_comb begin
        A33[31:0] = A;
        B33[31:0] = B;

        // MULHU
        if (sel[1] & sel[0]) begin
            A33[32] = A33[31];
            B33[32] = B33[31];
        end
        // MULHSU
        else if (sel[1]) begin
            A33[32] = A33[31];
            B33[32] = 1'b0;
        end
        // MUL/MULHU
        else begin
            A33[32] = 1'b0;
            B33[32] = 1'b0;
        end

        out = $signed(A33) * $signed(B33);
    end

endmodule
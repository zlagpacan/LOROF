module mul_diff_signs_upper (
    input logic CLK,
    input logic nRST,

    input logic [31:0] A,
    input logic [31:0] B,

    input logic [1:0] sel,

    output logic [63:0] out
);
    logic [63:0] intermediate; 

    always_comb begin

        // MULHU
        if (sel[1] & sel[0]) begin
            intermediate = A * B;
        end
        // MULHSU
        else if (sel[1]) begin
            intermediate = $signed(A) * B;
        end
        // MUL/MULHU
        else begin
            intermediate = $signed(A) * $signed(B);
        end
    end

    assign out[31:0] = A * B;
    assign out[63:32] = intermediate[63:32];

endmodule
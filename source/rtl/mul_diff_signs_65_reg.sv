module mul_diff_signs_65_reg (
    input logic CLK,
    input logic nRST,

    input logic [63:0] A,
    input logic [63:0] B,

    input logic [1:0] sel,

    output logic [127:0] out_reg_reg
);
    logic [64:0] A65;
    logic [64:0] B65;

    logic [127:0] out_reg;

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
    end
    
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            out_reg <= 128'h0;
            out_reg_reg <= 128'h0;
        end
        else begin
            out_reg <= $signed(A65) * $signed(B65);
            out_reg_reg <= out_reg;
        end
    end

endmodule
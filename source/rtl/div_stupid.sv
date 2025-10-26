module stupid_div (
    input logic CLK,
    input logic nRST,

    input logic signed [31:0] A,
    input logic signed [31:0] B,

    output logic signed [31:0] out
);
    always_comb begin
        if (B == 0) begin
            out = '1;
        end
        else begin
            out = A / B;
        end
    end

endmodule

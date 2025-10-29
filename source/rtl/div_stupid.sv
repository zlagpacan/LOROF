module div_stupid (
    input logic CLK,
    input logic nRST,

    input logic signed [31:0] A,
    input logic signed [31:0] B,

    output logic signed [31:0] quotient,
    output logic signed [31:0] remainder
);
    always_comb begin
        if (B == 0) begin
            quotient = '1;
            remainder = A;
        end
        else begin
            quotient = A / B;
            remainder = A % B;
        end
    end

endmodule

module stupid_div (
    input logic CLK,
    input logic nRST,

    input logic signed [31:0] A,
    input logic signed [31:0] B,

    output logic signed [31:0] out
);

    assign out = A / B;

endmodule
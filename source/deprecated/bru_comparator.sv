module bru_comparator (
    input logic [31:0] A,
    input logic [31:0] B,
    output logic eq,
    output logic lts,
    output logic ltu
);
    
    logic inner_lt;
    
    assign inner_lt = A[30:0] < B[30:0];
    
    assign eq = A == B;

    assign lts = A[31] & ~B[31] | inner_lt & ~(~A[31] & B[31]);

    assign ltu = ~A[31] & B[31] | inner_lt & ~(A[31] & ~B[31]);

endmodule
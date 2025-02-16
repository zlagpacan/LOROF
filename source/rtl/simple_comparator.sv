module simple_comparator (
    input logic [31:0] A,
    input logic [31:0] B,
    output logic eq,
    output logic lts,
    output logic ltu
);
    
    assign ltu = A < B;
    
    assign eq = A == B;

    assign lts = $signed(A) < $signed(B);

endmodule
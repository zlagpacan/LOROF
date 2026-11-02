module countones #(
    parameter WIDTH = 8
) (
    input logic [WIDTH-1:0] input_vec,

    output logic [$clog2(WIDTH+1)-1:0] countones
);
    // assign count_vec = $countones(input_vec);

    always_comb begin
        countones = 0;
        for (int i = 0; i < WIDTH; i++) begin
            countones += input_vec[i];
        end
    end

endmodule
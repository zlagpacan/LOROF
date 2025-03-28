module majority #(
    parameter WIDTH = 8,
    parameter THRESHOLD = 4
) (
    input logic [WIDTH-1:0] vec,
    output logic above_threshold
);

    logic [$clog2(WIDTH):0] count;

    always_comb begin
        count = 0;
        for (int i = 0; i < WIDTH; i++) begin
            if (vec[i]) begin
                count += 1;
            end
        end
    end

    assign above_threshold = count >= THRESHOLD;

endmodule
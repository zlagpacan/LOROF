/*
    Filename: pe2_lsb.sv
    Author: zlagpacan
    Description: RTL for 2nd Priority Encoder prioritizing lsb
*/

module pe2_lsb #(
    parameter WIDTH = 8
)(
    input logic [WIDTH-1:0]             req_vec,

    output logic [WIDTH-1:0]            ack_one_hot,
    output logic [$clog2(WIDTH)-1:0]    ack_index
);
    logic found_first;
    logic found_second;

    always_comb begin

        ack_one_hot = '0;
        ack_index = 0;

        found_first = 1'b0;
        found_second = 1'b0;

        if (req_vec[0]) begin
            found_first = 1'b1;
        end

        // go through req vec bits after lsb
        for (int i = 1; i < WIDTH; i++) begin
            
            if (req_vec[i] & ~found_first) begin
                found_first = 1'b1;
            end
            else if (req_vec[i] & ~found_second) begin
                found_second = 1'b1;
                ack_one_hot[i] = 1'b1;
                ack_index = i;
            end
        end
    end

endmodule
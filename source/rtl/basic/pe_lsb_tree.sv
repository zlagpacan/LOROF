/*
    Filename: pe_lsb_tree.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing lsb using tree logic
        - ChatGPT help
*/

module pe_lsb_tree #(
    parameter int unsigned WIDTH = 8
) (
    input  logic [WIDTH-1:0]            req_vec,

    output logic                        ack_valid,
    output logic [$clog2(WIDTH)-1:0]    ack_index
);

    localparam int unsigned LEVELS = $clog2(WIDTH);

    logic [LEVELS:0][WIDTH-1:0]                 valids;
    logic [LEVELS:0][WIDTH-1:0][LEVELS-1:0]     indexes;

    always_comb begin

        // level 0
        for (int j = 0; j < WIDTH; j++) begin
            valids[0][j] = req_vec[j];
            indexes[0][j] = j[LEVELS-1:0];
        end
        
        // reduction levels
        for (int l = 0; l < LEVELS; l++) begin
            for (int j = 0; j < (WIDTH >> (l + 1)); j++) begin
                valids[l+1][j] = valids[l][2*j] | valids[l][2*j+1];
                indexes[l+1][j] = valids[l][2*j] ? indexes[l][2*j] : indexes[l][2*j+1];
            end
        end
    end

    // assign ack_valid = valids[LEVELS][0];
    assign ack_valid = |req_vec;
    assign ack_index = indexes[LEVELS][0];

endmodule
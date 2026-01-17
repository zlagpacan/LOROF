/*
    Filename: pe_lsb_tree.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing lsb using tree logic
*/

module pe_lsb_tree #(
    parameter int unsigned WIDTH    = 8,
    parameter int unsigned LEVELS   = $clog2(WIDTH)
) (
    input  logic [WIDTH-1:0]    req_vec,

    output logic                ack_valid,
    output logic [LEVELS-1:0]   ack_index
);

    // ack_valid[level][node]
    logic [LEVELS:0][WIDTH-1:0]             v;
    logic [LEVELS:0][WIDTH-1:0][LEVELS-1:0] i;

    genvar l, j;

    // Leaf level (level 0)
    generate
        for (j = 0; j < WIDTH; j++) begin : LEAF
            assign v[0][j] = req_vec[j];
            assign i[0][j] = j[LEVELS-1:0];
        end
    endgenerate

    // Reduction levels
    generate
        for (l = 0; l < LEVELS; l++) begin : LEVEL
            localparam int WIDTH = WIDTH >> l;
            for (j = 0; j < WIDTH/2; j++) begin : WIDTHODE
                assign v[l+1][j] =
                    v[l][2*j] | v[l][2*j+1];

                assign i[l+1][j] =
                    v[l][2*j] ? i[l][2*j]
                              : i[l][2*j+1];
            end
        end
    endgenerate

    assign ack_valid = v[LEVELS][0];
    assign ack_index = i[LEVELS][0];

endmodule
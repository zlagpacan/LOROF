/*
    Filename: ibuffer_marker.sv
    Author: zlagpacan
    Description: RTL for Instruction Buffer next valid instruction marker
    Spec: LOROF/spec/design/ibuffer_marker.md
*/

module ibuffer_marker #(
    parameter int unsigned WIDTH = 8
) (
    input logic [WIDTH-1:0]     valid_vec,
    input logic [WIDTH-1:0]     uncompressed_vec,

    output logic [WIDTH-1:0]    marker_vec
);

    always_comb begin
        marker_vec[0] = valid_vec[0];
        for (int i = 1; i < WIDTH-1; i++) begin
            marker_vec[i] = valid_vec[i] & (~marker_vec[i-1] | ~uncompressed_vec[i-1]);
        end
        marker_vec[WIDTH-1] = valid_vec[WIDTH-1] & (~marker_vec[WIDTH-2] | ~uncompressed_vec[WIDTH-2]) & ~uncompressed_vec[WIDTH-1];
    end

endmodule
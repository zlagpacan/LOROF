/*
    Filename: nearest_index.sv
    Author: zlagpacan
    Description: RTL for {bit vector, target index} -> {nearest index}
    Spec: LOROF/spec/design/nearest_index.md
*/

module nearest_index #(
    parameter VECTOR_WIDTH = 32,
    parameter INDEX_WIDTH = $clog2(VECTOR_WIDTH)
) (
    input logic [VECTOR_WIDTH-1:0]  bit_vector,
    input logic [INDEX_WIDTH-1:0]   target_index,

    output logic                    bit_present,
    output logic [INDEX_WIDTH-1:0]  nearest_index
);
    logic bit_found;

    assign bit_present = |bit_vector;

    always_comb begin
        bit_found = 1'b0;
        nearest_index = 0;

        if (bit_vector[target_index]) begin
            bit_found = 1'b1;
            nearest_index = target_index; 
        end
        else begin
            for (logic [INDEX_WIDTH-1:0] diff = 1; diff < VECTOR_WIDTH/2 + 1; diff++) begin

                if (~bit_found & bit_vector[target_index + diff]) begin
                    bit_found = 1'b1;
                    nearest_index = target_index + diff;
                end
                else if (~bit_found & bit_vector[target_index - diff]) begin
                    bit_found = 1'b1;
                    nearest_index = target_index - diff;
                end
            end
        end
    end

endmodule
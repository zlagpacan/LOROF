/*
    Filename: youngest_older.sv
    Author: zlagpacan
    Description: RTL for youngest older entry logic
    Spec: LOROF/spec/design/youngest_older.md
*/

module youngest_older #(
    parameter VECTOR_WIDTH = 8,
    parameter INDEX_WIDTH = $clog2(VECTOR_WIDTH)
) (
    input logic [VECTOR_WIDTH-1:0]  req_vec,

    input logic [INDEX_WIDTH-1:0]   head_index,
    input logic [VECTOR_WIDTH-1:0]  head_mask,

    input logic [INDEX_WIDTH-1:0]   target_index,
    input logic [VECTOR_WIDTH-1:0]  target_mask,

    output logic                    older_present,
    output logic [INDEX_WIDTH-1:0]  youngest_older_index
);
    logic [INDEX_WIDTH-1:0] and_head_and_not_target_index;
    logic [INDEX_WIDTH-1:0] and_not_target_index;
    logic [INDEX_WIDTH-1:0] all_index;

    pe_msb #(
        .WIDTH(VECTOR_WIDTH),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) AND_HEAD_AND_NOT_TARGET_PE_MSB (
        .req_vec(req_vec & head_mask & ~target_mask),
        .ack_index(and_head_and_not_target_index)
    );
    pe_msb #(
        .WIDTH(VECTOR_WIDTH),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) AND_NOT_TARGET_PE_MSB (
        .req_vec(req_vec & ~target_mask),
        .ack_index(and_not_target_index)
    );
    pe_msb #(
        .WIDTH(VECTOR_WIDTH),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) ALL_PE_MSB (
        .req_vec(req_vec),
        .ack_index(all_index)
    );

    always_comb begin
        if (target_index > head_index) begin
            older_present = |(req_vec & head_mask & ~target_mask);
            youngest_older_index = and_head_and_not_target_index;
        end
        else begin
            older_present = |(req_vec & (head_mask | ~target_mask));
            if (|(req_vec & ~target_mask)) begin
                youngest_older_index = and_not_target_index;
            end
            else begin
                youngest_older_index = all_index;
            end
        end
    end

endmodule
/*
    Filename: oldest_younger.sv
    Author: zlagpacan
    Description: RTL for oldest younger entry logic
    Spec: LOROF/spec/design/oldest_younger.md
*/

module oldest_younger #(
    parameter VECTOR_WIDTH = 8,
    parameter INDEX_WIDTH = $clog2(VECTOR_WIDTH)
) (
    input logic [VECTOR_WIDTH-1:0]  req_vec,

    input logic [INDEX_WIDTH-1:0]   head_index,
    input logic [VECTOR_WIDTH-1:0]  head_mask,

    input logic [INDEX_WIDTH-1:0]   target_index,
    input logic [VECTOR_WIDTH-1:0]  target_mask,

    output logic                    younger_present,
    output logic [INDEX_WIDTH-1:0]  oldest_younger_index
);
    logic [INDEX_WIDTH-1:0] and_target_and_not_head_index;
    logic [INDEX_WIDTH-1:0] and_target_index;
    logic [INDEX_WIDTH-1:0] all_index;

    pe_lsb #(
        .WIDTH(VECTOR_WIDTH),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) AND_TARGET_AND_NOT_HEAD_PE_LSB (
        .req_vec(req_vec & target_mask & ~head_mask),
        .ack_index(and_target_and_not_head_index)
    );
    pe_lsb #(
        .WIDTH(VECTOR_WIDTH),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) AND_TARGET_PE_LSB (
        .req_vec(req_vec & target_mask),
        .ack_index(and_target_index)
    );
    pe_lsb #(
        .WIDTH(VECTOR_WIDTH),
        .USE_ONE_HOT(0),
        .USE_INDEX(1)
    ) ALL_PE_LSB (
        .req_vec(req_vec),
        .ack_index(all_index)
    );

    always_comb begin
        if (target_index >= head_index) begin
            younger_present = |(req_vec & (target_mask | ~head_mask));
            if (|(req_vec & target_mask)) begin
                oldest_younger_index = and_target_index;
            end
            else begin
                oldest_younger_index = all_index;
            end
        end
        else begin
            younger_present = |(req_vec & target_mask & ~head_mask);
            oldest_younger_index = and_target_and_not_head_index;
        end
    end

endmodule
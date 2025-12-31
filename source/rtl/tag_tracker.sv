/*
    Filename: tag_tracker.sv
    Author: zlagpacan
    Description: RTL for Transaction Tag Tracker
    Spec: LOROF/spec/design/tag_tracker.md
*/

module tag_tracker #(
    parameter int unsigned TAG_COUNT = 4,
    parameter int unsigned TAG_WIDTH = $clog2(TAG_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // new tag dispatch
    input logic                     new_tag_consume,
    output logic                    new_tag_ready,
    output logic [TAG_WIDTH-1:0]    new_tag,

    // old tag retirement
    input logic                     old_tag_done,
    input logic [TAG_WIDTH-1:0]     old_tag
);

    // bit vec of ready-to-use tags
    logic [TAG_COUNT-1:0] bit_vec;

    // for now, simple linear priority for tags
    pe_lsb #(
        .WIDTH(TAG_COUNT),
        .USE_ONE_HOT(0),
        .USE_COLD(0),
        .USE_INDEX(1)
    ) PE_LSB (
        .req_vec(bit_vec),
        .ack_index(new_tag)
    );

    always_comb begin
        new_tag_ready = |bit_vec;
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            bit_vec <= '1;
        end
        else begin
            if (new_tag_consume & new_tag_ready) begin
                bit_vec[new_tag] <= 1'b0;
            end
            if (old_tag_done) begin
                bit_vec[old_tag] <= 1'b1;
            end
        end
    end

endmodule
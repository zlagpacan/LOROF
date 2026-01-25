/*
    Filename: id_tracker.sv
    Author: zlagpacan
    Description: RTL for Transaction Tag Tracker
    Spec: LOROF/spec/design/id_tracker.md
*/

module id_tracker #(
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
    pe_lsb_tree #(
        .WIDTH(TAG_COUNT)
    ) PE_LSB_TREE (
        .req_vec(bit_vec),
        .ack_valid(new_tag_ready),
        .ack_index(new_tag)
    );

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
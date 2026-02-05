/*
    Filename: id_tracker.sv
    Author: zlagpacan
    Description: RTL for Transaction ID Tracker
    Spec: LOROF/spec/design/id_tracker.md
*/

module id_tracker #(
    parameter int unsigned ID_COUNT = 4,
    parameter int unsigned ID_WIDTH = $clog2(ID_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // new id dispatch
    input logic                     new_id_consume,
    output logic                    new_id_ready,
    output logic [ID_WIDTH-1:0]     new_id,

    // old id retirement
    input logic                     old_id_done,
    input logic [ID_WIDTH-1:0]      old_id
);

    // bit vec of ready-to-use ids
    logic [ID_COUNT-1:0] bit_vec;

    // for now, simple linear priority for ids
    pe_lsb_tree #(
        .WIDTH(ID_COUNT)
    ) PE_LSB_TREE (
        .req_vec(bit_vec),
        .ack_valid(new_id_ready),
        .ack_index(new_id)
    );

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            bit_vec <= '1;
        end
        else begin
            if (new_id_consume & new_id_ready) begin
                bit_vec[new_id] <= 1'b0;
            end
            if (old_id_done) begin
                bit_vec[old_id] <= 1'b1;
            end
        end
    end

endmodule
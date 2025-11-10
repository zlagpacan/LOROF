/*
    Filename: arbiter_rr.sv
    Author: zlagpacan
    Description: RTL for Round-Robin Arbiter
    Spec: LOROF/spec/design/arbiter_rr.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module arbiter_rr #(
    parameter REQUESTER_COUNT = 4,
    parameter LOG_REQUESTER_COUNT = $clog2(REQUESTER_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,
 
    input logic [REQUESTER_COUNT-1:0]       req_vec,
    output logic                            req_present,

    input logic                             ack_ready,
    output logic [REQUESTER_COUNT-1:0]      ack_one_hot,
    output logic [LOG_REQUESTER_COUNT-1:0]  ack_index
);

    logic [REQUESTER_COUNT-1:0] last_mask;
    logic [REQUESTER_COUNT-1:0] cold_ack_mask;

    logic [REQUESTER_COUNT-1:0]         masked_req_vec;
    logic [REQUESTER_COUNT-1:0]         masked_ack_one_hot;
    logic [REQUESTER_COUNT-1:0]         masked_cold_ack_mask;
    logic [LOG_REQUESTER_COUNT-1:0]     masked_ack_index;

    logic [REQUESTER_COUNT-1:0]         unmasked_ack_one_hot;
    logic [REQUESTER_COUNT-1:0]         unmasked_cold_ack_mask;
    logic [LOG_REQUESTER_COUNT-1:0]     unmasked_ack_index;

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            last_mask <= '0;
        end
        else if (ack_ready) begin
            last_mask <= cold_ack_mask;
        end
    end
    
    always_comb begin
        masked_req_vec = req_vec & last_mask;
    end

    pe_lsb #(
        .WIDTH(REQUESTER_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(1),
        .USE_INDEX(1)
    ) MASKED_PE_LSB (
        .req_vec(masked_req_vec),
        .ack_one_hot(masked_ack_one_hot),
        .cold_ack_mask(masked_cold_ack_mask),
        .ack_index(masked_ack_index)
    );

    pe_lsb #(
        .WIDTH(REQUESTER_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(1),
        .USE_INDEX(1)
    ) UNMASKED_PE_LSB (
        .req_vec(req_vec),
        .ack_one_hot(unmasked_ack_one_hot),
        .cold_ack_mask(unmasked_cold_ack_mask),
        .ack_index(unmasked_ack_index)
    );

    always_comb begin
        req_present = |req_vec;

        ack_one_hot = 
            {REQUESTER_COUNT{ack_ready}}
            & (
                masked_ack_one_hot
                | (unmasked_ack_one_hot & {REQUESTER_COUNT{~|masked_req_vec}}));

        if (|masked_req_vec) begin
            cold_ack_mask = masked_cold_ack_mask;
            ack_index = masked_ack_index;
        end
        else begin
            cold_ack_mask = unmasked_cold_ack_mask;
            ack_index = unmasked_ack_index;
        end
    end

endmodule
/*
    Filename: prf.sv
    Author: zlagpacan
    Description: RTL for Physical Register File
    Spec: LOROF/spec/design/prf.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf (

    // seq
    input logic CLK,
    input logic nRST,

    // reg read req by read requester
    input logic [PRF_RR_COUNT-1:0]                      reg_read_req_valid_by_rr,
    input logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]    reg_read_req_PR_by_rr,

    // reg read info by read requestor
    output logic [PRF_RR_COUNT-1:0]     reg_read_ack_by_rr,
    output logic [PRF_RR_COUNT-1:0]     reg_read_port_by_rr,

    // reg read data by bank
    output logic [PRF_BANK_COUNT-1:0][1:0][31:0] reg_read_data_by_bank_by_port,

    // writeback data by write requestor
    input logic [PRF_WR_COUNT-1:0]                          WB_valid_by_wr,
    input logic [PRF_WR_COUNT-1:0][31:0]                    WB_data_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]        WB_PR_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]     WB_ROB_index_by_wr,

    // writeback backpressure by write requestor
    output logic [PRF_WR_COUNT-1:0] WB_ready_by_wr

    // writeback bus by bank
    output logic [PRF_BANK_COUNT-1:0]                                       WB_bus_valid_by_bank,
    output logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]  WB_bus_upper_PR_by_bank
);

    // ----------------------------------------------------------------
    // Signals:

    // Reg File RAM Array
    logic [PRF_BANK_COUNT-1:0][PR_COUNT/PRF_BANK_COUNT-1:0][31:0] PRF_by_bank;

    // Read Req Signals
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    reg_read_req_valid_by_bank_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    unacked_reg_read_req_valid_by_bank_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      unacked_reg_read_req_PR_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    compressed_reg_read_req_valid_by_bank_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      compressed_reg_read_req_PR_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    last_reg_read_mask_by_bank;

    // Write Req Signals
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    WB_valid_by_bank_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    unacked_WB_valid_by_bank_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                  unacked_WB_data_by_wr,
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]      unacked_WB_PR_by_wr,
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   unacked_WB_ROB_index_by_wr,

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    compressed_WB_valid_by_bank_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                  compressed_WB_data_by_wr,
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]      compressed_WB_PR_by_wr,
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   compressed_WB_ROB_index_by_wr,

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    last_WB_mask;

    // ----------------------------------------------------------------
    // Reg Read Logic:

    always_comb begin

        // demux reg read req's to banks
        reg_read_req_valid_by_bank_by_rr = '0;
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
            reg_read_req_valid_by_bank_by_rr[reg_read_req_PR_by_rr[rr][LOG_PRF_BANK_COUNT-1:0]][rr] = reg_read_req_valid_by_rr[rr];
        end

        // compress current + unacked req's
        compressed_reg_read_req_valid_by_bank_by_rr = reg_read_req_valid_by_bank_by_rr | unacked_reg_read_req_valid_by_bank_by_rr;

        // select current vs. unacked req PR for compressed
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin

            // use unacked reg read PR if any bank valid for unacked reg read
            if (|unacked_reg_read_req_valid_by_bank_by_rr[PRF_BANK_COUNT-1:0][rr]) begin
                compressed_reg_read_req_PR_by_rr[rr] = unacked_reg_read_req_PR_by_rr;
            end
            else begin
                compressed_reg_read_req_PR_by_rr[rr] = reg_read_req_PR_by_rr;
            end
        end
    end

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            unacked_reg_read_req_valid_by_bank_by_rr <= '0;
            unacked_reg_read_req_PR_by_rr <= '0;
            last_reg_read_mask_by_bank <= '0;
        end
        else begin

        end
    end

    // determine ack's for next cycle

    // ----------------------------------------------------------------
    // Writeback Logic:

    // assign WB_ready_by_wr = WB_valid_by_wr & unacked_WB_valid_by_wr;

    // next unacked = ready?

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin

        end
        else begin

        end
    end

endmodule
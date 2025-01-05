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
    output logic [PRF_WR_COUNT-1:0] WB_ready_by_wr,

    // writeback bus by bank
    output logic [PRF_BANK_COUNT-1:0]                                       WB_bus_valid_by_bank,
    output logic [PRF_BANK_COUNT-1:0][31:0]                                 WB_bus_data_by_bank,
    output logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]  WB_bus_upper_PR_by_bank,
    output logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                  WB_bus_ROB_index_by_bank,

    // forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank
);

    // ----------------------------------------------------------------
    // Signals:

    // Reg File RAM Array
    logic [PRF_BANK_COUNT-1:0][PR_COUNT/PRF_BANK_COUNT-1:0][31:0]       prf_array_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     prf_port0_read_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     next_prf_port0_read_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     prf_port1_read_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     next_prf_port1_read_upper_PR_by_bank;

    // Read Req Signals
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    reg_read_req_valid_by_bank_by_rr;

    logic [PRF_RR_COUNT-1:0]                        unacked_reg_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0]                        next_unacked_reg_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      unacked_reg_read_req_PR_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      next_unacked_reg_read_req_PR_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    unacked_reg_read_req_valid_by_bank_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    compressed_reg_read_req_valid_by_bank_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      compressed_reg_read_req_PR_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port0_masked_reg_read_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port0_unmasked_reg_read_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port1_masked_reg_read_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port1_unmasked_reg_read_ack_by_bank_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port0_reg_read_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port1_reg_read_ack_by_bank_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    last_reg_read_mask_by_bank;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    next_last_reg_read_mask_by_bank;

    // Write Req Signals
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    WB_valid_by_bank_by_wr;

    logic [PRF_WR_COUNT-1:0]                        unacked_WB_valid_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                  unacked_WB_data_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]      unacked_WB_PR_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   unacked_WB_ROB_index_by_wr;
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    unacked_WB_valid_by_bank_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    compressed_WB_valid_by_bank_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                  compressed_WB_data_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]      compressed_WB_PR_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   compressed_WB_ROB_index_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    last_WB_mask;

    // ----------------------------------------------------------------
    // Reg Read Logic:

    // PQ function for RR's, prioritizing msb to lsb
    function logic [PRF_RR_COUNT-1:0] RR_PQ (input [PRF_RR_COUNT-1:0] req_vec);
        
        // init clear vec
        RR_PQ = '0;

        // go through req vec
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
            
            // check this req hot
            if (req_vec[rr]) begin

                // new one-hot vec
                    // override any lsb one-hot
                RR_PQ = '0;
                RR_PQ[rr] = 1'b1;
            end
        end
    endfunction

    always_comb begin

        // demux reg read req's to banks
        reg_read_req_valid_by_bank_by_rr = '0;
        unacked_reg_read_req_valid_by_bank_by_rr = '0;
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
            reg_read_req_valid_by_bank_by_rr[reg_read_req_PR_by_rr[rr][LOG_PRF_BANK_COUNT-1:0]][rr] = reg_read_req_valid_by_rr[rr];
            unacked_reg_read_req_valid_by_bank_by_rr[unacked_reg_read_req_PR_by_rr[rr][LOG_PRF_BANK_COUNT-1:0]][rr] = unacked_reg_read_req_valid_by_rr[rr];
        end

        // compress current + unacked req's
        compressed_reg_read_req_valid_by_bank_by_rr = reg_read_req_valid_by_bank_by_rr | unacked_reg_read_req_valid_by_bank_by_rr;

        // select current vs. unacked req PR for compressed
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin

            // use unacked reg read PR if any bank valid for unacked reg read
            if (unacked_reg_read_req_valid_by_rr[rr]) begin
                compressed_reg_read_req_PR_by_rr[rr] = unacked_reg_read_req_PR_by_rr[rr];
            end
            else begin
                compressed_reg_read_req_PR_by_rr[rr] = reg_read_req_PR_by_rr[rr];
            end
        end
        
        // ack PQ by bank
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            
            // port 0:
                // single PQ over raw compressed req's

            // port 0 masked
            port0_masked_reg_read_ack_by_bank_by_rr = RR_PQ(compressed_reg_read_req_valid_by_bank_by_rr[bank] & last_reg_read_mask_by_bank[bank]);

            // port 0 unmasked
            port0_unmasked_reg_read_ack_by_bank_by_rr = RR_PQ(compressed_reg_read_req_valid_by_bank_by_rr[bank]);

            // select port 0:
                // if any masked req, use masked
                // else use unmasked
            if (|compressed_reg_read_req_valid_by_bank_by_rr[bank] & last_reg_read_mask_by_bank[bank]) begin
                port0_reg_read_ack_by_bank_by_rr[bank] = port0_masked_reg_read_ack_by_bank_by_rr[bank];
            end
            else begin
                port0_reg_read_ack_by_bank_by_rr[bank] = port0_unmasked_reg_read_ack_by_bank_by_rr[bank];
            end

            // port 1:
                // single PQ over raw compressed req's with port 0 ack masked out

            // port 1 masked
            port1_masked_reg_read_ack_by_bank_by_rr = RR_PQ(compressed_reg_read_req_valid_by_bank_by_rr[bank] & ~port0_reg_read_ack_by_bank_by_rr[bank] & last_reg_read_mask_by_bank[bank]);

            // port 1 unmasked
            port1_unmasked_reg_read_ack_by_bank_by_rr = RR_PQ(compressed_reg_read_req_valid_by_bank_by_rr[bank] & ~port0_reg_read_ack_by_bank_by_rr[bank]);

            // select port 1:
                // if any masked req, use masked
                // else use unmasked
            if (|compressed_reg_read_req_valid_by_bank_by_rr[bank] & ~port0_reg_read_ack_by_bank_by_rr[bank] & last_reg_read_mask_by_bank[bank]) begin
                port1_reg_read_ack_by_bank_by_rr[bank] = port1_masked_reg_read_ack_by_bank_by_rr[bank];
            end
            else begin
                port1_reg_read_ack_by_bank_by_rr[bank] = port1_unmasked_reg_read_ack_by_bank_by_rr[bank];
            end
        end

        // final ack
            // combine port 0 and port 1 req's over all banks for ack
            // combine port 1 over all banks for port 
        reg_read_ack_by_rr = '0;
        reg_read_port_by_rr = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            reg_read_ack_by_rr |= port0_reg_read_ack_by_bank_by_rr[bank] | port1_reg_read_ack_by_bank_by_rr[bank];
            reg_read_port_by_rr |= port1_reg_read_ack_by_bank_by_rr[bank];
        end

        // unacked req's
        next_unacked_reg_read_req_valid_by_rr = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            next_unacked_reg_read_req_valid_by_rr |= compressed_reg_read_req_valid_by_bank_by_rr[bank];
        end
        next_unacked_reg_read_req_valid_by_rr = next_unacked_reg_read_req_valid_by_rr & ~reg_read_ack_by_rr;

        next_unacked_reg_read_req_PR_by_rr = compressed_reg_read_req_PR_by_rr;

        // last reg read mask
            // base on port 1
        next_last_reg_read_mask_by_bank = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            for (int rr = PRF_BANK_COUNT-2; rr >= 0; rr++) begin
                next_last_reg_read_mask_by_bank[bank][rr] = reg_read_ack_by_rr[rr+1] | next_last_reg_read_mask_by_bank[bank][rr+1];
            end
        end
    end

    // determine next reg read
    always_comb begin

        // go through banks
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin

            // port 0 one-hot mux
                // get PR:
                    // AND with ack
                    // OR by rr
            next_prf_port0_read_upper_PR_by_bank[bank] = '0;
            for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
                next_prf_port0_read_upper_PR_by_bank[bank] |= 
                    compressed_reg_read_req_PR_by_rr[rr][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT]
                    & 
                    {(LOG_PR_COUNT-LOG_PRF_BANK_COUNT){port0_reg_read_ack_by_bank_by_rr[bank][rr]}}
                ;
            end

            // port 1 one-hot mux
            next_prf_port1_read_upper_PR_by_bank[bank] = '0;
            for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
                next_prf_port1_read_upper_PR_by_bank[bank] |= 
                    compressed_reg_read_req_PR_by_rr[rr][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT]
                    & 
                    {(LOG_PR_COUNT-LOG_PRF_BANK_COUNT){port1_reg_read_ack_by_bank_by_rr[bank][rr]}}
                ;
            end
        end
    end

    // actual reg read
        // use registered index
    always_comb begin

        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            reg_read_data_by_bank_by_port[bank][0] = prf_array_by_bank[bank][prf_port0_read_upper_PR_by_bank];
            reg_read_data_by_bank_by_port[bank][1] = prf_array_by_bank[bank][prf_port1_read_upper_PR_by_bank];
        end
    end

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            prf_port0_read_upper_PR_by_bank <= '0;
            prf_port1_read_upper_PR_by_bank <= '0;
            unacked_reg_read_req_valid_by_rr <= '0;
            unacked_reg_read_req_PR_by_rr <= '0;
            last_reg_read_mask_by_bank <= '0;
        end
        else begin
            prf_port0_read_upper_PR_by_bank <= next_prf_port0_read_upper_PR_by_bank;
            prf_port1_read_upper_PR_by_bank <= next_prf_port1_read_upper_PR_by_bank;
            unacked_reg_read_req_valid_by_rr <= next_unacked_reg_read_req_valid_by_rr;
            unacked_reg_read_req_PR_by_rr <= next_unacked_reg_read_req_PR_by_rr;
            last_reg_read_mask_by_bank <= next_last_reg_read_mask_by_bank;
        end
    end

    // ----------------------------------------------------------------
    // Writeback Logic:

    // assign WB_ready_by_wr = WB_valid_by_wr & unacked_WB_valid_by_wr;

    // next unacked = ready?

    // Distributed RAM
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            prf_array_by_bank <= '0;
        end
        else begin
            for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
                if (WB_bus_valid_by_bank[bank]) 
                    prf_array_by_bank[bank][WB_bus_upper_PR_by_bank] <= WB_bus_data_by_bank;
            end
        end
    end

endmodule
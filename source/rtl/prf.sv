/*
    Filename: prf.sv
    Author: zlagpacan
    Description: RTL for Physical Register File
    Spec: LOROF/spec/design/prf.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf #(
    parameter PR_COUNT = 128,
    parameter LOG_PR_COUNT = $clog2(PR_COUNT),
    parameter PRF_BANK_COUNT = 4,
    parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT),
    parameter PRF_RR_COUNT = 11,
    parameter PRF_WR_COUNT = 7,
    
    parameter USE_BRAM = 1'b0
)(

    // seq
    input logic CLK,
    input logic nRST,

    // read req info by read requester
    input logic [PRF_RR_COUNT-1:0]                      read_req_valid_by_rr,
    input logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]    read_req_PR_by_rr,

    // read resp info by read requestor
    output logic [PRF_RR_COUNT-1:0]     read_resp_ack_by_rr,
    output logic [PRF_RR_COUNT-1:0]     read_resp_port_by_rr,

    // read data by bank
    output logic [PRF_BANK_COUNT-1:0][1:0][31:0] read_data_by_bank_by_port,

    // writeback info by write requestor
    input logic [PRF_WR_COUNT-1:0]                          WB_valid_by_wr,
    input logic [PRF_WR_COUNT-1:0][31:0]                    WB_data_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]        WB_PR_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]     WB_ROB_index_by_wr,

    // writeback feedback by write requestor
    output logic [PRF_WR_COUNT-1:0] WB_ready_by_wr,

    // writeback bus by bank
    output logic [PRF_BANK_COUNT-1:0]                                       WB_bus_valid_by_bank,
    output logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]  WB_bus_upper_PR_by_bank,

    // forward data by bank
    output logic [PRF_BANK_COUNT-1:0][31:0] forward_data_bus_by_bank,

    // complete bus by bank
    output logic [PRF_BANK_COUNT-1:0]                       complete_bus_valid_by_bank,
    output logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]  complete_bus_ROB_index_by_bank
);

    // ----------------------------------------------------------------
    // Signals:

    // // Reg File RAM Array
    // logic [PRF_BANK_COUNT-1:0][PR_COUNT/PRF_BANK_COUNT-1:0][31:0]       prf_array_by_bank_by_upper_PR;
        // instantiate this in ram module

    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     prf_port0_read_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     next_prf_port0_read_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     prf_port1_read_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     next_prf_port1_read_upper_PR_by_bank;
    
    logic [PRF_BANK_COUNT-1:0]                                          prf_WB_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0]                                          next_prf_WB_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0][31:0]                                    prf_WB_data_by_bank;
    logic [PRF_BANK_COUNT-1:0][31:0]                                    next_prf_WB_data_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     prf_WB_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     next_prf_WB_upper_PR_by_bank;

    logic [PRF_BANK_COUNT-1:0]                                          prf_complete_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0]                                          next_prf_complete_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                     prf_complete_ROB_index_by_bank; 
    logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                     next_prf_complete_ROB_index_by_bank;
        // ROB_index also here since shares one-hot mux logic

    // Read Req Signals
    logic [PRF_RR_COUNT-1:0]                        unacked_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0]                        next_unacked_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      unacked_read_req_PR_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      next_unacked_read_req_PR_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    read_req_valid_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    unacked_read_req_valid_by_bank_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    compressed_read_req_valid_by_bank_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      compressed_read_req_PR_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port0_masked_read_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port0_unmasked_read_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port1_masked_read_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port1_unmasked_read_ack_by_bank_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port0_read_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    port1_read_ack_by_bank_by_rr;

    logic [PRF_RR_COUNT-1:0]                        next_read_resp_ack_by_rr;
    logic [PRF_RR_COUNT-1:0]                        next_read_resp_port_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    last_read_mask_by_bank;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    next_last_read_mask_by_bank;

    // Writeback Signals
    logic [PRF_WR_COUNT-1:0]                        unacked_WB_valid_by_wr;
    logic [PRF_WR_COUNT-1:0]                        next_unacked_WB_valid_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                  unacked_WB_data_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                  next_unacked_WB_data_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]      unacked_WB_PR_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]      next_unacked_WB_PR_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   unacked_WB_ROB_index_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   next_unacked_WB_ROB_index_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    WB_valid_by_bank_by_wr;
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    unacked_WB_valid_by_bank_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    compressed_WB_valid_by_bank_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                  compressed_WB_data_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]      compressed_WB_PR_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]   compressed_WB_ROB_index_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    masked_WB_ack_by_bank_by_wr;
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    unmasked_WB_ack_by_bank_by_wr;
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    WB_ack_by_bank_by_wr;
    logic [PRF_WR_COUNT-1:0]                        WB_ack_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    last_WB_mask_by_bank;
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    next_last_WB_mask_by_bank;

    // ----------------------------------------------------------------
    // Memory Array Def:

    // create RAM array for each bank
    genvar ram_bank;
    generate

        for (ram_bank = 0; ram_bank < PRF_BANK_COUNT; ram_bank++) begin : ram_banks

            if (USE_BRAM) begin

                // BRAM using next's
                bram_2rport_1wport #(
                    .INNER_WIDTH(32),
                    .OUTER_WIDTH(PR_COUNT/PRF_BANK_COUNT)
                ) BRAM (
                    .CLK(CLK),
                    .nRST(nRST),
                    .port0_ren(1'b1),
                    .port0_rindex(next_prf_port0_read_upper_PR_by_bank[ram_bank]),
                    .port0_rdata(read_data_by_bank_by_port[ram_bank][0]),
                    .port1_ren(1'b1),
                    .port1_rindex(next_prf_port1_read_upper_PR_by_bank[ram_bank]),
                    .port1_rdata(read_data_by_bank_by_port[ram_bank][1]),
                    .wen_byte({4{prf_WB_valid_by_bank[ram_bank]}}),
                    .windex(prf_WB_upper_PR_by_bank[ram_bank]),
                    .wdata(prf_WB_data_by_bank[ram_bank])
                );

                // // BRAM using curr's
                // bram_2rport_1wport #(
                //     .INNER_WIDTH(32),
                //     .OUTER_WIDTH(PR_COUNT/PRF_BANK_COUNT)
                // ) BRAM (
                //     .CLK(CLK),
                //     .nRST(nRST),
                //     .port0_ren(1'b1),
                //     .port0_rindex(prf_port0_read_upper_PR_by_bank[ram_bank]),
                //     .port0_rdata(read_data_by_bank_by_port[ram_bank][0]),
                //     .port1_ren(1'b1),
                //     .port1_rindex(prf_port1_read_upper_PR_by_bank[ram_bank]),
                //     .port1_rdata(read_data_by_bank_by_port[ram_bank][1]),
                //     .wen_byte({4{prf_WB_valid_by_bank[ram_bank]}}),
                //     .windex(prf_WB_upper_PR_by_bank[ram_bank]),
                //     .wdata(prf_WB_data_by_bank[ram_bank])
                // );
            end

            else begin

                // DistRAM using curr's
                distram_2rport_1wport #(
                    .INNER_WIDTH(32),
                    .OUTER_WIDTH(PR_COUNT/PRF_BANK_COUNT)
                ) DISTRAM (
                    .CLK(CLK),
                    .port0_rindex(prf_port0_read_upper_PR_by_bank[ram_bank]),
                    .port0_rdata(read_data_by_bank_by_port[ram_bank][0]),
                    .port1_rindex(prf_port1_read_upper_PR_by_bank[ram_bank]),
                    .port1_rdata(read_data_by_bank_by_port[ram_bank][1]),
                    .wen(prf_WB_valid_by_bank[ram_bank]),
                    .windex(prf_WB_upper_PR_by_bank[ram_bank]),
                    .wdata(prf_WB_data_by_bank[ram_bank])
                );
            end
        end

    endgenerate

    // ----------------------------------------------------------------
    // Reg Read Logic:

    // Read Request PQ's
    genvar rr_bank;
    generate
        for (rr_bank = 0; rr_bank < PRF_BANK_COUNT; rr_bank++) begin
            
            // port 0:
                // single PQ over raw compressed req's
            
            // port 0 masked
            pq_lsb #(.WIDTH(PRF_RR_COUNT)) RR_PORT0_MASKED_PQ_LSB (
                .req_vec(compressed_read_req_valid_by_bank_by_rr[rr_bank] & last_read_mask_by_bank[rr_bank]),
                .ack_one_hot(port0_masked_read_ack_by_bank_by_rr[rr_bank]),
                .ack_mask()
            );
            
            // port 0 unmasked
            pq_lsb #(.WIDTH(PRF_RR_COUNT)) RR_PORT0_UNMASKED_PQ_LSB (
                .req_vec(compressed_read_req_valid_by_bank_by_rr[rr_bank]),
                .ack_one_hot(port0_unmasked_read_ack_by_bank_by_rr[rr_bank]),
                .ack_mask()
            );

            // port 1:
                // single PQ over raw compressed req's with port 0 ack masked out
            
            // port 1 masked
            pq_lsb #(.WIDTH(PRF_RR_COUNT)) RR_PORT1_MASKED_PQ_LSB (
                .req_vec(compressed_read_req_valid_by_bank_by_rr[rr_bank] & ~port0_read_ack_by_bank_by_rr[rr_bank] & last_read_mask_by_bank[rr_bank]),
                .ack_one_hot(port1_masked_read_ack_by_bank_by_rr[rr_bank]),
                .ack_mask()
            );
            
            // port 1 unmasked
            pq_lsb #(.WIDTH(PRF_RR_COUNT)) RR_PORT1_UNMASKED_PQ_LSB (
                .req_vec(compressed_read_req_valid_by_bank_by_rr[rr_bank] & ~port0_read_ack_by_bank_by_rr[rr_bank]),
                .ack_one_hot(port1_unmasked_read_ack_by_bank_by_rr[rr_bank]),
                .ack_mask()
            );

        end
    endgenerate

    always_comb begin

        // demux reg read req's to banks
        read_req_valid_by_bank_by_rr = '0;
        unacked_read_req_valid_by_bank_by_rr = '0;
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
            read_req_valid_by_bank_by_rr[read_req_PR_by_rr[rr][LOG_PRF_BANK_COUNT-1:0]][rr] = read_req_valid_by_rr[rr];
            unacked_read_req_valid_by_bank_by_rr[unacked_read_req_PR_by_rr[rr][LOG_PRF_BANK_COUNT-1:0]][rr] = unacked_read_req_valid_by_rr[rr];
        end

        // compress current + unacked req's
        compressed_read_req_valid_by_bank_by_rr = read_req_valid_by_bank_by_rr | unacked_read_req_valid_by_bank_by_rr;

        // select current vs. unacked req PR for compressed
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin

            // use unacked reg read PR if any bank valid for unacked reg read
            if (unacked_read_req_valid_by_rr[rr]) begin
                compressed_read_req_PR_by_rr[rr] = unacked_read_req_PR_by_rr[rr];
            end
            else begin
                compressed_read_req_PR_by_rr[rr] = read_req_PR_by_rr[rr];
            end
        end
        
        // port 0 and port 1 select by bank
            // use RR PQ's above
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin

            // select port 0:
                // if any masked req, use masked
                // else use unmasked
            if (|(compressed_read_req_valid_by_bank_by_rr[bank] & last_read_mask_by_bank[bank])) begin
                port0_read_ack_by_bank_by_rr[bank] = port0_masked_read_ack_by_bank_by_rr[bank];
            end
            else begin
                port0_read_ack_by_bank_by_rr[bank] = port0_unmasked_read_ack_by_bank_by_rr[bank];
            end

            // select port 1:
                // if any masked req, use masked
                // else use unmasked
            if (|(compressed_read_req_valid_by_bank_by_rr[bank] & ~port0_read_ack_by_bank_by_rr[bank] & last_read_mask_by_bank[bank])) begin
                port1_read_ack_by_bank_by_rr[bank] = port1_masked_read_ack_by_bank_by_rr[bank];
            end
            else begin
                port1_read_ack_by_bank_by_rr[bank] = port1_unmasked_read_ack_by_bank_by_rr[bank];
            end
        end

        // final ack
            // combine port 0 and port 1 req's over all banks for ack
            // combine port 1 over all banks for port 
        next_read_resp_ack_by_rr = '0;
        next_read_resp_port_by_rr = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            next_read_resp_ack_by_rr |= port0_read_ack_by_bank_by_rr[bank] | port1_read_ack_by_bank_by_rr[bank];
            next_read_resp_port_by_rr |= port1_read_ack_by_bank_by_rr[bank];
        end

        // unacked req's
        next_unacked_read_req_valid_by_rr = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            next_unacked_read_req_valid_by_rr |= compressed_read_req_valid_by_bank_by_rr[bank];
        end
        next_unacked_read_req_valid_by_rr &= ~next_read_resp_ack_by_rr;

        next_unacked_read_req_PR_by_rr = compressed_read_req_PR_by_rr;

        // last reg read mask
            // base on port 1
        next_last_read_mask_by_bank = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            for (int rr = 1; rr < PRF_RR_COUNT; rr++) begin
                next_last_read_mask_by_bank[bank][rr] = port1_read_ack_by_bank_by_rr[bank][rr-1] | next_last_read_mask_by_bank[bank][rr-1];
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
                    compressed_read_req_PR_by_rr[rr][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT]
                    & 
                    {(LOG_PR_COUNT-LOG_PRF_BANK_COUNT){port0_read_ack_by_bank_by_rr[bank][rr]}}
                ;
            end

            // port 1 one-hot mux
            next_prf_port1_read_upper_PR_by_bank[bank] = '0;
            for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
                next_prf_port1_read_upper_PR_by_bank[bank] |= 
                    compressed_read_req_PR_by_rr[rr][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT]
                    & 
                    {(LOG_PR_COUNT-LOG_PRF_BANK_COUNT){port1_read_ack_by_bank_by_rr[bank][rr]}}
                ;
            end
        end
    end

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            prf_port0_read_upper_PR_by_bank <= '0;
            prf_port1_read_upper_PR_by_bank <= '0;
            unacked_read_req_valid_by_rr <= '0;
            unacked_read_req_PR_by_rr <= '0;
            last_read_mask_by_bank <= '0;
            read_resp_ack_by_rr <= '0;
            read_resp_port_by_rr <= '0;
        end
        else begin
            prf_port0_read_upper_PR_by_bank <= next_prf_port0_read_upper_PR_by_bank;
            prf_port1_read_upper_PR_by_bank <= next_prf_port1_read_upper_PR_by_bank;
            unacked_read_req_valid_by_rr <= next_unacked_read_req_valid_by_rr;
            unacked_read_req_PR_by_rr <= next_unacked_read_req_PR_by_rr;
            last_read_mask_by_bank <= next_last_read_mask_by_bank;
            read_resp_ack_by_rr <= next_read_resp_ack_by_rr;
            read_resp_port_by_rr <= next_read_resp_port_by_rr;
        end
    end

    // ----------------------------------------------------------------
    // Writeback Logic:

    // Write Request PQ's
    genvar wr_bank;
    generate
        for (wr_bank = 0; wr_bank < PRF_BANK_COUNT; wr_bank++) begin

            // masked
            pq_lsb #(.WIDTH(PRF_WR_COUNT)) WR_MASKED_PQ_LSB (
                .req_vec(compressed_WB_valid_by_bank_by_wr[wr_bank] & last_WB_mask_by_bank[wr_bank]),
                .ack_one_hot(masked_WB_ack_by_bank_by_wr[wr_bank]),
                .ack_mask()
            );

            // unmasked
            pq_lsb #(.WIDTH(PRF_WR_COUNT)) WR_UNMASKED_PQ_LSB (
                .req_vec(compressed_WB_valid_by_bank_by_wr[wr_bank]),
                .ack_one_hot(unmasked_WB_ack_by_bank_by_wr[wr_bank]),
                .ack_mask()
            );

        end
    endgenerate

    always_comb begin

        // demux WB's to banks
        WB_valid_by_bank_by_wr = '0;
        unacked_WB_valid_by_bank_by_wr = '0;
        for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
            WB_valid_by_bank_by_wr[WB_PR_by_wr[wr][LOG_PRF_BANK_COUNT-1:0]][wr] = WB_valid_by_wr[wr] & ~unacked_WB_valid_by_wr[wr];
                // only handle oldest WB req per wr at a time, so ignore curr if have unacked (regardless of banks)
            unacked_WB_valid_by_bank_by_wr[unacked_WB_PR_by_wr[wr][LOG_PRF_BANK_COUNT-1:0]][wr] = unacked_WB_valid_by_wr[wr];
        end
    
        // compress current + unacked req's
        compressed_WB_valid_by_bank_by_wr = WB_valid_by_bank_by_wr | unacked_WB_valid_by_bank_by_wr;

        // select current vs. unacked req info for compressed
        for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin

            // use unacked WB info if any bank valid for unacked WB
            if (unacked_WB_valid_by_wr[wr]) begin
                compressed_WB_data_by_wr[wr] = unacked_WB_data_by_wr[wr];
                compressed_WB_PR_by_wr[wr] = unacked_WB_PR_by_wr[wr];
                compressed_WB_ROB_index_by_wr[wr] = unacked_WB_ROB_index_by_wr[wr];
            end
            else begin
                compressed_WB_data_by_wr[wr] = WB_data_by_wr[wr];
                compressed_WB_PR_by_wr[wr] = WB_PR_by_wr[wr];
                compressed_WB_ROB_index_by_wr[wr] = WB_ROB_index_by_wr[wr];
            end
        end

        // select by bank
            // use RR PQ's above
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin

            // select masked vs. unmasked
                // if any masked req, use masked
                // else use unmasked
            if (|(compressed_WB_valid_by_bank_by_wr[bank] & last_WB_mask_by_bank[bank])) begin
                WB_ack_by_bank_by_wr[bank] = masked_WB_ack_by_bank_by_wr[bank];
            end
            else begin
                WB_ack_by_bank_by_wr[bank] = unmasked_WB_ack_by_bank_by_wr[bank];
            end
        end

        // final ack
            // combine over all banks
        WB_ack_by_wr = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            WB_ack_by_wr |= WB_ack_by_bank_by_wr[bank];
        end

        // unacked req's
        next_unacked_WB_valid_by_wr = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            next_unacked_WB_valid_by_wr |= compressed_WB_valid_by_bank_by_wr[bank];
        end
        next_unacked_WB_valid_by_wr &= ~WB_ack_by_wr;

        next_unacked_WB_data_by_wr = compressed_WB_data_by_wr;
        next_unacked_WB_PR_by_wr = compressed_WB_PR_by_wr;
        next_unacked_WB_ROB_index_by_wr = compressed_WB_ROB_index_by_wr;
    
        // last WB mask
        next_last_WB_mask_by_bank = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            for (int wr = 1; wr < PRF_WR_COUNT; wr++) begin
                next_last_WB_mask_by_bank[bank][wr] = WB_ack_by_bank_by_wr[bank][wr-1] | next_last_WB_mask_by_bank[bank][wr-1];
            end
        end
    end

    // determine next reg WB
    always_comb begin

        // go through banks
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin

            // valid WB initially follows compressed for bank
                // can be cancelled if the write is determined to be to reg 0 later
            next_prf_WB_valid_by_bank[bank] = |compressed_WB_valid_by_bank_by_wr[bank];

            // valid complete follows any compressed for bank
            next_prf_complete_valid_by_bank[bank] = |compressed_WB_valid_by_bank_by_wr[bank];

            // one-hot mux
                // get data and PR:
                    // AND with ACK
                    // OR by wr
            next_prf_WB_data_by_bank[bank] = '0;
            next_prf_WB_upper_PR_by_bank[bank] = '0;

            next_prf_complete_ROB_index_by_bank[bank] = '0;

            for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
                next_prf_WB_data_by_bank[bank] |= 
                    compressed_WB_data_by_wr[wr]
                    &
                    {32{WB_ack_by_bank_by_wr[bank][wr]}}
                ;
                next_prf_WB_upper_PR_by_bank[bank] |=
                    compressed_WB_PR_by_wr[wr][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT]
                    &
                    {(LOG_PR_COUNT-LOG_PRF_BANK_COUNT){WB_ack_by_bank_by_wr[bank][wr]}}
                ;
                next_prf_complete_ROB_index_by_bank[bank] |= 
                    compressed_WB_ROB_index_by_wr[wr]
                    &
                    {LOG_ROB_ENTRIES{WB_ack_by_bank_by_wr[bank][wr]}}
                ;
            end
        end

        // ensure no WB if reg 0
            // don't want a write or a forward
        if (next_prf_WB_upper_PR_by_bank[0] == '0) begin
            next_prf_WB_valid_by_bank[0] = 1'b0;
        end
    end

    // ready logic
        // ready if don't currently have unacked req
            // don't care if have current valid or not, upstream pipelines can figure out internally if need to stall based on this
    assign WB_ready_by_wr = ~unacked_WB_valid_by_wr;

    // writeback bus
    assign WB_bus_valid_by_bank = prf_WB_valid_by_bank;
    assign WB_bus_upper_PR_by_bank = prf_WB_upper_PR_by_bank;

    // complete bus
    assign complete_bus_valid_by_bank = prf_complete_valid_by_bank;
    assign complete_bus_ROB_index_by_bank = prf_complete_ROB_index_by_bank;

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            prf_WB_valid_by_bank <= '0;
            prf_WB_data_by_bank <= '0;
            prf_WB_upper_PR_by_bank <= '0;
            prf_complete_valid_by_bank <= '0;
            prf_complete_ROB_index_by_bank <= '0;
            unacked_WB_valid_by_wr <= '0;
            unacked_WB_data_by_wr <= '0;
            unacked_WB_PR_by_wr <= '0;
            unacked_WB_ROB_index_by_wr <= '0;
            last_WB_mask_by_bank <= '0;
            forward_data_bus_by_bank <= '0;
        end
        else begin
            prf_WB_valid_by_bank <= next_prf_WB_valid_by_bank;
            prf_WB_data_by_bank <= next_prf_WB_data_by_bank;
            prf_WB_upper_PR_by_bank <= next_prf_WB_upper_PR_by_bank;
            prf_complete_valid_by_bank <= next_prf_complete_valid_by_bank;
            prf_complete_ROB_index_by_bank <= next_prf_complete_ROB_index_by_bank;
            unacked_WB_valid_by_wr <= next_unacked_WB_valid_by_wr;
            unacked_WB_data_by_wr <= next_unacked_WB_data_by_wr;
            unacked_WB_PR_by_wr <= next_unacked_WB_PR_by_wr;
            unacked_WB_ROB_index_by_wr <= next_unacked_WB_ROB_index_by_wr;
            last_WB_mask_by_bank <= next_last_WB_mask_by_bank;
            forward_data_bus_by_bank <= prf_WB_data_by_bank; 
                // 1-cycle delay from when actual WB happened
                    // this is cycle when pipelines can pick up value 
                // cycle before is when WB info is advertized to IQs
        end
    end

endmodule
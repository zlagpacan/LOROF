/*
    Filename: prf.sv
    Author: zlagpacan
    Description: RTL for Physical Register File
    Spec: LOROF/spec/design/prf.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf #(
    parameter USE_BRAM = 1'b0
)(

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
    output logic [PRF_BANK_COUNT-1:0][31:0] forward_data_by_bank
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
    logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                     prf_WB_ROB_index_by_bank; 
    logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                     next_prf_WB_ROB_index_by_bank;
        // ROB_index also here since shares one-hot mux logic

    // Read Req Signals
    logic [PRF_RR_COUNT-1:0]                        unacked_reg_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0]                        next_unacked_reg_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      unacked_reg_read_req_PR_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]      next_unacked_reg_read_req_PR_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    reg_read_req_valid_by_bank_by_rr;
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
    genvar bank;
    generate

        for (bank = 0; bank < PRF_BANK_COUNT; bank++) begin : BRAM_banks

            if (USE_BRAM) begin

                // BRAM using next's
                bram_2rport_1wport #(
                    .INNER_WIDTH(32),
                    .OUTER_WIDTH(PR_COUNT/PRF_BANK_COUNT)
                ) BRAM (
                    .CLK(CLK),
                    .nRST(nRST),
                    .port0_ren(1'b1),
                    .port0_rindex(next_prf_port0_read_upper_PR_by_bank[bank]),
                    .port0_rdata(reg_read_data_by_bank_by_port[bank][0]),
                    .port1_ren(1'b1),
                    .port1_rindex(next_prf_port1_read_upper_PR_by_bank[bank]),
                    .port1_rdata(reg_read_data_by_bank_by_port[bank][1]),
                    .wen_byte({4{prf_WB_valid_by_bank[bank]}}),
                    .windex(prf_WB_upper_PR_by_bank[bank]),
                    .wdata(prf_WB_data_by_bank)
                );

                // // BRAM using curr's
                // bram_2rport_1wport #(
                //     .INNER_WIDTH(32),
                //     .OUTER_WIDTH(PR_COUNT/PRF_BANK_COUNT)
                // ) BRAM (
                //     .CLK(CLK),
                //     .nRST(nRST),
                //     .port0_ren(1'b1),
                //     .port0_rindex(prf_port0_read_upper_PR_by_bank[bank]),
                //     .port0_rdata(reg_read_data_by_bank_by_port[bank][0]),
                //     .port1_ren(1'b1),
                //     .port1_rindex(prf_port1_read_upper_PR_by_bank[bank]),
                //     .port1_rdata(reg_read_data_by_bank_by_port[bank][1]),
                //     .wen_byte({4{prf_WB_valid_by_bank[bank]}}),
                //     .windex(prf_WB_upper_PR_by_bank[bank]),
                //     .wdata(prf_WB_data_by_bank)
                // );
            end

            else begin

                // DistRAM using curr's
                distram_2rport_1wport #(
                    .INNER_WIDTH(32),
                    .OUTER_WIDTH(PR_COUNT/PRF_BANK_COUNT)
                ) BRAM (
                    .CLK(CLK),
                    .port0_rindex(prf_port0_read_upper_PR_by_bank[bank]),
                    .port0_rdata(reg_read_data_by_bank_by_port[bank][0]),
                    .port1_rindex(prf_port1_read_upper_PR_by_bank[bank]),
                    .port1_rdata(reg_read_data_by_bank_by_port[bank][1]),
                    .wen(prf_WB_valid_by_bank[bank]),
                    .windex(prf_WB_upper_PR_by_bank[bank]),
                    .wdata(prf_WB_data_by_bank)
                );
            end
        end

    endgenerate

    // ----------------------------------------------------------------
    // Reg Read Logic:

    // PQ function for RR's, prioritizing msb to lsb
    function static logic [PRF_RR_COUNT-1:0] RR_PQ (input logic [PRF_RR_COUNT-1:0] req_vec);
        
        // init clear vec
        RR_PQ = '0;

        // go through req vec
            // lsb to msb so msb gets last say
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
            port0_masked_reg_read_ack_by_bank_by_rr[bank] = RR_PQ(compressed_reg_read_req_valid_by_bank_by_rr[bank] & last_reg_read_mask_by_bank[bank]);

            // port 0 unmasked
            port0_unmasked_reg_read_ack_by_bank_by_rr[bank] = RR_PQ(compressed_reg_read_req_valid_by_bank_by_rr[bank]);

            // select port 0:
                // if any masked req, use masked
                // else use unmasked
            if (|(compressed_reg_read_req_valid_by_bank_by_rr[bank] & last_reg_read_mask_by_bank[bank])) begin
                port0_reg_read_ack_by_bank_by_rr[bank] = port0_masked_reg_read_ack_by_bank_by_rr[bank];
            end
            else begin
                port0_reg_read_ack_by_bank_by_rr[bank] = port0_unmasked_reg_read_ack_by_bank_by_rr[bank];
            end

            // port 1:
                // single PQ over raw compressed req's with port 0 ack masked out

            // port 1 masked
            port1_masked_reg_read_ack_by_bank_by_rr[bank] = RR_PQ(compressed_reg_read_req_valid_by_bank_by_rr[bank] & ~port0_reg_read_ack_by_bank_by_rr[bank] & last_reg_read_mask_by_bank[bank]);

            // port 1 unmasked
            port1_unmasked_reg_read_ack_by_bank_by_rr[bank] = RR_PQ(compressed_reg_read_req_valid_by_bank_by_rr[bank] & ~port0_reg_read_ack_by_bank_by_rr[bank]);

            // select port 1:
                // if any masked req, use masked
                // else use unmasked
            if (|(compressed_reg_read_req_valid_by_bank_by_rr[bank] & ~port0_reg_read_ack_by_bank_by_rr[bank] & last_reg_read_mask_by_bank[bank])) begin
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
        next_unacked_reg_read_req_valid_by_rr &= ~reg_read_ack_by_rr;

        next_unacked_reg_read_req_PR_by_rr = compressed_reg_read_req_PR_by_rr;

        // last reg read mask
            // base on port 1
        next_last_reg_read_mask_by_bank = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            for (int rr = PRF_RR_COUNT-2; rr >= 0; rr--) begin
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

    // // actual reg read
    // generate

    //     if (USE_BRAM) begin

    //         // BRAM:
    //             // registered read, use unregistered index
    //         always_ff @ (posedge CLK) begin
    //             for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
    //                 reg_read_data_by_bank_by_port[bank][0] <= prf_array_by_bank_by_upper_PR[bank][next_prf_port0_read_upper_PR_by_bank];
    //                 reg_read_data_by_bank_by_port[bank][1] <= prf_array_by_bank_by_upper_PR[bank][next_prf_port1_read_upper_PR_by_bank];
    //             end
    //         end
            
    //         // // BRAM:
    //         //     // registered read, use registered index
    //         // always_ff @ (posedge CLK) begin
    //         //     for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
    //         //         reg_read_data_by_bank_by_port[bank][0] <= prf_array_by_bank_by_upper_PR[bank][prf_port0_read_upper_PR_by_bank];
    //         //         reg_read_data_by_bank_by_port[bank][1] <= prf_array_by_bank_by_upper_PR[bank][prf_port1_read_upper_PR_by_bank];
    //         //     end
    //         // end
    //     end

    //     else begin

    //         // Distributed RAM:
    //             // use registered index
    //         always_comb begin
    //             for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
    //                 reg_read_data_by_bank_by_port[bank][0] = prf_array_by_bank_by_upper_PR[bank][prf_port0_read_upper_PR_by_bank];
    //                 reg_read_data_by_bank_by_port[bank][1] = prf_array_by_bank_by_upper_PR[bank][prf_port1_read_upper_PR_by_bank];
    //             end
    //         end
    //     end

    // endgenerate

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

    // PQ function for WR's, prioritizing msb to lsb
    function static logic [PRF_WR_COUNT-1:0] WR_PQ (input logic [PRF_WR_COUNT-1:0] req_vec);

        // init clear vec
        WR_PQ = '0;

        // go through req vec
            // lsb to msb so msb gets last say
        for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
            
            // check this req hot
            if (req_vec[wr]) begin

                // new one-hot vec
                    // override any lsb one-hot
                WR_PQ = '0;
                WR_PQ[wr] = 1'b1;
            end
        end

    endfunction

    always_comb begin

        // demux WB's to banks
        WB_valid_by_bank_by_wr = '0;
        unacked_WB_valid_by_bank_by_wr = '0;
        for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
            WB_valid_by_bank_by_wr[WB_PR_by_wr[wr][LOG_PRF_BANK_COUNT-1:0]][wr] = WB_valid_by_wr[wr];
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

        // ack PQ by bank
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin

            // masked
            masked_WB_ack_by_bank_by_wr[bank] = WR_PQ(compressed_WB_valid_by_bank_by_wr[bank] & last_WB_mask_by_bank[bank]);

            // unmasked
            unmasked_WB_ack_by_bank_by_wr[bank] = WR_PQ(compressed_WB_valid_by_bank_by_wr[bank]);
        
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
            for (int wr = PRF_WR_COUNT-2; wr >= 0; wr--) begin
                next_last_WB_mask_by_bank[bank][wr] = WB_ack_by_wr[wr+1] | next_last_WB_mask_by_bank[bank][wr+1];
            end
        end
    end

    // ddetermine next reg WB
    always_comb begin

        // determine which banks hot


        // go through banks
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin

            // valid follows any compressed for bank
            next_prf_WB_valid_by_bank[bank] = |compressed_WB_valid_by_bank_by_wr[bank];

            // one-hot mux
                // get data and PR:
                    // AND with ACK
                    // OR by wr
            next_prf_WB_data_by_bank[bank] = '0;
            next_prf_WB_upper_PR_by_bank[bank] = '0;
            next_prf_WB_ROB_index_by_bank[bank] = '0;

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
                next_prf_WB_ROB_index_by_bank[bank] |= 
                    compressed_WB_ROB_index_by_wr[wr]
                    &
                    {LOG_ROB_ENTRIES{WB_ack_by_bank_by_wr[bank][wr]}}
                ;
            end
        end
    end

    // ready logic
        // ready if don't currently have double req
        // if have double req:
            // stall this cycle, guaranteed keeping current around
            // once ack unacked req (can be this cycle or later cycle), can keep things moving starting the next cycle
            // cycle after unacked is acked, can collect current or make it unacked
        // not a true buffer, more of a stall when full this cycle
            // will stall even if won't be full next cycle
            // do this for friendlier timing, can know if WB ready early in cycle
    assign WB_ready_by_wr = ~(WB_valid_by_wr & unacked_WB_valid_by_wr);

    // writeback bus
    assign WB_bus_valid_by_bank = prf_WB_valid_by_bank;
    assign WB_bus_data_by_bank = prf_WB_data_by_bank;
    assign WB_bus_upper_PR_by_bank = prf_WB_upper_PR_by_bank;
    assign WB_bus_ROB_index_by_bank = prf_WB_ROB_index_by_bank;

    // FF
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            prf_WB_valid_by_bank <= '0;
            prf_WB_data_by_bank <= '0;
            prf_WB_upper_PR_by_bank <= '0;
            prf_WB_ROB_index_by_bank <= '0;
            unacked_WB_valid_by_wr <= '0;
            unacked_WB_data_by_wr <= '0;
            unacked_WB_PR_by_wr <= '0;
            unacked_WB_ROB_index_by_wr <= '0;
            last_WB_mask_by_bank <= '0;
            forward_data_by_bank <= '0;
        end
        else begin
            prf_WB_valid_by_bank <= next_prf_WB_valid_by_bank;
            prf_WB_data_by_bank <= next_prf_WB_data_by_bank;
            prf_WB_upper_PR_by_bank <= next_prf_WB_upper_PR_by_bank;
            prf_WB_ROB_index_by_bank <= next_prf_WB_ROB_index_by_bank;
            unacked_WB_valid_by_wr <= next_unacked_WB_valid_by_wr;
            unacked_WB_data_by_wr <= next_unacked_WB_data_by_wr;
            unacked_WB_PR_by_wr <= next_unacked_WB_PR_by_wr;
            unacked_WB_ROB_index_by_wr <= next_unacked_WB_ROB_index_by_wr;
            last_WB_mask_by_bank <= next_last_WB_mask_by_bank;
            forward_data_by_bank <= prf_WB_data_by_bank; 
                // 1-cycle delay from when actual WB happened
                    // this is cycle when pipelines can pick up value 
                // cycle before is when WB info is advertized to IQs
        end
    end

    // // actual reg write
    // generate

    //     if (USE_BRAM) begin

    //         // BRAM
    //             // no reset
    //         always_ff @ (posedge CLK) begin
    //             for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
    //                 if (prf_WB_valid_by_bank[bank]) begin
    //                     prf_array_by_bank_by_upper_PR[bank][prf_WB_upper_PR_by_bank[bank]] <= prf_WB_data_by_bank[bank];
    //                 end
    //             end
    //         end

    //     end

    //     else begin

    //         // Distributed RAM
    //             // reset
    //         always_ff @ (posedge CLK, negedge nRST) begin
    //             if (~nRST) begin
    //                 prf_array_by_bank_by_upper_PR <= '0;
    //             end
    //             else begin
    //                 for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
    //                     if (prf_WB_valid_by_bank[bank]) begin
    //                         prf_array_by_bank_by_upper_PR[bank][prf_WB_upper_PR_by_bank[bank]] <= prf_WB_data_by_bank[bank];
    //                     end
    //                 end
    //             end
    //         end
    //     end

    // endgenerate

endmodule
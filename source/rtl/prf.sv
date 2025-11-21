/*
    Filename: prf.sv
    Author: zlagpacan
    Description: RTL for 2-read-port, 1-write-port, banked Physical Register File
    Spec: LOROF/spec/design/prf.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module prf #(
    parameter PR_COUNT = 128,
    parameter LOG_PR_COUNT = $clog2(PR_COUNT),
    parameter PRF_BANK_COUNT = 4,
    parameter LOG_PRF_BANK_COUNT = $clog2(PRF_BANK_COUNT),

    parameter PRF_RR_COUNT = 9,
    parameter PRF_RR_INPUT_BUFFER_SIZE = 2,
    parameter PRF_WR_COUNT = 8,
    parameter PRF_WR_INPUT_BUFFER_SIZE = 2
)(

    // seq
    input logic CLK,
    input logic nRST,

    // read req info by read requestor
    input logic [PRF_RR_COUNT-1:0]                      read_req_valid_by_rr,
    input logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-1:0]    read_req_PR_by_rr,

    // read req feedback by read requestor
    output logic [PRF_RR_COUNT-1:0]                     read_req_ready_by_rr,

    // read resp info by read requestor
    output logic [PRF_RR_COUNT-1:0]                     read_resp_valid_by_rr,
    output logic [PRF_RR_COUNT-1:0][31:0]               read_resp_data_by_rr,

    // writeback info by write requestor
    input logic [PRF_WR_COUNT-1:0]                          WB_valid_by_wr,
    input logic [PRF_WR_COUNT-1:0]                          WB_send_complete_by_wr,
    input logic [PRF_WR_COUNT-1:0][31:0]                    WB_data_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-1:0]        WB_PR_by_wr,
    input logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]     WB_ROB_index_by_wr,

    // writeback feedback by write requestor
    output logic [PRF_WR_COUNT-1:0]                         WB_ready_by_wr,

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
    // Memory Array Signals:

    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     array_read_port0_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][31:0]                                    array_read_port0_data_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     array_read_port1_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][31:0]                                    array_read_port1_data_by_bank;
    
    logic [PRF_BANK_COUNT-1:0]                                          array_write_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     array_write_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][31:0]                                    array_write_data_by_bank;

    // ----------------------------------------------------------------
    // Reg Read Signals:

    logic [PRF_RR_COUNT-1:0]                                        enq_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   enq_read_req_upper_PR_by_rr;
    logic [PRF_RR_COUNT-1:0][PRF_BANK_COUNT-1:0]                    enq_read_req_bank_mask_by_rr;
    logic [PRF_RR_COUNT-1:0]                                        enq_read_req_ready_by_rr;

    logic [PRF_RR_COUNT-1:0]                                        deq_read_req_valid_by_rr;
    logic [PRF_RR_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   deq_read_req_upper_PR_by_rr;
    logic [PRF_RR_COUNT-1:0][PRF_BANK_COUNT-1:0]                    deq_read_req_bank_mask_by_rr;
    logic [PRF_RR_COUNT-1:0]                                        deq_read_req_ready_by_rr;

    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    arbiter_read_req_valid_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    arbiter_read_req_port0_ack_by_bank_by_rr;
    logic [PRF_BANK_COUNT-1:0][PRF_RR_COUNT-1:0]    arbiter_read_req_port1_ack_by_bank_by_rr;

    // ----------------------------------------------------------------
    // Reg Write Signals:

    logic [PRF_WR_COUNT-1:0]                                        enq_write_req_valid_by_wr;
    logic [PRF_WR_COUNT-1:0]                                        enq_write_req_perform_write_by_wr;
    logic [PRF_WR_COUNT-1:0]                                        enq_write_req_send_complete_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                                  enq_write_req_data_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   enq_write_req_upper_PR_by_wr;
    logic [PRF_WR_COUNT-1:0][PRF_BANK_COUNT-1:0]                    enq_write_req_bank_mask_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                   enq_write_req_ROB_index_by_wr;
    logic [PRF_WR_COUNT-1:0]                                        enq_write_req_ready_by_wr;

    logic [PRF_WR_COUNT-1:0]                                        deq_write_req_valid_by_wr;
    logic [PRF_WR_COUNT-1:0]                                        deq_write_req_perform_write_by_wr;
    logic [PRF_WR_COUNT-1:0]                                        deq_write_req_send_complete_by_wr;
    logic [PRF_WR_COUNT-1:0][31:0]                                  deq_write_req_data_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]   deq_write_req_upper_PR_by_wr;
    logic [PRF_WR_COUNT-1:0][PRF_BANK_COUNT-1:0]                    deq_write_req_bank_mask_by_wr;
    logic [PRF_WR_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                   deq_write_req_ROB_index_by_wr;
    logic [PRF_WR_COUNT-1:0]                                        deq_write_req_ready_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    queue_arbiter_write_req_valid_by_bank_by_wr;
    logic [PRF_BANK_COUNT-1:0]                      queue_arbiter_write_req_present_by_bank;
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    queue_arbiter_write_req_ack_by_bank_by_wr;

    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    bypass_arbiter_write_req_valid_by_bank_by_wr;
    logic [PRF_BANK_COUNT-1:0][PRF_WR_COUNT-1:0]    bypass_arbiter_write_req_ack_by_bank_by_wr;
    logic [PRF_WR_COUNT-1:0]                        bypass_arbiter_write_req_ack_by_wr;

    logic [PRF_BANK_COUNT-1:0]                                          queue_selected_write_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0]                                          queue_selected_write_perform_write_by_bank;
    logic [PRF_BANK_COUNT-1:0]                                          queue_selected_write_send_complete_by_bank;
    logic [PRF_BANK_COUNT-1:0][31:0]                                    queue_selected_write_data_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     queue_selected_write_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                     queue_selected_write_ROB_index_by_bank;

    logic [PRF_BANK_COUNT-1:0]                                          bypass_selected_write_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0]                                          bypass_selected_write_perform_write_by_bank;
    logic [PRF_BANK_COUNT-1:0]                                          bypass_selected_write_send_complete_by_bank;
    logic [PRF_BANK_COUNT-1:0][31:0]                                    bypass_selected_write_data_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     bypass_selected_write_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                     bypass_selected_write_ROB_index_by_bank;

    logic [PRF_BANK_COUNT-1:0]                                          selected_write_valid_by_bank;
    logic [PRF_BANK_COUNT-1:0]                                          selected_write_perform_write_by_bank;
    logic [PRF_BANK_COUNT-1:0]                                          selected_write_send_complete_by_bank;
    logic [PRF_BANK_COUNT-1:0][31:0]                                    selected_write_data_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0]     selected_write_upper_PR_by_bank;
    logic [PRF_BANK_COUNT-1:0][LOG_ROB_ENTRIES-1:0]                     selected_write_ROB_index_by_bank;

    logic [PRF_BANK_COUNT-1:0][31:0] WB_bus_data_by_bank;

    // ----------------------------------------------------------------
    // Reg Read Logic:
    
    genvar input_buffer_rr;
    generate
        for (input_buffer_rr = 0; input_buffer_rr < PRF_RR_COUNT; input_buffer_rr++) begin : read_req_input_buffers
            q_fast_ready #(
                .DATA_WIDTH(LOG_PR_COUNT-LOG_PRF_BANK_COUNT + PRF_BANK_COUNT),
                .NUM_ENTRIES(PRF_RR_INPUT_BUFFER_SIZE)
            ) READ_REQ_INPUT_BUFFER (
                .CLK(CLK),
                .nRST(nRST),
                .enq_valid(enq_read_req_valid_by_rr[input_buffer_rr]),
                .enq_data({enq_read_req_upper_PR_by_rr[input_buffer_rr], enq_read_req_bank_mask_by_rr[input_buffer_rr]}),
                .enq_ready(enq_read_req_ready_by_rr[input_buffer_rr]),
                .deq_valid(deq_read_req_valid_by_rr[input_buffer_rr]),
                .deq_data({deq_read_req_upper_PR_by_rr[input_buffer_rr], deq_read_req_bank_mask_by_rr[input_buffer_rr]}),
                .deq_ready(deq_read_req_ready_by_rr[input_buffer_rr])
            );
        end
    endgenerate

    always_comb begin
        enq_read_req_valid_by_rr = read_req_valid_by_rr;
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin  
            enq_read_req_upper_PR_by_rr[rr] = read_req_PR_by_rr[rr][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT];
            enq_read_req_bank_mask_by_rr[rr] = '0;
            enq_read_req_bank_mask_by_rr[rr][read_req_PR_by_rr[rr][LOG_PRF_BANK_COUNT-1:0]] = 1'b1;
        end

        read_req_ready_by_rr = enq_read_req_ready_by_rr;

        // demux read req's to arbiter banks
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
                arbiter_read_req_valid_by_bank_by_rr[bank][rr] = deq_read_req_valid_by_rr[rr] & deq_read_req_bank_mask_by_rr[rr][bank];
            end
        end

        // retrieve arbiter bank ack's for input buffer deq ready's
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
            deq_read_req_ready_by_rr[rr] = '0;
            for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
                deq_read_req_ready_by_rr[rr] |= arbiter_read_req_port0_ack_by_bank_by_rr[bank][rr];
                deq_read_req_ready_by_rr[rr] |= arbiter_read_req_port1_ack_by_bank_by_rr[bank][rr];
            end
        end
    end

    genvar read_bank;
    generate
        for (read_bank = 0; read_bank < PRF_BANK_COUNT; read_bank++) begin : read_arbiters

            arbiter2_rr #(
                .REQUESTOR_COUNT(PRF_RR_COUNT)
            ) READ_ARBITER (
                .CLK(CLK),
                .nRST(nRST),
                .req_valid(1'b1),
                .req_vec(arbiter_read_req_valid_by_bank_by_rr[read_bank]),
                .port0_ack_valid(),
                .port0_ack_one_hot(arbiter_read_req_port0_ack_by_bank_by_rr[read_bank]),
                .port1_ack_valid(),
                .port1_ack_one_hot(arbiter_read_req_port1_ack_by_bank_by_rr[read_bank])
            );

            mux_one_hot #(
                .COUNT(PRF_RR_COUNT),
                .WIDTH(LOG_PR_COUNT - LOG_PRF_BANK_COUNT)
            ) READ_PORT0_UPPER_PR_MUX_ONE_HOT (
                .sel_one_hot(arbiter_read_req_port0_ack_by_bank_by_rr[read_bank]),
                .data_by_requestor(deq_read_req_upper_PR_by_rr),
                .selected_data(array_read_port0_upper_PR_by_bank[read_bank])
            );

            mux_one_hot #(
                .COUNT(PRF_RR_COUNT),
                .WIDTH(LOG_PR_COUNT - LOG_PRF_BANK_COUNT)
            ) READ_PORT1_UPPER_PR_MUX_ONE_HOT (
                .sel_one_hot(arbiter_read_req_port1_ack_by_bank_by_rr[read_bank]),
                .data_by_requestor(deq_read_req_upper_PR_by_rr),
                .selected_data(array_read_port1_upper_PR_by_bank[read_bank])
            );
        end
    endgenerate

    always_comb begin
        read_resp_valid_by_rr = deq_read_req_ready_by_rr;

        read_resp_data_by_rr = '0;
        for (int rr = 0; rr < PRF_RR_COUNT; rr++) begin
            for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
                if (arbiter_read_req_port0_ack_by_bank_by_rr[bank][rr]) begin
                    read_resp_data_by_rr[rr] |= array_read_port0_data_by_bank[bank];
                end
                if (arbiter_read_req_port1_ack_by_bank_by_rr[bank][rr]) begin
                    read_resp_data_by_rr[rr] |= array_read_port1_data_by_bank[bank];
                end
            end
        end
    end

    // ----------------------------------------------------------------
    // Writeback Logic:

    genvar input_buffer_wr;
    generate
        for (input_buffer_wr = 0; input_buffer_wr < PRF_WR_COUNT; input_buffer_wr++) begin : write_req_input_buffers
            q_fast_ready #(
                .DATA_WIDTH(1 + 1 + 32 + LOG_PR_COUNT-LOG_PRF_BANK_COUNT + PRF_BANK_COUNT + LOG_ROB_ENTRIES),
                .NUM_ENTRIES(PRF_WR_INPUT_BUFFER_SIZE)
            ) WRITE_REQ_INPUT_BUFFER (
                .CLK(CLK),
                .nRST(nRST),
                .enq_valid(enq_write_req_valid_by_wr[input_buffer_wr]),
                .enq_data({
                    enq_write_req_perform_write_by_wr[input_buffer_wr],
                    enq_write_req_send_complete_by_wr[input_buffer_wr],
                    enq_write_req_data_by_wr[input_buffer_wr],
                    enq_write_req_upper_PR_by_wr[input_buffer_wr],
                    enq_write_req_bank_mask_by_wr[input_buffer_wr],
                    enq_write_req_ROB_index_by_wr[input_buffer_wr]
                }),
                .enq_ready(enq_write_req_ready_by_wr[input_buffer_wr]),
                .deq_valid(deq_write_req_valid_by_wr[input_buffer_wr]),
                .deq_data({
                    deq_write_req_perform_write_by_wr[input_buffer_wr],
                    deq_write_req_send_complete_by_wr[input_buffer_wr],
                    deq_write_req_data_by_wr[input_buffer_wr],
                    deq_write_req_upper_PR_by_wr[input_buffer_wr],
                    deq_write_req_bank_mask_by_wr[input_buffer_wr],
                    deq_write_req_ROB_index_by_wr[input_buffer_wr]
                }),
                .deq_ready(deq_write_req_ready_by_wr[input_buffer_wr])
            );
        end
    endgenerate

    always_comb begin
        // check for a bypass
        bypass_arbiter_write_req_ack_by_wr = '0;
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            bypass_arbiter_write_req_ack_by_wr |= bypass_arbiter_write_req_ack_by_bank_by_wr[bank];
        end

        // only enq if didn't get bypass -> queue arbiter req present for relevant bank or this bypass arbiter req not ack'd
        enq_write_req_valid_by_wr = WB_valid_by_wr;
        for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
            enq_write_req_valid_by_wr[wr] &= (
                queue_arbiter_write_req_present_by_bank[WB_PR_by_wr[wr][LOG_PRF_BANK_COUNT-1:0]]
                | ~bypass_arbiter_write_req_ack_by_wr[wr]);
        end
        enq_write_req_send_complete_by_wr = WB_send_complete_by_wr;
        enq_write_req_data_by_wr = WB_data_by_wr;
        for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
            enq_write_req_perform_write_by_wr[wr] = WB_PR_by_wr[wr] != 0;
            enq_write_req_upper_PR_by_wr[wr] = WB_PR_by_wr[wr][LOG_PR_COUNT-1:LOG_PRF_BANK_COUNT];
            enq_write_req_bank_mask_by_wr[wr] = '0;
            enq_write_req_bank_mask_by_wr[wr][WB_PR_by_wr[wr][LOG_PRF_BANK_COUNT-1:0]] = 1'b1;
        end
        enq_write_req_ROB_index_by_wr = WB_ROB_index_by_wr;

        // even with bypass, readiness simply follows enq ready
        WB_ready_by_wr = enq_write_req_ready_by_wr;

        // demux write req's to arbiter banks
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
                queue_arbiter_write_req_valid_by_bank_by_wr[bank][wr] = deq_write_req_valid_by_wr[wr] & deq_write_req_bank_mask_by_wr[wr][bank];
                bypass_arbiter_write_req_valid_by_bank_by_wr[bank][wr] = WB_valid_by_wr[wr] & enq_write_req_bank_mask_by_wr[wr][bank];
            end
        end

        // retrieve arbiter bank ack's for input buffer deq ready's
        for (int wr = 0; wr < PRF_WR_COUNT; wr++) begin
            deq_write_req_ready_by_wr[wr] = '0;
            for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
                deq_write_req_ready_by_wr[wr] |= queue_arbiter_write_req_ack_by_bank_by_wr[bank][wr];
            end
        end
    end

    genvar write_bank;
    generate
        for (write_bank = 0; write_bank < PRF_BANK_COUNT; write_bank++) begin : write_arbiters

            // queue arbiter
                // must be fair -> round robin
            arbiter_rr #(
                .REQUESTOR_COUNT(PRF_WR_COUNT)
            ) QUEUE_WRITE_ARBITER (
                .CLK(CLK),
                .nRST(nRST),
                .req_vec(queue_arbiter_write_req_valid_by_bank_by_wr[write_bank]),
                .req_present(queue_arbiter_write_req_present_by_bank[write_bank]),
                .ack_ready(1'b1),
                .ack_one_hot(queue_arbiter_write_req_ack_by_bank_by_wr[write_bank])
            );

            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(1)
            ) QUEUE_WRITE_PERFORM_WRITE_MUX_ONE_HOT (
                .sel_one_hot(queue_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(deq_write_req_perform_write_by_wr),
                .selected_data(queue_selected_write_perform_write_by_bank[write_bank])
            );
            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(1)
            ) QUEUE_WRITE_SEND_COMPLETE_MUX_ONE_HOT (
                .sel_one_hot(queue_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(deq_write_req_send_complete_by_wr),
                .selected_data(queue_selected_write_send_complete_by_bank[write_bank])
            );
            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(32)
            ) QUEUE_WRITE_DATA_MUX_ONE_HOT (
                .sel_one_hot(queue_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(deq_write_req_data_by_wr),
                .selected_data(queue_selected_write_data_by_bank[write_bank])
            );
            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(LOG_PR_COUNT - LOG_PRF_BANK_COUNT)
            ) QUEUE_WRITE_UPPER_PR_MUX_ONE_HOT (
                .sel_one_hot(queue_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(deq_write_req_upper_PR_by_wr),
                .selected_data(queue_selected_write_upper_PR_by_bank[write_bank])
            );
            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(LOG_ROB_ENTRIES)
            ) QUEUE_WRITE_ROB_INDEX_MUX_ONE_HOT (
                .sel_one_hot(queue_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(deq_write_req_ROB_index_by_wr),
                .selected_data(queue_selected_write_ROB_index_by_bank[write_bank])
            );

            // bypass arbiter
                // simple and fast ideal -> static priority
            pe_lsb #(
                .WIDTH(PRF_WR_COUNT)
            ) BYPASS_WRITE_ARBITER (
                .req_vec(bypass_arbiter_write_req_valid_by_bank_by_wr[write_bank]),
                .ack_one_hot(bypass_arbiter_write_req_ack_by_bank_by_wr[write_bank])
            );

            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(1)
            ) BYPASS_WRITE_PERFORM_WRITE_MUX_ONE_HOT (
                .sel_one_hot(bypass_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(enq_write_req_perform_write_by_wr),
                .selected_data(bypass_selected_write_perform_write_by_bank[write_bank])
            );
            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(1)
            ) BYPASS_WRITE_SEND_COMPLETE_MUX_ONE_HOT (
                .sel_one_hot(bypass_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(enq_write_req_send_complete_by_wr),
                .selected_data(bypass_selected_write_send_complete_by_bank[write_bank])
            );
            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(32)
            ) BYPASS_WRITE_DATA_MUX_ONE_HOT (
                .sel_one_hot(bypass_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(enq_write_req_data_by_wr),
                .selected_data(bypass_selected_write_data_by_bank[write_bank])
            );
            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(LOG_PR_COUNT - LOG_PRF_BANK_COUNT)
            ) BYPASS_WRITE_UPPER_PR_MUX_ONE_HOT (
                .sel_one_hot(bypass_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(enq_write_req_upper_PR_by_wr),
                .selected_data(bypass_selected_write_upper_PR_by_bank[write_bank])
            );
            mux_one_hot #(
                .COUNT(PRF_WR_COUNT),
                .WIDTH(LOG_ROB_ENTRIES)
            ) BYPASS_WRITE_ROB_INDEX_MUX_ONE_HOT (
                .sel_one_hot(bypass_arbiter_write_req_ack_by_bank_by_wr[write_bank]),
                .data_by_requestor(enq_write_req_ROB_index_by_wr),
                .selected_data(bypass_selected_write_ROB_index_by_bank[write_bank])
            );
        end
    endgenerate

    always_comb begin
        for (int bank = 0; bank < PRF_BANK_COUNT; bank++) begin
            queue_selected_write_valid_by_bank[bank] = queue_arbiter_write_req_present_by_bank[bank];
            bypass_selected_write_valid_by_bank[bank] = |bypass_arbiter_write_req_valid_by_bank_by_wr[bank];

            selected_write_valid_by_bank[bank] = queue_selected_write_valid_by_bank[bank] | bypass_selected_write_valid_by_bank[bank];
            // select queue arbitration if present else bypass
            if (queue_selected_write_valid_by_bank[bank]) begin
                selected_write_perform_write_by_bank[bank] = queue_selected_write_perform_write_by_bank[bank];
                selected_write_send_complete_by_bank[bank] = queue_selected_write_send_complete_by_bank[bank];
                selected_write_data_by_bank[bank] = queue_selected_write_data_by_bank[bank];
                selected_write_upper_PR_by_bank[bank] = queue_selected_write_upper_PR_by_bank[bank];
                selected_write_ROB_index_by_bank[bank] = queue_selected_write_ROB_index_by_bank[bank];
            end
            else begin
                selected_write_perform_write_by_bank[bank] = bypass_selected_write_perform_write_by_bank[bank];
                selected_write_send_complete_by_bank[bank] = bypass_selected_write_send_complete_by_bank[bank];
                selected_write_data_by_bank[bank] = bypass_selected_write_data_by_bank[bank];
                selected_write_upper_PR_by_bank[bank] = bypass_selected_write_upper_PR_by_bank[bank];
                selected_write_ROB_index_by_bank[bank] = bypass_selected_write_ROB_index_by_bank[bank];
            end
        end
    end

    // array write
    // always_comb begin
    //     array_write_valid_by_bank = selected_write_valid_by_bank & selected_write_perform_write_by_bank;
    //         // must be forced 0 for PRF0
    //     array_write_upper_PR_by_bank = selected_write_upper_PR_by_bank;
    //     array_write_data_by_bank = selected_write_data_by_bank;
    // end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            array_write_valid_by_bank <= '0;
            array_write_upper_PR_by_bank <= '0;
            array_write_data_by_bank <= '0;
        end
        else begin
            array_write_valid_by_bank <= selected_write_valid_by_bank & selected_write_perform_write_by_bank;
                // must be forced 0 for PRF0
            array_write_upper_PR_by_bank <= selected_write_upper_PR_by_bank;
            array_write_data_by_bank <= selected_write_data_by_bank;
        end
    end

    // WB bus broadcast
        // can switch this to registered if too slow, but will slow down IPC for dependent forward data paths
    // always_comb begin
    //     WB_bus_valid_by_bank = selected_write_valid_by_bank;
    //         // doesn't have to be forced 0 for PRF0
    //     WB_bus_upper_PR_by_bank = selected_write_upper_PR_by_bank;
    // end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            WB_bus_valid_by_bank <= '0;
            WB_bus_upper_PR_by_bank <= '0;
            WB_bus_data_by_bank <= '0;
        end
        else begin
            WB_bus_valid_by_bank <= selected_write_valid_by_bank;
                // doesn't have to be forced 0 for PRF0
            WB_bus_upper_PR_by_bank <= selected_write_upper_PR_by_bank;
            WB_bus_data_by_bank <= selected_write_data_by_bank;
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            forward_data_bus_by_bank <= '0;
            complete_bus_valid_by_bank <= 1'b0;
            complete_bus_ROB_index_by_bank <= 0;
        end
        else begin
            forward_data_bus_by_bank <= WB_bus_data_by_bank;
            complete_bus_valid_by_bank <= selected_write_valid_by_bank & selected_write_send_complete_by_bank;
                // don't want forced PRF 0 writes invalid
            complete_bus_ROB_index_by_bank <= selected_write_ROB_index_by_bank;
        end    
    end

    // ----------------------------------------------------------------
    // Memory Array Logic:

    // create RAM array for each bank
    genvar ram_bank;
    generate
        for (ram_bank = 0; ram_bank < PRF_BANK_COUNT; ram_bank++) begin : ram_banks
            // DistRAM using curr's
            distram_2rport_1wport #(
                .INNER_WIDTH(32),
                .OUTER_WIDTH(PR_COUNT/PRF_BANK_COUNT)
            ) DISTRAM (
                .CLK(CLK),
                .port0_rindex(array_read_port0_upper_PR_by_bank[ram_bank]),
                .port0_rdata(array_read_port0_data_by_bank[ram_bank]),
                .port1_rindex(array_read_port1_upper_PR_by_bank[ram_bank]),
                .port1_rdata(array_read_port1_data_by_bank[ram_bank]),
                .wen(array_write_valid_by_bank[ram_bank]),
                .windex(array_write_upper_PR_by_bank[ram_bank]),
                .wdata(array_write_data_by_bank[ram_bank])
            );
        end
    endgenerate

endmodule
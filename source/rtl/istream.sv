/*
    Filename: istream.sv
    Author: zlagpacan
    Description: RTL for Instruction Stream
    Spec: LOROF/spec/design/istream.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module istream #(
    parameter ISTREAM_SETS = 8,
    parameter INIT_PC = 32'h0
) (

    // seq
    input logic CLK,
    input logic nRST,

    // SENQ stage
    input logic                                 valid_SENQ,
    input logic [7:0]                           valid_by_fetch_2B_SENQ,
    input logic [7:0]                           one_hot_redirect_by_fetch_2B_SENQ,
    input logic [7:0][15:0]                     instr_2B_by_fetch_2B_SENQ,
    input logic [7:0][BTB_PRED_INFO_WIDTH-1:0]  pred_info_by_fetch_2B_SENQ,
    input logic [7:0]                           pred_lru_by_fetch_2B_SENQ,
    input logic [7:0][MDPT_INFO_WIDTH-1:0]      mdp_info_by_fetch_2B_SENQ,
    input logic [31:0]                          after_PC_SENQ,
    input logic [LH_LENGTH-1:0]                 LH_SENQ,
    input logic [GH_LENGTH-1:0]                 GH_SENQ,
    input logic [RAS_INDEX_WIDTH-1:0]           ras_index_SENQ,
    input logic                                 page_fault_SENQ,
    input logic                                 access_fault_SENQ,

    // SENQ feedback
    output logic stall_SENQ,

    // SDEQ stage
    output logic                                        valid_SDEQ,
    output logic [3:0]                                  valid_by_way_SDEQ,
    output logic [3:0]                                  uncompressed_by_way_SDEQ,
    output logic [3:0][1:0][15:0]                       instr_2B_by_way_by_chunk_SDEQ,
    output logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0]    pred_info_by_way_by_chunk_SDEQ,
    output logic [3:0][1:0]                             pred_lru_by_way_by_chunk_SDEQ,
    output logic [3:0][1:0]                             redirect_by_way_by_chunk_SDEQ,
    output logic [3:0][1:0][31:0]                       pred_PC_by_way_by_chunk_SDEQ,
    output logic [3:0][1:0]                             page_fault_by_way_by_chunk_SDEQ,
    output logic [3:0][1:0]                             access_fault_by_way_by_chunk_SDEQ,
    output logic [3:0][MDPT_INFO_WIDTH-1:0]             mdp_info_by_way_SDEQ,
    output logic [3:0][31:0]                            PC_by_way_SDEQ,
    output logic [3:0][LH_LENGTH-1:0]                   LH_by_way_SDEQ,
    output logic [3:0][GH_LENGTH-1:0]                   GH_by_way_SDEQ,
    output logic [3:0][RAS_INDEX_WIDTH-1:0]             ras_index_by_way_SDEQ,

    // SDEQ feedback
    input logic stall_SDEQ,

    // restart
    input logic         restart,
    input logic [31:0]  restart_PC
);

    // ----------------------------------------------------------------
    // Signals:

    typedef struct packed {
        logic [13:0]    upper_bits;
        logic [1:0]     lsb2;
    } instr_2B_t;

    typedef struct packed {
        logic                               redirect;
        instr_2B_t                          instr_2B;
        logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info;
        logic                               pred_lru;
        logic [MDPT_INFO_WIDTH-1:0]         mdp_info;
    } instr_chunk_t;

    typedef struct packed {
        instr_chunk_t [7:0]             chunks;
        logic [31:0]                    after_PC;
        logic [LH_LENGTH-1:0]           LH;
        logic [GH_LENGTH-1:0]           GH;
        logic [RAS_INDEX_WIDTH-1:0]     ras_index;
        logic                           page_fault;
        logic                           access_fault;
    } stream_set_t;

    stream_set_t [ISTREAM_SETS-1:0] stream_set_array, next_stream_set_array;

    typedef struct packed {
        logic                               msb;
        logic [ISTREAM_INDEX_WIDTH-1:0]     index;
    } stream_ptr_t;

    stream_ptr_t stream_enq_ptr, next_stream_enq_ptr;
    stream_ptr_t stream_deq0_ptr, next_stream_deq0_ptr;
    stream_ptr_t stream_deq1_ptr, next_stream_deq1_ptr;

    logic stream_full;
    logic stream_empty0;
    logic stream_empty1;

    logic [31:0] deq0_PC, next_deq0_PC;

    logic [7:0] enq_set_valid_vec;
    logic [7:0] enq_set_uncompressed_vec;
    logic [7:0] enq_set_marker_vec;
    logic [8:0] enq_set_last_marker_uncompressed_vec;

    logic uncompressed_carry_in_state, next_uncompressed_carry_in_state;

    logic [ISTREAM_SETS-1:0][7:0] valid_set_vec_array, next_valid_set_vec_array;
    logic [ISTREAM_SETS-1:0][7:0] uncompressed_set_vec_array, next_uncompressed_set_vec_array;
    logic [ISTREAM_SETS-1:0][7:0] marker_set_vec_array, next_marker_set_vec_array;

    logic [ISTREAM_SETS-1:0] set_valid_array, next_set_valid_array;
    logic [ISTREAM_SETS-1:0] set_enq_one_hot;

    logic [LH_LENGTH-1:0] LH_deq0;
    logic [LH_LENGTH-1:0] LH_deq1;
    logic [GH_LENGTH-1:0] GH_deq0;
    logic [GH_LENGTH-1:0] GH_deq1;
    logic [RAS_INDEX_WIDTH-1:0] ras_index_deq0;
    logic [RAS_INDEX_WIDTH-1:0] ras_index_deq1;

    logic [15:0]                            valid_vec;
    logic [15:0]                            uncompressed_vec;
    logic [15:0]                            redirect_vec;
    instr_2B_t [15:0]                       instr_2B_vec;
    logic [15:0][BTB_PRED_INFO_WIDTH-1:0]   pred_info_vec;
    logic [15:0]                            pred_lru_vec;
    logic [15:0][MDPT_INFO_WIDTH-1:0]       mdp_info_vec;
    logic [15:0][31:0]                      pred_PC_vec;
    logic [15:0]                            page_fault_vec;
    logic [15:0]                            access_fault_vec;

    logic [3:0]         lower_present_by_way;
    logic [3:0][15:0]   lower_req_vec_by_way;
    logic [3:0][15:0]   lower_ack_one_hot_by_way;
    logic [3:0][15:0]   lower_cold_ack_mask_by_way;
    logic [3:0][3:0]    lower_ack_index_by_way;
    
    logic [3:0]         upper_present_by_way;
    logic [3:0][15:0]   upper_req_vec_by_way;
    logic [3:0][15:0]   upper_ack_one_hot_by_way;
    logic [3:0][15:0]   upper_cold_ack_mask_by_way;
    logic [3:0][3:0]    upper_ack_index_by_way;

    logic [15:0]    marker_vec;
    logic [15:0]    last_marker_uncompressed_vec;
    logic [15:0]    ack_vec;

    logic [15:0]    valid_mask_vec;

    logic [3:0]     marker_lower_countones;
    logic [7:0]     marker_lower_and_uncompressed_mask_vec;
    logic           valid_mask_neq_marker_lower_and_uncompressed_mask;

    logic [3:0]     marker_upper_countones;
    logic [15:0]    marker_total_and_uncompressed_mask_vec;
    logic           valid_mask_neq_marker_total_and_uncompressed_mask;

    logic deq0_done;
    logic deq1_done;

    // ----------------------------------------------------------------
    // deQ Helper Logic: 

    always_comb begin

        valid_vec[7:0] = valid_set_vec_array[0];
        uncompressed_vec[7:0] = uncompressed_set_vec_array[0];

        // align deq ptr0 into vec
        for (int i = 0; i < 8; i++) begin
            redirect_vec[i] = stream_set_array[stream_deq0_ptr.index].chunks[i].redirect;
            instr_2B_vec[i] = stream_set_array[stream_deq0_ptr.index].chunks[i].instr_2B;
            pred_info_vec[i] = stream_set_array[stream_deq0_ptr.index].chunks[i].pred_info;
            pred_lru_vec[i] = stream_set_array[stream_deq0_ptr.index].chunks[i].pred_lru;
            mdp_info_vec[i] = stream_set_array[stream_deq0_ptr.index].chunks[i].mdp_info;
            page_fault_vec[i] = stream_set_array[stream_deq0_ptr.index].page_fault;
            access_fault_vec[i] = stream_set_array[stream_deq0_ptr.index].access_fault;
        end

        valid_vec[15:8] = valid_set_vec_array[1];
        uncompressed_vec[15:8] = uncompressed_set_vec_array[1];

        // align deq ptr1 into vec
        for (int j = 0; j < 8; j++) begin
            redirect_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].chunks[j].redirect;
            instr_2B_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].chunks[j].instr_2B;
            pred_info_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].chunks[j].pred_info;
            pred_lru_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].chunks[j].pred_lru;
            mdp_info_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].chunks[j].mdp_info;
            page_fault_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].page_fault;
            access_fault_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].access_fault;
        end
    end

    always_comb begin

        // align deq ptr0 into vec, redirecting as needed
        for (int i = 0; i < 8; i++) begin
            if (redirect_vec[i]) begin
                pred_PC_vec[i] = {
                    stream_set_array[stream_deq0_ptr.index].after_PC[31:1],
                    1'b0
                };
            end 
            else begin
                pred_PC_vec[i] = {
                    deq0_PC[31:4],
                    i[2:0] + 3'h1,
                    1'b0
                };
            end
        end

        // align deq ptr1 into vec, redirecting as needed
        for (int j = 0; j < 8; j++) begin
            if (redirect_vec[j + 8]) begin
                pred_PC_vec[j + 8] = {
                    stream_set_array[stream_deq1_ptr.index].after_PC[31:1],
                    1'b0
                };
            end 
            else begin
                pred_PC_vec[j + 8] = {
                    stream_set_array[stream_deq0_ptr.index].after_PC[31:4],
                    j[2:0] + 3'h9,
                    1'b0
                };
            end
        end
    end

    always_comb begin

        marker_vec[7:0] = marker_set_vec_array[0];
        marker_vec[15:8] = marker_set_vec_array[1];

        enq_set_last_marker_uncompressed_vec[0] = uncompressed_carry_in_state;

        for (int i = 0; i < 8; i++) begin
            if (enq_set_valid_vec[i]) begin
                if (enq_set_last_marker_uncompressed_vec[i]) begin
                    enq_set_last_marker_uncompressed_vec[i+1] = 1'b0;
                    enq_set_marker_vec[i] = 1'b0;
                end else begin
                    enq_set_last_marker_uncompressed_vec[i+1] = enq_set_uncompressed_vec[i];
                    enq_set_marker_vec[i] = 1'b1;
                end
            end else begin
                enq_set_last_marker_uncompressed_vec[i+1] = enq_set_last_marker_uncompressed_vec[i];
                enq_set_marker_vec[i] = 1'b0;
            end
        end
    end

    // lower way 0: can guarantee in lower 8
    pe_lsb #(
        .WIDTH(8),
        .USE_ONE_HOT(1),
        .USE_COLD(1),
        .USE_INDEX(1)
    ) WAY_LOWER (
        .req_vec(lower_req_vec_by_way[0][7:0]),
        .ack_one_hot(lower_ack_one_hot_by_way[0][7:0]),
        .ack_mask(),
        .cold_ack_mask(lower_cold_ack_mask_by_way[0][7:0]),
        .ack_index(lower_ack_index_by_way[0][2:0])
    );

    assign lower_ack_one_hot_by_way[0][15:8] = 8'h0;
    assign lower_cold_ack_mask_by_way[0][15:8] = {8{|lower_req_vec_by_way[0][7:0]}};
    assign lower_ack_index_by_way[0][3] = 1'b0;

    // upper by way
    pe_lsb #(
        .WIDTH(16),
        .USE_ONE_HOT(1),
        .USE_COLD(1),
        .USE_INDEX(1)
    ) WAY_UPPER (
        .req_vec(upper_req_vec_by_way[0]),
        .ack_one_hot(upper_ack_one_hot_by_way[0]),
        .ack_mask(),
        .cold_ack_mask(upper_cold_ack_mask_by_way[0]),
        .ack_index(upper_ack_index_by_way[0])
    );

    genvar way;
    generate
        for (way = 1; way < 4; way++) begin : lower_pe_upper_pe_by_way

            // lower by way
            pe_lsb #(
                .WIDTH(16),
                .USE_ONE_HOT(1),
                .USE_COLD(1),
                .USE_INDEX(1)
            ) WAY_LOWER (
                .req_vec(lower_req_vec_by_way[way]),
                .ack_one_hot(lower_ack_one_hot_by_way[way]),
                .ack_mask(),
                .cold_ack_mask(lower_cold_ack_mask_by_way[way]),
                .ack_index(lower_ack_index_by_way[way])
            );

            // upper by way
            pe_lsb #(
                .WIDTH(16),
                .USE_ONE_HOT(1),
                .USE_COLD(1),
                .USE_INDEX(1)
            ) WAY_UPPER (
                .req_vec(upper_req_vec_by_way[way]),
                .ack_one_hot(upper_ack_one_hot_by_way[way]),
                .ack_mask(),
                .cold_ack_mask(upper_cold_ack_mask_by_way[way]),
                .ack_index(upper_ack_index_by_way[way])
            );
        end
    endgenerate

    always_comb begin

        valid_SDEQ = 1'b0;
        valid_by_way_SDEQ = 4'b0000;
        ack_vec = 16'h0;

        // way 0:
        lower_req_vec_by_way[0] = marker_vec; // starting point
        upper_req_vec_by_way[0] = valid_vec & lower_cold_ack_mask_by_way[0];

        // lower_req_vec_by_way[1] = marker_vec & lower_cold_ack_mask_by_way[0];
        lower_req_vec_by_way[1] = lower_req_vec_by_way[0] & ~lower_ack_one_hot_by_way[0];
        upper_req_vec_by_way[1] = valid_vec & lower_cold_ack_mask_by_way[1];

        // lower_req_vec_by_way[2] = marker_vec & lower_cold_ack_mask_by_way[1];
        lower_req_vec_by_way[2] = lower_req_vec_by_way[1] & ~lower_ack_one_hot_by_way[1];
        upper_req_vec_by_way[2] = valid_vec & lower_cold_ack_mask_by_way[2];

        // lower_req_vec_by_way[3] = marker_vec & lower_cold_ack_mask_by_way[2];
        lower_req_vec_by_way[3] = lower_req_vec_by_way[2] & ~lower_ack_one_hot_by_way[2];
        upper_req_vec_by_way[3] = valid_vec & lower_cold_ack_mask_by_way[3];

        for (int way = 0; way < 4; way++) begin

            lower_present_by_way[way] = |lower_req_vec_by_way[way];
            upper_present_by_way[way] = |upper_req_vec_by_way[way];

            // check for lower uncompressed
                // need lower and upper present
            if (lower_present_by_way[way] & uncompressed_by_way_SDEQ[way]) begin

                // need upper present
                if (upper_present_by_way[way]) begin

                    // guaranteed valid for way 0 valid
                    if (way == 0) begin
                        valid_SDEQ = set_valid_array[0];
                    end

                    // mark way valid
                    valid_by_way_SDEQ[way] = 1'b1;

                    // ack lower and upper
                    ack_vec |= lower_ack_one_hot_by_way[way];
                    ack_vec |= upper_ack_one_hot_by_way[way];
                end

                // otherwise, no upper, this way failed
                else begin

                    // mark way invalid
                    valid_by_way_SDEQ[way] = 1'b0;
                end
            end

            // otherwise, lower compressed
                // only need lower present
            else if (lower_present_by_way[way]) begin

                // guaranteed valid for way 0 valid
                if (way == 0) begin
                    valid_SDEQ = set_valid_array[0];
                end

                // mark way valid
                valid_by_way_SDEQ[way] = 1'b1;

                // ack lower
                ack_vec |= lower_ack_one_hot_by_way[way];
            end

            // otherwise, no lower, way fail
            else begin

                // mark way invalid
                valid_by_way_SDEQ[way] = 1'b0;
            end
        end
    end

    assign LH_deq0 = stream_set_array[stream_deq0_ptr.index].LH;
    assign LH_deq1 = stream_set_array[stream_deq1_ptr.index].LH;
    assign GH_deq0 = stream_set_array[stream_deq0_ptr.index].GH;
    assign GH_deq1 = stream_set_array[stream_deq1_ptr.index].GH;
    assign ras_index_deq0 = stream_set_array[stream_deq0_ptr.index].ras_index;
    assign ras_index_deq1 = stream_set_array[stream_deq1_ptr.index].ras_index;

    always_comb begin
        for (int way = 0; way < 4; way++) begin

            // uncompressed and mdp info follow lower:
            uncompressed_by_way_SDEQ[way] = |(uncompressed_vec & lower_ack_one_hot_by_way[way]);
            mdp_info_by_way_SDEQ[way] = '0;
            for (int i = 0; i < 16; i++) begin
                if (lower_ack_one_hot_by_way[way][i]) begin
                    mdp_info_by_way_SDEQ[way] |= mdp_info_vec[i];
                end
            end

            // instr, pred info, pred lru, pred PC, page fault, access fault follow lower to chunk 0, upper to chunk 1:
            instr_2B_by_way_by_chunk_SDEQ[way] = '0;
            pred_info_by_way_by_chunk_SDEQ[way] = '0;
            pred_lru_by_way_by_chunk_SDEQ[way] = '0;
            redirect_by_way_by_chunk_SDEQ[way] = '0;
            pred_PC_by_way_by_chunk_SDEQ[way] = '0;
            page_fault_by_way_by_chunk_SDEQ[way] = '0;
            access_fault_by_way_by_chunk_SDEQ[way] = '0;
            for (int i = 0; i < 16; i++) begin
                if (lower_ack_one_hot_by_way[way][i]) begin
                    instr_2B_by_way_by_chunk_SDEQ[way][0] |= instr_2B_vec[i];
                    pred_info_by_way_by_chunk_SDEQ[way][0] |= pred_info_vec[i];
                    pred_lru_by_way_by_chunk_SDEQ[way][0] |= pred_lru_vec[i];
                    redirect_by_way_by_chunk_SDEQ[way][0] |= redirect_vec[i];
                    pred_PC_by_way_by_chunk_SDEQ[way][0] |= pred_PC_vec[i];
                    page_fault_by_way_by_chunk_SDEQ[way][0] |= page_fault_vec[i];
                    access_fault_by_way_by_chunk_SDEQ[way][0] |= access_fault_vec[i];
                end
                if (upper_ack_one_hot_by_way[way][i]) begin
                    instr_2B_by_way_by_chunk_SDEQ[way][1] |= instr_2B_vec[i];
                    pred_info_by_way_by_chunk_SDEQ[way][1] |= pred_info_vec[i];
                    pred_lru_by_way_by_chunk_SDEQ[way][1] |= pred_lru_vec[i];
                    redirect_by_way_by_chunk_SDEQ[way][1] |= redirect_vec[i];
                    pred_PC_by_way_by_chunk_SDEQ[way][1] |= pred_PC_vec[i];
                    page_fault_by_way_by_chunk_SDEQ[way][1] |= page_fault_vec[i];
                    access_fault_by_way_by_chunk_SDEQ[way][1] |= access_fault_vec[i];
                end
            end

            // PC follows lower set index
            if (|lower_req_vec_by_way[way][7:0]) begin
                PC_by_way_SDEQ[way] = {
                    deq0_PC[31:4],
                    lower_ack_index_by_way[way][2:0],
                    1'b0
                };
            end else begin
                PC_by_way_SDEQ[way] = {
                    stream_set_array[stream_deq0_ptr.index].after_PC[31:4],
                    lower_ack_index_by_way[way][2:0],
                    1'b0
                };
            end

            // LH, GH, ras_index follow upper set index
                // this relies on no redirection mid-instruction to be correct
                    // if do have this, will be able to detect problem via instr fetch fault in decoder
            if (
                (|lower_req_vec_by_way[way][6:0]) 
                | 
                (~uncompressed_vec[7] & lower_req_vec_by_way[way][7])
            ) begin
                LH_by_way_SDEQ[way] = LH_deq0;
                GH_by_way_SDEQ[way] = GH_deq0;
                ras_index_by_way_SDEQ[way] = ras_index_deq0;
            end else begin
                LH_by_way_SDEQ[way] = LH_deq1;
                GH_by_way_SDEQ[way] = GH_deq1;
                ras_index_by_way_SDEQ[way] = ras_index_deq1;
            end
        end
    end

    assign stream_empty0 = ~set_valid_array[0];
    assign stream_empty1 = ~set_valid_array[1];

    always_comb begin

        valid_mask_vec[15] = valid_vec[15];
        for (int i = 14; i >= 0; i--) begin
            valid_mask_vec[i] = 
                valid_vec[i] 
                | 
                valid_mask_vec[i+1]
            ;
        end

        valid_mask_neq_marker_lower_and_uncompressed_mask = 1'b0;
        marker_lower_and_uncompressed_mask_vec[7] = marker_vec[7] & uncompressed_vec[7];
        for (int i = 14; i >= 0; i--) begin
            
            if (i <= 6) begin
                marker_lower_and_uncompressed_mask_vec[i] = 
                    (marker_vec[i] & uncompressed_vec[i]) 
                    | 
                    marker_lower_and_uncompressed_mask_vec[i+1]
                ;
            end

            if (i >= 8) begin
                if (valid_mask_vec[i]) begin
                    valid_mask_neq_marker_lower_and_uncompressed_mask = 1'b1;
                end
            end else begin
                if (valid_mask_vec[i] & ~marker_lower_and_uncompressed_mask_vec[i]) begin
                    valid_mask_neq_marker_lower_and_uncompressed_mask = 1'b1;
                end
            end
        end

        valid_mask_neq_marker_total_and_uncompressed_mask = 1'b0;
        marker_total_and_uncompressed_mask_vec[15] = marker_vec[15] & uncompressed_vec[15];
        for (int i = 14; i >= 0; i--) begin

            marker_total_and_uncompressed_mask_vec[i] = 
                (marker_vec[i] & uncompressed_vec[i]) 
                | 
                marker_total_and_uncompressed_mask_vec[i+1]
            ;

            if (valid_mask_vec[i] & ~marker_total_and_uncompressed_mask_vec[i]) begin
                valid_mask_neq_marker_total_and_uncompressed_mask = 1'b1;
            end
        end
    end

    always_comb begin : countones_adders
        marker_lower_countones = 0;
        for (int i = 0; i < 8; i++) begin
            marker_lower_countones += marker_vec[i];
        end

        marker_upper_countones = 0;
        for (int i = 8; i < 16; i++) begin
            marker_upper_countones += marker_vec[i];
        end
    end
    
    always_comb begin
        
        deq0_done = 1'b0;
        if (marker_lower_countones <= 4) begin
            if (valid_mask_neq_marker_lower_and_uncompressed_mask) begin
                deq0_done = ~stream_empty0;
            end
        end

        deq1_done = 1'b0;
        if (marker_lower_countones + marker_upper_countones <= 4) begin
            if (valid_mask_neq_marker_total_and_uncompressed_mask) begin
                deq1_done = ~stream_empty1;
            end
        end
    end

    // ----------------------------------------------------------------
    // enQ Helper Logic: 

    // stall follows current ptr FIFO full check
    assign stream_full = 
        stream_enq_ptr.index == stream_deq0_ptr.index 
        & 
        stream_enq_ptr.msb != stream_deq0_ptr.msb
    ;

    assign stall_SENQ = stream_full;

    always_comb begin
        enq_set_valid_vec = valid_by_fetch_2B_SENQ;
        for (int i = 0; i < 8; i++) begin
            enq_set_uncompressed_vec[i] = instr_2B_by_fetch_2B_SENQ[i][1:0] == 2'b11;
        end
    end

    pe_lsb #(
        .WIDTH(ISTREAM_SETS),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_VALID_PE (
        .req_vec(~set_valid_array),
        .ack_one_hot(set_enq_one_hot)
    );

    // ----------------------------------------------------------------
    // FF Logic: 

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            stream_set_array <= '0;

            stream_enq_ptr <= '0;
            stream_deq0_ptr <= 0;
            stream_deq1_ptr <= 1;

            deq0_PC <= INIT_PC;

            set_valid_array <= '0;
            valid_set_vec_array <= '0;
            uncompressed_set_vec_array <= '0;
            marker_set_vec_array <= '0;
            uncompressed_carry_in_state <= 1'b0;
        end
        else if (restart) begin
            stream_set_array <= '0;

            stream_enq_ptr <= '0;
            stream_deq0_ptr <= 0;
            stream_deq1_ptr <= 1;

            deq0_PC <= restart_PC;

            set_valid_array <= '0;
            valid_set_vec_array <= '0;
            uncompressed_set_vec_array <= '0;
            marker_set_vec_array <= '0;
            uncompressed_carry_in_state <= 1'b0;
        end
        else begin
            stream_set_array <= next_stream_set_array;

            stream_enq_ptr <= next_stream_enq_ptr;
            stream_deq0_ptr <= next_stream_deq0_ptr;
            stream_deq1_ptr <= next_stream_deq1_ptr;

            deq0_PC <= next_deq0_PC;
            
            uncompressed_carry_in_state <= next_uncompressed_carry_in_state;

            // check double deQ
            if (~stall_SDEQ & deq0_done & deq1_done) begin

                for (int i = 0; i < ISTREAM_SETS-2; i++) begin
                    valid_set_vec_array[i] <= next_valid_set_vec_array[i+2];
                    uncompressed_set_vec_array[i] <= next_uncompressed_set_vec_array[i+2];
                    marker_set_vec_array[i] <= next_marker_set_vec_array[i+2];
                    set_valid_array[i] <= next_set_valid_array[i+2];
                end

                valid_set_vec_array[ISTREAM_SETS-2] <= 8'h0;
                uncompressed_set_vec_array[ISTREAM_SETS-2] <= 8'h0;
                marker_set_vec_array[ISTREAM_SETS-2] <= 8'h0;
                set_valid_array[ISTREAM_SETS-2] <= 1'b0;

                valid_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                uncompressed_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                marker_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                set_valid_array[ISTREAM_SETS-1] <= 1'b0;
            end

            // check single deQ
            else if (~stall_SDEQ & deq0_done) begin

                for (int i = 0; i < ISTREAM_SETS-1; i++) begin
                    valid_set_vec_array[i] <= next_valid_set_vec_array[i+1];
                    uncompressed_set_vec_array[i] <= next_uncompressed_set_vec_array[i+1];
                    marker_set_vec_array[i] <= next_marker_set_vec_array[i+1];
                    set_valid_array[i] <= next_set_valid_array[i+1];
                end

                valid_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                uncompressed_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                marker_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                set_valid_array[ISTREAM_SETS-1] <= 1'b0;
            end

            // otherwise, just take self
            else begin
                valid_set_vec_array <= next_valid_set_vec_array;
                uncompressed_set_vec_array <= next_uncompressed_set_vec_array;
                marker_set_vec_array <= next_marker_set_vec_array;
                set_valid_array <= next_set_valid_array;
            end
        end
    end

    // Next State Logic:
    always_comb begin
        
        next_stream_set_array = stream_set_array;

        next_stream_enq_ptr = stream_enq_ptr;
        next_stream_deq0_ptr = stream_deq0_ptr;
        next_stream_deq1_ptr = stream_deq1_ptr;

        next_deq0_PC = deq0_PC;

        next_uncompressed_carry_in_state = uncompressed_carry_in_state;

        // restart/flush handled in FF logic
            // act as if no restart/flush with next_* signals

        // enQ logic
        if (valid_SENQ & ~stall_SENQ) begin

            // enQ on stream
            for (int i = 0; i < 8; i++) begin
                next_stream_set_array[stream_enq_ptr.index].chunks[i].redirect = one_hot_redirect_by_fetch_2B_SENQ[i];
                next_stream_set_array[stream_enq_ptr.index].chunks[i].instr_2B = instr_2B_by_fetch_2B_SENQ[i];
                next_stream_set_array[stream_enq_ptr.index].chunks[i].pred_info = pred_info_by_fetch_2B_SENQ[i];
                next_stream_set_array[stream_enq_ptr.index].chunks[i].pred_lru = pred_lru_by_fetch_2B_SENQ[i];
                next_stream_set_array[stream_enq_ptr.index].chunks[i].mdp_info = mdp_info_by_fetch_2B_SENQ[i];
            end
            next_stream_set_array[stream_enq_ptr.index].after_PC = after_PC_SENQ;
            next_stream_set_array[stream_enq_ptr.index].LH = LH_SENQ;
            next_stream_set_array[stream_enq_ptr.index].GH = GH_SENQ;
            next_stream_set_array[stream_enq_ptr.index].ras_index = ras_index_SENQ;
            next_stream_set_array[stream_enq_ptr.index].page_fault = page_fault_SENQ;
            next_stream_set_array[stream_enq_ptr.index].access_fault = access_fault_SENQ;

            // incr enQ ptr
            next_stream_enq_ptr = stream_enq_ptr + 1;

            // update uncompressed carry in state
            next_uncompressed_carry_in_state = enq_set_last_marker_uncompressed_vec[8];
        end

        // deQ logic
        if (~stall_SDEQ) begin

            // set deq's:

            // deq0 and deq1: incr 2, take deq1 after PC
            if (deq0_done & deq1_done) begin
                next_stream_deq0_ptr = stream_deq0_ptr + 2;
                next_stream_deq1_ptr = stream_deq1_ptr + 2;
                next_deq0_PC = stream_set_array[stream_deq1_ptr.index].after_PC;
            end
            // only deq0: incr 1, take deq0 after PC
            else if (deq0_done) begin
                next_stream_deq0_ptr = stream_deq0_ptr + 1;
                next_stream_deq1_ptr = stream_deq1_ptr + 1;
                next_deq0_PC = stream_set_array[stream_deq0_ptr.index].after_PC;
            end
            // none: no change
            else begin
                next_stream_deq0_ptr = stream_deq0_ptr;
                next_stream_deq1_ptr = stream_deq1_ptr;
                next_deq0_PC = deq0_PC;
            end
        end
    end

    always_comb begin
        next_valid_set_vec_array = valid_set_vec_array;
        next_uncompressed_set_vec_array = uncompressed_set_vec_array;
        next_marker_set_vec_array = marker_set_vec_array;
        next_set_valid_array = set_valid_array;

        if (~stall_SDEQ) begin
            for (int i = 0; i < 8; i++) begin
                if (ack_vec[i]) begin
                    next_valid_set_vec_array[0][i] = 1'b0;
                    next_marker_set_vec_array[0][i] = 1'b0;
                end
            end
            for (int j = 0; j < 8; j++) begin
                if (ack_vec[j + 8]) begin
                    next_valid_set_vec_array[1][j] = 1'b0;
                    next_marker_set_vec_array[1][j] = 1'b0;
                end
            end
        end

        for (int i = 0; i < ISTREAM_SETS; i++) begin
            if (set_enq_one_hot[i]) begin
                next_set_valid_array[i] = valid_SENQ & ~stall_SENQ;
                next_valid_set_vec_array[i] = enq_set_valid_vec;
                next_uncompressed_set_vec_array[i] = enq_set_uncompressed_vec;
                next_marker_set_vec_array[i] = enq_set_marker_vec;
            end
        end
    end

endmodule
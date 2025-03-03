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
    parameter INIT_PC = 32'h80000000
) (

    // seq
    input logic CLK,
    input logic nRST,

    // SENQ stage
    input logic                                 valid_SENQ,
    input logic [7:0]                           valid_by_fetch_2B_SENQ,
    input logic [7:0][15:0]                     instr_2B_by_fetch_2B_SENQ,
    input logic [7:0][BTB_PRED_INFO_WIDTH-1:0]  pred_info_by_fetch_2B_SENQ,
    input logic [7:0]                           dep_pred_by_fetch_2B_SENQ,
    input logic [31:0]                          after_PC_SENQ,
    input logic [LH_LENGTH-1:0]                 LH_SENQ,
    input logic [GH_LENGTH-1:0]                 GH_SENQ,
    input logic [RAS_INDEX_WIDTH-1:0]           ras_index_SENQ,

    // SENQ feedback
    output logic stall_SENQ,

    // SDEQ stage
    output logic                                        valid_SDEQ,
    output logic [3:0]                                  valid_by_way_SDEQ,
    output logic [3:0]                                  uncompressed_by_way_SDEQ,
    output logic [3:0][1:0][15:0]                       instr_2B_by_way_by_chunk_SDEQ,
    output logic [3:0][1:0][BTB_PRED_INFO_WIDTH-1:0]    pred_info_by_way_by_chunk_SDEQ,
    output logic [3:0]                                  dep_pred_by_way_SDEQ,
    output logic [3:0][31:0]                            PC_by_way_SDEQ,
    output logic [3:0][LH_LENGTH-1:0]                   LH_by_way_SDEQ,
    output logic [3:0][GH_LENGTH-1:0]                   GH_by_way_SDEQ,
    output logic [3:0][RAS_INDEX_WIDTH-1:0]             ras_index_by_way_SDEQ,

    // SDEQ feedback
    input logic stall_SDEQ,

    // control
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
        instr_2B_t                          instr_2B;
        logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info;
        logic                               dep_pred;
    } instr_chunk_t;

    typedef struct packed {
        instr_chunk_t [7:0]             chunks;
        logic [27:0]                    after_PC28;
        logic [LH_LENGTH-1:0]           LH;
        logic [GH_LENGTH-1:0]           GH;
        logic [RAS_INDEX_WIDTH-1:0]     ras_index;
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

    logic [27:0] deq0_PC28, next_deq0_PC28;

    logic [7:0] enq_set_valid_vec;
    logic [7:0] enq_set_uncompressed_vec;

    logic [ISTREAM_SETS-1:0][7:0] valid_set_vec_array, next_valid_set_vec_array;
    logic [ISTREAM_SETS-1:0][7:0] uncompressed_set_vec_array, next_uncompressed_set_vec_array;

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
    instr_2B_t [15:0]                       instr_2B_vec;
    logic [15:0][BTB_PRED_INFO_WIDTH-1:0]   pred_info_vec;
    logic [15:0]                            dep_pred_vec;

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
            instr_2B_vec[i] = stream_set_array[stream_deq0_ptr.index].chunks[i].instr_2B;
            pred_info_vec[i] = stream_set_array[stream_deq0_ptr.index].chunks[i].pred_info;
            dep_pred_vec[i] = stream_set_array[stream_deq0_ptr.index].chunks[i].dep_pred;
        end

        valid_vec[15:8] = valid_set_vec_array[1];
        uncompressed_vec[15:8] = uncompressed_set_vec_array[1];

        // align deq ptr1 into vec
        for (int j = 0; j < 8; j++) begin
            instr_2B_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].chunks[j].instr_2B;
            pred_info_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].chunks[j].pred_info;
            dep_pred_vec[j + 8] = stream_set_array[stream_deq1_ptr.index].chunks[j].dep_pred;
        end
    end

    always_comb begin

        // marker vec
        marker_vec[0] = valid_vec[0];
        last_marker_uncompressed_vec[1] = valid_vec[0] & uncompressed_vec[0];

        // for (int i = 1; i <= 14; i++) begin
            // marker_vec[i] = valid_vec[i] & ~(marker_vec[i-1] & uncompressed_vec[i-1]);
            // marker_vec[i] = valid_vec[i] & ~last_marker_uncompressed_vec[i];
            
        for (int i = 1; i <= 15; i++) begin
            if (valid_vec[i]) begin
                if (last_marker_uncompressed_vec[i]) begin
                    if (i < 15) last_marker_uncompressed_vec[i+1] = 1'b0;
                    marker_vec[i] = 1'b0;
                end else begin
                    if (i < 15) last_marker_uncompressed_vec[i+1] = uncompressed_vec[i];
                    marker_vec[i] = 1'b1;
                end
            end else begin
                if (i < 15) last_marker_uncompressed_vec[i+1] = last_marker_uncompressed_vec[i];
                marker_vec[i] = 1'b0;
            end
        end

        // marker_vec[15] = valid_vec[15] & ~uncompressed_vec[15] & ~(marker_vec[14] & uncompressed_vec[14]);
        // marker_vec[15] = valid_vec[15] & ~(marker_vec[14] & uncompressed_vec[14]);
    end

    // lower way 0: can guarantee in lower 8
    pq_lsb #(
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
    pq_lsb #(
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
        for (way = 1; way < 4; way++) begin : lower_pq_upper_pq_by_way

            // lower by way
            pq_lsb #(
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
            pq_lsb #(
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
            if (lower_present_by_way[way] & |(uncompressed_vec & lower_ack_one_hot_by_way[way])) begin

                // need upper present
                if (upper_present_by_way[way]) begin

                    // guaranteed valid for way 0 valid
                    if (way == 0) begin
                        valid_SDEQ = 1'b1;
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
                    valid_SDEQ = 1'b1;
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

            // uncompressed and dep pred follow lower:

            uncompressed_by_way_SDEQ[way] = |(uncompressed_vec & lower_ack_one_hot_by_way[way]);
            // dep_pred_by_way_SDEQ[way] = dep_pred_vec[lower_ack_index_by_way[way]];

            dep_pred_by_way_SDEQ[way] = '0;
            for (int i = 0; i < 16; i++) begin
                if (lower_ack_one_hot_by_way[way][i]) begin
                    dep_pred_by_way_SDEQ[way] |= dep_pred_vec[i];
                end
            end

            // instr and pred info follow lower to chunk 0, upper to chunk 1:
            
            // instr_2B_by_way_by_chunk_SDEQ[way][0] = instr_2B_vec[lower_ack_index_by_way[way]];
            // instr_2B_by_way_by_chunk_SDEQ[way][1] = instr_2B_vec[upper_ack_index_by_way[way]];
            // pred_info_by_way_by_chunk_SDEQ[way][0] = pred_info_vec[lower_ack_index_by_way[way]];
            // pred_info_by_way_by_chunk_SDEQ[way][1] = pred_info_vec[upper_ack_index_by_way[way]];
        
            instr_2B_by_way_by_chunk_SDEQ[way] = '0;
            pred_info_by_way_by_chunk_SDEQ[way] = '0;
            for (int i = 0; i < 16; i++) begin
                if (lower_ack_one_hot_by_way[way][i]) begin
                    instr_2B_by_way_by_chunk_SDEQ[way][0] |= instr_2B_vec[i];
                    pred_info_by_way_by_chunk_SDEQ[way][0] |= pred_info_vec[i];
                end
                if (upper_ack_one_hot_by_way[way][i]) begin
                    instr_2B_by_way_by_chunk_SDEQ[way][1] |= instr_2B_vec[i];
                    pred_info_by_way_by_chunk_SDEQ[way][1] |= pred_info_vec[i];
                end
            end

            // PC follows lower index set
            // msb = 1 means in deq ptr1 set
            if (|lower_ack_one_hot_by_way[way][15:8]) begin
                PC_by_way_SDEQ[way] = {
                    stream_set_array[stream_deq0_ptr.index].after_PC28,
                    lower_ack_index_by_way[way][2:0],
                    1'b0
                };
            // msb = 0 means in deq ptr0 set
            end else begin
                PC_by_way_SDEQ[way] = {
                    deq0_PC28,
                    lower_ack_index_by_way[way][2:0],
                    1'b0
                };
            end

            // LH, GH, ras index follow upper index set if uncompressed, lower index set if compressed
            if (uncompressed_by_way_SDEQ[way]) begin
                // msb = 1 means in deq ptr1 set
                if (|upper_ack_one_hot_by_way[way][15:8]) begin
                    LH_by_way_SDEQ[way] = LH_deq1;
                    GH_by_way_SDEQ[way] = GH_deq1;
                    ras_index_by_way_SDEQ[way] = ras_index_deq1;
                // msb = 0 means in deq ptr0 set
                end else begin
                    LH_by_way_SDEQ[way] = LH_deq0;
                    GH_by_way_SDEQ[way] = GH_deq0;
                    ras_index_by_way_SDEQ[way] = ras_index_deq0;
                end
            end else begin
                // msb = 1 means in deq ptr1 set
                if (|lower_ack_one_hot_by_way[way][15:8]) begin
                    LH_by_way_SDEQ[way] = LH_deq1;
                    GH_by_way_SDEQ[way] = GH_deq1;
                    ras_index_by_way_SDEQ[way] = ras_index_deq1;
                // msb = 0 means in deq ptr0 set
                end else begin
                    LH_by_way_SDEQ[way] = LH_deq0;
                    GH_by_way_SDEQ[way] = GH_deq0;
                    ras_index_by_way_SDEQ[way] = ras_index_deq0;
                end
            end
        end
    end

    assign stream_empty0 = ~set_valid_array[0];
    assign stream_empty1 = ~set_valid_array[1];

    // assign deq0_done = ~stream_empty0 & &(~valid_vec[7:0] | ack_vec[7:0]);
    // assign deq1_done = ~stream_empty1 & &(~valid_vec[15:8] | ack_vec[15:8]);

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

    pq_lsb #(
        .WIDTH(ISTREAM_SETS),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_VALID_PQ (
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

            deq0_PC28 <= INIT_PC[31:4];

            set_valid_array <= '0;
            valid_set_vec_array <= '0;
            uncompressed_set_vec_array <= '0;
        end
        else if (restart) begin
            stream_set_array <= '0;

            stream_enq_ptr <= '0;
            stream_deq0_ptr <= 0;
            stream_deq1_ptr <= 1;

            deq0_PC28 <= restart_PC[31:4];

            set_valid_array <= '0;
            valid_set_vec_array <= '0;
            uncompressed_set_vec_array <= '0;
        end
        else begin
            stream_set_array <= next_stream_set_array;

            stream_enq_ptr <= next_stream_enq_ptr;
            stream_deq0_ptr <= next_stream_deq0_ptr;
            stream_deq1_ptr <= next_stream_deq1_ptr;

            deq0_PC28 <= next_deq0_PC28;

            // check double deQ
            if (~stall_SDEQ & deq0_done & deq1_done) begin

                for (int i = 0; i < ISTREAM_SETS-2; i++) begin
                    valid_set_vec_array[i] <= next_valid_set_vec_array[i+2];
                    uncompressed_set_vec_array[i] <= next_uncompressed_set_vec_array[i+2];
                    set_valid_array[i] <= next_set_valid_array[i+2];
                end

                valid_set_vec_array[ISTREAM_SETS-2] <= 8'h0;
                uncompressed_set_vec_array[ISTREAM_SETS-2] <= 8'h0;
                set_valid_array[ISTREAM_SETS-2] <= 1'b0;

                valid_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                uncompressed_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                set_valid_array[ISTREAM_SETS-1] <= 1'b0;
            end

            // check single deQ
            else if (~stall_SDEQ & deq0_done) begin

                for (int i = 0; i < ISTREAM_SETS-1; i++) begin
                    valid_set_vec_array[i] <= next_valid_set_vec_array[i+1];
                    uncompressed_set_vec_array[i] <= next_uncompressed_set_vec_array[i+1];
                    set_valid_array[i] <= next_set_valid_array[i+1];
                end

                valid_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                uncompressed_set_vec_array[ISTREAM_SETS-1] <= 8'h0;
                set_valid_array[ISTREAM_SETS-1] <= 1'b0;
            end

            // otherwise, just take self
            else begin
                valid_set_vec_array <= next_valid_set_vec_array;
                uncompressed_set_vec_array <= next_uncompressed_set_vec_array;
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

        next_deq0_PC28 = deq0_PC28;

        // restart/flush handled in FF logic
            // act as if no restart/flush with next_* signals

        // enQ logic
        if (valid_SENQ & ~stall_SENQ) begin

            // enQ on stream
            for (int i = 0; i < 8; i++) begin
                next_stream_set_array[stream_enq_ptr.index].chunks[i].instr_2B = instr_2B_by_fetch_2B_SENQ[i];
                next_stream_set_array[stream_enq_ptr.index].chunks[i].pred_info = pred_info_by_fetch_2B_SENQ[i];
                next_stream_set_array[stream_enq_ptr.index].chunks[i].dep_pred = dep_pred_by_fetch_2B_SENQ[i];
            end
            next_stream_set_array[stream_enq_ptr.index].after_PC28 = after_PC_SENQ[31:4];
            next_stream_set_array[stream_enq_ptr.index].LH = LH_SENQ;
            next_stream_set_array[stream_enq_ptr.index].GH = GH_SENQ;
            next_stream_set_array[stream_enq_ptr.index].ras_index = ras_index_SENQ;

            // incr enQ ptr
            next_stream_enq_ptr = stream_enq_ptr + 1;
        end

        // deQ logic
        if (~stall_SDEQ) begin

            // set deq's:

            // deq0 and deq1: incr 2, take deq1 after PC
            if (deq0_done & deq1_done) begin
                next_stream_deq0_ptr = stream_deq0_ptr + 2;
                next_stream_deq1_ptr = stream_deq1_ptr + 2;
                next_deq0_PC28 = stream_set_array[stream_deq1_ptr.index].after_PC28;
            end
            // only deq0: incr 1, take deq0 after PC
            else if (deq0_done) begin
                next_stream_deq0_ptr = stream_deq0_ptr + 1;
                next_stream_deq1_ptr = stream_deq1_ptr + 1;
                next_deq0_PC28 = stream_set_array[stream_deq0_ptr.index].after_PC28;
            end
            // none: no change
            else begin
                next_stream_deq0_ptr = stream_deq0_ptr;
                next_stream_deq1_ptr = stream_deq1_ptr;
                next_deq0_PC28 = deq0_PC28;
            end
        end
    end

    always_comb begin
        next_valid_set_vec_array = valid_set_vec_array;
        next_uncompressed_set_vec_array = uncompressed_set_vec_array;
        next_set_valid_array = set_valid_array;

        if (~stall_SDEQ) begin
            for (int i = 0; i < 8; i++) begin
                if (ack_vec[i]) begin
                    next_valid_set_vec_array[0][i] = 1'b0;
                end
            end
            for (int j = 0; j < 8; j++) begin
                if (ack_vec[j + 8]) begin
                    next_valid_set_vec_array[1][j] = 1'b0;
                end
            end
        end

        for (int i = 0; i < ISTREAM_SETS; i++) begin
            if (set_enq_one_hot[i]) begin
                next_set_valid_array[i] = valid_SENQ & ~stall_SENQ;
                next_valid_set_vec_array[i] = enq_set_valid_vec;
                next_uncompressed_set_vec_array[i] = enq_set_uncompressed_vec;
            end
        end
    end

endmodule
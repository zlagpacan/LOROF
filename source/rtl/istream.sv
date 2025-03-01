/*
    Filename: istream.sv
    Author: zlagpacan
    Description: RTL for Instruction Stream
    Spec: LOROF/spec/design/istream.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module istream (

    // seq
    input logic CLK,
    input logic nRST,

    // SENQ stage
    input logic                                                 valid_SENQ,
    input logic [FETCH_WIDTH_2B-1:0]                            valid_by_fetch_2B_SENQ,
    input logic [FETCH_WIDTH_2B-1:0][15:0]                      instr_2B_by_fetch_2B_SENQ,
    input logic [FETCH_WIDTH_2B-1:0][BTB_PRED_INFO_WIDTH-1:0]   pred_info_by_fetch_2B_SENQ,
    input logic [FETCH_WIDTH_2B-1:0]                            dep_pred_by_fetch_2B_SENQ,
    input logic [31:0]                                          PC_SENQ,
    input logic [LH_LENGTH-1:0]                                 LH_SENQ,
    input logic [GH_LENGTH-1:0]                                 GH_SENQ,
    input logic [RAS_INDEX_WIDTH-1:0]                           ras_index_SENQ,

    // SENQ feedback
    output logic stall_SENQ,

    // SDEQ stage
    output logic [3:0]                              valid_by_way_SDEQ,
    output logic [3:0]                              compressed_by_way_SDEQ,
    output logic [3:0][31:0]                        instr_4B_by_way_SDEQ,
    output logic [3:0][BTB_PRED_INFO_WIDTH-1:0]     pred_info_by_way_SDEQ,
    output logic [3:0]                              dep_pred_by_way_SDEQ,
    output logic [3:0][31:0]                        PC_by_way_SDEQ,
    output logic [3:0][LH_LENGTH-1:0]               LH_by_way_SDEQ,
    output logic [3:0][GH_LENGTH-1:0]               GH_by_way_SDEQ,
    output logic [3:0][RAS_INDEX_WIDTH-1:0]         ras_index_by_way_SDEQ,

    // SDEQ feedback
    input logic stall_SDEQ,

    // control
    input logic flush
);

    // ----------------------------------------------------------------
    // Signals:

    typedef struct packed {
        logic                               valid;
        logic [15:0]                        instr_2B;
        logic [BTB_PRED_INFO_WIDTH-1:0]     pred_info;
        logic                               dep_pred;
    } instr_block_t;

    typedef struct packed {
        logic                           valid;
        instr_block_t                   block;
        logic [31:0]                    after_PC;
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
    stream_ptr_t stream_deq_ptr0, next_stream_deq_ptr0;
    stream_ptr_t stream_deq_ptr1, next_stream_deq_ptr1;

    logic stream_full;

    // ----------------------------------------------------------------
    // Logic: 

    // FF's:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            stream_set_array <= '0;
            stream_enq_ptr <= '0;
            stream_deq_ptr0 <= 0;
            stream_deq_ptr1 <= 1;
        end
        else if (flush) begin
            stream_set_array <= '0;
            stream_enq_ptr <= '0;
            stream_deq_ptr0 <= 0;
            stream_deq_ptr1 <= 1;
        end
        else begin
            stream_set_array <= next_stream_set_array;
            stream_enq_ptr <= next_stream_enq_ptr;
            stream_deq_ptr0 <= next_stream_deq_ptr0;
            stream_deq_ptr1 <= next_stream_deq_ptr1;
        end
    end

    // current ptr FIFO full check
    assign stream_full = 
        stream_enq_ptr.index == stream_deq_ptr0.index 
        & 
        stream_enq_ptr.msb != stream_deq_ptr0.msb
    ;

    always_comb begin
        
        next_stream_set_array = stream_set_array;
        next_stream_enq_ptr = stream_enq_ptr;
        next_stream_deq_ptr0 = stream_deq_ptr0;
        next_stream_deq_ptr1 = stream_deq_ptr1;

        // flush handled in FF logic
            // act as if no flush with next_* signals

        // enQ logic
        if (valid_SENQ & ~stream_full) begin

        end

        // deQ logic
        if (~stall_SDEQ) begin

        end
    end

endmodule
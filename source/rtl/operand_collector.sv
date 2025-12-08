/*
    Filename: operand_collector.sv
    Author: zlagpacan
    Description: RTL for Operand Collector
    Spec: LOROF/spec/design/operand_collector.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module operand_collector #(
    parameter OC_ENTRIES = 3,
    parameter LOG_OC_ENTRIES = $clog2(OC_ENTRIES),
    parameter FAST_FORWARD_PIPE_COUNT = 4,
    parameter LOG_FAST_FORWARD_PIPE_COUNT = $clog2(FAST_FORWARD_PIPE_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // issue info
    input logic                                     enq_valid,
    input logic                                     enq_is_reg,
    input logic                                     enq_is_bus_forward,
    input logic                                     enq_is_fast_forward,
    input logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]   enq_fast_forward_pipe,
    input logic [LOG_PRF_BANK_COUNT-1:0]            enq_bank,

    // reg read data from PRF
    input logic         reg_read_resp_valid,
    input logic [31:0]  reg_read_resp_data,

    // bus forward data from PRF
    input logic [PRF_BANK_COUNT-1:0][31:0] bus_forward_data_by_bank,

    // fast forward data
    input logic [FAST_FORWARD_PIPE_COUNT-1:0]           fast_forward_data_valid_by_pipe,
    input logic [FAST_FORWARD_PIPE_COUNT-1:0][31:0]     fast_forward_data_by_pipe,

    // operand collection control
    output logic            operand_collected,
    input logic             operand_collected_ack,
    output logic [31:0]     operand_data,
    input logic             operand_data_ack
);

    // ----------------------------------------------------------------
    // Signals:

    // memory array
    typedef struct packed {
        logic                                       valid;
        logic                                       acked;
        logic                                       need_reg;
        logic                                       need_bus_forward;
        logic                                       need_fast_forward;
        logic [LOG_FAST_FORWARD_PIPE_COUNT-1:0]     fast_forward_pipe;
        logic [PRF_BANK_COUNT-1:0]                  bank;
        logic [31:0]                                data;
    } OC_entry_t;
    OC_entry_t [OC_ENTRIES-1:0] OC_array;

    logic [LOG_OC_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_OC_ENTRIES-1:0] notif_deq_ptr, notif_deq_ptr_plus_1;
    logic [LOG_OC_ENTRIES-1:0] data_deq_ptr, data_deq_ptr_plus_1;
    logic [OC_ENTRIES-1:0] wraparound_mask, next_wraparound_mask;

    logic [OC_ENTRIES-1:0] unmasked_need_reg_by_entry;
    logic [OC_ENTRIES-1:0] selected_unmasked_need_reg_one_hot;
    logic [OC_ENTRIES-1:0] masked_need_reg_by_entry;
    logic [OC_ENTRIES-1:0] selected_masked_need_reg_one_hot;

    logic [OC_ENTRIES-1:0] reg_collecting_by_entry;

    // ----------------------------------------------------------------
    // Logic:

    // outputs:
    always_comb begin
        operand_collected =
            OC_array[notif_deq_ptr].valid
            & (~OC_array[notif_deq_ptr].need_reg | reg_read_resp_valid)
            // bus forward guaranteed to be handled
            & (~OC_array[notif_deq_ptr].need_fast_forward | fast_forward_data_valid_by_pipe[OC_array[notif_deq_ptr].fast_forward_pipe]);

        operand_data = OC_array[data_deq_ptr].data;
    end

    // need_reg arbitration:
        // collect reg read for only the oldest need_reg
    always_comb begin
        for (int entry = 0; entry < OC_ENTRIES; entry++) begin
            unmasked_need_reg_by_entry[entry] = OC_array[entry].need_reg;
            masked_need_reg_by_entry[entry] = OC_array[entry].need_reg & wraparound_mask[entry]; 
        end
    end

    pe_lsb #(
        .WIDTH(OC_ENTRIES),
        .USE_ONE_HOT(1)
    ) UNMASKED_NEED_REG_PE_LSB (
        .req_vec(unmasked_need_reg_by_entry),
        .ack_one_hot(selected_unmasked_need_reg_one_hot)
    );
    pe_lsb #(
        .WIDTH(OC_ENTRIES),
        .USE_ONE_HOT(1)
    ) MASKED_NEED_REG_PE_LSB (
        .req_vec(masked_need_reg_by_entry),
        .ack_one_hot(selected_masked_need_reg_one_hot)
    );
    
    always_comb begin
        // prioritize mask over unmasked
            // also should be all 0's if no need_reg
        if (|masked_need_reg_by_entry) begin
            reg_collecting_by_entry = selected_masked_need_reg_one_hot;
        end
        else begin
            reg_collecting_by_entry = selected_unmasked_need_reg_one_hot;
        end
    end

    // memory array logic:
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            OC_array <= '0;
        end
        else begin
            // update operand data for all entries
            for (int entry = 0; entry < OC_ENTRIES; entry++) begin
                // reg read's come in in-order -> signal with reg_collecting_by_entry
                if (reg_collecting_by_entry[entry] & reg_read_resp_valid) begin
                    OC_array[entry].need_reg <= 1'b0;
                    OC_array[entry].data <= reg_read_resp_data;
                end
                // bus forwards technically can only come the cycle after enQ but this way is fine
                if (OC_array[entry].need_bus_forward) begin
                    OC_array[entry].need_bus_forward <= 1'b0;
                    OC_array[entry].data <= bus_forward_data_by_bank[OC_array[entry].bank];
                end
                // fast forwards can come at any time into any entry
                if (OC_array[entry].need_fast_forward & fast_forward_data_valid_by_pipe[OC_array[entry].fast_forward_pipe]) begin
                    OC_array[entry].need_fast_forward <= 1'b0;
                    OC_array[entry].data <= fast_forward_data_by_pipe[OC_array[entry].fast_forward_pipe];
                end
            end

            // notif deQ
                // assume external will deQ only if entry valid 
            if (operand_collected_ack) begin
                OC_array[notif_deq_ptr].acked <= 1'b1;
                    // optional, only for debug
            end

            // data deQ
                // assume external will deQ only if entry valid
            if (operand_data_ack) begin
                OC_array[data_deq_ptr].valid <= 1'b0; 
            end

            // enQ
                // assume enQ never overrides entry
            if (enq_valid) begin
                OC_array[enq_ptr].valid <= 1'b1;
                OC_array[enq_ptr].acked <= 1'b0;
                OC_array[enq_ptr].need_reg <= enq_is_reg;
                OC_array[enq_ptr].need_bus_forward <= enq_is_bus_forward;
                OC_array[enq_ptr].need_fast_forward <= enq_is_fast_forward;
                OC_array[enq_ptr].fast_forward_pipe <= enq_fast_forward_pipe;
                OC_array[enq_ptr].bank <= enq_bank;
                OC_array[enq_ptr].data <= 32'h0; 
                    // clear data for is_zero case
            end
        end
    end

    // pointers and masks:
    generate
        // power-of-2 # entries can use simple +1 for ptr's
        if (OC_ENTRIES & (OC_ENTRIES - 1) == 0) begin
            assign enq_ptr_plus_1 = enq_ptr + 1;
            assign notif_deq_ptr_plus_1 = notif_deq_ptr + 1;
            assign data_deq_ptr_plus_1 = data_deq_ptr + 1;
        end

        // otherwise, manual wraparound for ptr's
        else begin
            always_comb begin
                if (enq_ptr == OC_ENTRIES - 1) begin
                    enq_ptr_plus_1 = 0;
                end
                else begin
                    enq_ptr_plus_1 = enq_ptr + 1;
                end
                if (notif_deq_ptr == OC_ENTRIES - 1) begin
                    notif_deq_ptr_plus_1 = 0;
                end
                else begin
                    notif_deq_ptr_plus_1 = notif_deq_ptr + 1;
                end
                if (data_deq_ptr == OC_ENTRIES - 1) begin
                    data_deq_ptr_plus_1 = 0;
                end
                else begin
                    data_deq_ptr_plus_1 = data_deq_ptr + 1;
                end
            end
        end
    endgenerate
    
    always_comb begin
        // reset mask if looks like 1000...
        if (~wraparound_mask[LOG_OC_ENTRIES-2]) begin
            next_wraparound_mask = '1;
        end
        // otherwise left shift mask by 1
        else begin
            next_wraparound_mask = {wraparound_mask[LOG_OC_ENTRIES-2:0], 1'b0};
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            enq_ptr <= 0;
            notif_deq_ptr <= 0;
            data_deq_ptr <= 0;
            wraparound_mask <= '1;
        end
        else begin
            // enQ
            if (enq_valid) begin
                enq_ptr <= enq_ptr_plus_1;
            end
            // notif deQ
            if (operand_collected_ack) begin
                notif_deq_ptr <= notif_deq_ptr_plus_1;
                wraparound_mask <= next_wraparound_mask;
            end
            // data deQ
            if (operand_data_ack) begin
                data_deq_ptr <= data_deq_ptr_plus_1;
            end
        end
    end

endmodule
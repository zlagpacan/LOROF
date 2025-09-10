/*
    Filename: free_list.sv
    Author: zlagpacan
    Description: RTL for Physical Register Free List
    Spec: LOROF/spec/design/free_list.md
*/

`include "core_types_pkg.vh"
import core_types_pkg::*;

module free_list #(
    parameter FREE_LIST_BANK_COUNT = PRF_BANK_COUNT,
    parameter LOG_FREE_LIST_BANK_COUNT = $clog2(FREE_LIST_BANK_COUNT),
    parameter FREE_LIST_LENGTH_PER_BANK = PR_COUNT / FREE_LIST_BANK_COUNT,
    parameter LOG_FREE_LIST_LENGTH_PER_BANK = $clog2(FREE_LIST_LENGTH_PER_BANK),

    parameter FREE_LIST_SHIFT_REG_ENTRIES = 12,

    parameter FREE_LIST_LOWER_THRESHOLD = 8,
    parameter FREE_LIST_UPPER_THRESHOLD = 24
) (
    // seq
    input logic CLK,
    input logic nRST,

    // enqueue request
    input logic [FREE_LIST_BANK_COUNT-1:0]                      enq_req_valid_by_bank,
    input logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0]    enq_req_PR_by_bank,

    // enqueue feedback
    output logic [FREE_LIST_BANK_COUNT-1:0]                     enq_resp_ack_by_bank,

    // dequeue request
    input logic [FREE_LIST_BANK_COUNT-1:0]                      deq_req_valid_by_bank,
    output logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0]   deq_req_PR_by_bank,

    // dequeue feedback
    output logic [FREE_LIST_BANK_COUNT-1:0]                     deq_resp_ready_by_bank
);

    // ----------------------------------------------------------------
    // Signals:

    // array
    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_LENGTH_PER_BANK-1:0][LOG_PR_COUNT-1:0]
        free_list_by_bank;

    typedef struct packed {
        logic                                       msb;
        logic [LOG_FREE_LIST_LENGTH_PER_BANK-1:0]   index;
    } free_list_ptr_t;

    free_list_ptr_t [FREE_LIST_BANK_COUNT-1:0]  enq_ptr_by_bank, next_enq_ptr_by_bank;
    free_list_ptr_t [FREE_LIST_BANK_COUNT-1:0]  deq_ptr_by_bank, next_deq_ptr_by_bank;

    free_list_ptr_t [FREE_LIST_BANK_COUNT-1:0]  worst_case_next_enq_ptr_by_bank;

    logic [FREE_LIST_BANK_COUNT-1:0]                    array_enq_valid_by_bank;
    logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0]  array_enq_PR_by_bank;

    logic [FREE_LIST_BANK_COUNT-1:0]                    array_deq_valid_by_bank;
    logic [FREE_LIST_BANK_COUNT-1:0][LOG_PR_COUNT-1:0]  array_deq_PR_by_bank;

    logic [FREE_LIST_BANK_COUNT-1:0]    empty_by_bank;
    logic [FREE_LIST_BANK_COUNT-1:0]    full_by_bank;

    // swizzle enQ
    logic [FREE_LIST_BANK_COUNT-1:0]    lower_threshold_bank_mask;
    logic [FREE_LIST_BANK_COUNT-1:0]    not_upper_threshold_bank_mask;
    logic [FREE_LIST_BANK_COUNT-1:0]    not_full_bank_mask;

    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_BANK_COUNT-1:0]  enq_lower_threshold_bank_req_vec_by_bank;
    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_BANK_COUNT-1:0]  enq_lower_threshold_bank_ack_one_hot_by_bank;

    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_BANK_COUNT-1:0]  enq_not_upper_threshold_bank_req_vec_by_bank;
    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_BANK_COUNT-1:0]  enq_not_upper_threshold_bank_ack_one_hot_by_bank;

    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_BANK_COUNT-1:0]  enq_not_full_bank_req_vec_by_bank;
    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_BANK_COUNT-1:0]  enq_not_full_bank_ack_one_hot_by_bank;

    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_BANK_COUNT-1:0]  enq_bank_ack_one_hot_by_bank;

    // shift reg
    logic [FREE_LIST_SHIFT_REG_ENTRIES-1:0]                     shift_reg_valid_by_entry;
    logic [FREE_LIST_SHIFT_REG_ENTRIES-1:0][LOG_PR_COUNT-1:0]   shift_reg_PR_by_entry;

    // swizzle deQ
    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_SHIFT_REG_ENTRIES-1:0]   shift_reg_open_mask_by_bank;
    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_SHIFT_REG_ENTRIES-1:0]   shift_reg_pe_one_hot_by_bank;
    logic [FREE_LIST_BANK_COUNT-1:0][FREE_LIST_SHIFT_REG_ENTRIES-1:0]   shift_reg_one_hot_by_bank;

    logic deq_to_shift_reg_condition;

    logic [FREE_LIST_SHIFT_REG_ENTRIES-1:0]                     new_shift_reg_valid_by_entry;
    logic [FREE_LIST_SHIFT_REG_ENTRIES-1:0][LOG_PR_COUNT-1:0]   new_shift_reg_PR_by_entry;

    logic [FREE_LIST_BANK_COUNT-1:0] shift_reg_deq_by_bank;

    logic upper_take_1_above;
    logic upper_take_2_above;
    logic upper_take_3_above;
    logic upper_take_4_above;

    // ----------------------------------------------------------------
    // swizzle enQ Logic:

    // register upper threshold and lower threshold based on previous cycle (not big deal if slightly off)
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            not_upper_threshold_bank_mask <= '1;
            lower_threshold_bank_mask <= '0;
        end
        else begin
            for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin

                // upper threshold
                if (deq_ptr_by_bank[bank].index - enq_ptr_by_bank[bank].index > FREE_LIST_UPPER_THRESHOLD) begin
                    not_upper_threshold_bank_mask[bank] <= 1'b0;
                end else begin
                    not_upper_threshold_bank_mask[bank] <= 1'b1;
                end

                // lower threshold
                if (deq_ptr_by_bank[bank].index - enq_ptr_by_bank[bank].index < FREE_LIST_LOWER_THRESHOLD) begin
                    lower_threshold_bank_mask[bank] <= 1'b1;
                end else begin
                    lower_threshold_bank_mask[bank] <= 1'b0;
                end
            end
        end
    end

    // take current not full's
        // full's calculated last cycle with next pointer's so this up to date
    assign not_full_bank_mask = ~full_by_bank;

    /////////////////////////
    // enQ Request Bank 0: //
    /////////////////////////
    assign enq_lower_threshold_bank_req_vec_by_bank[0] = lower_threshold_bank_mask;
    assign enq_not_upper_threshold_bank_req_vec_by_bank[0] = not_upper_threshold_bank_mask;
    assign enq_not_full_bank_req_vec_by_bank[0] = not_full_bank_mask;
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK0_LOWER_THRESHOLD_PE (
        .req_vec(enq_lower_threshold_bank_req_vec_by_bank[0]),
        .ack_one_hot(enq_lower_threshold_bank_ack_one_hot_by_bank[0])
    );
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK0_UPPER_THRESHOLD_PE (
        .req_vec(enq_not_upper_threshold_bank_req_vec_by_bank[0]),
        .ack_one_hot(enq_not_upper_threshold_bank_ack_one_hot_by_bank[0])
    );
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK0_NOT_FULL_PE (
        .req_vec(enq_not_full_bank_req_vec_by_bank[0]),
        .ack_one_hot(enq_not_full_bank_ack_one_hot_by_bank[0])
    );

    /////////////////////////
    // enQ Request Bank 1: //
    /////////////////////////
    assign enq_lower_threshold_bank_req_vec_by_bank[1] = enq_lower_threshold_bank_req_vec_by_bank[0] & ~enq_bank_ack_one_hot_by_bank[0];
    assign enq_not_upper_threshold_bank_req_vec_by_bank[1] = enq_not_upper_threshold_bank_req_vec_by_bank[0] & ~enq_bank_ack_one_hot_by_bank[0];
    assign enq_not_full_bank_req_vec_by_bank[1] = enq_not_full_bank_req_vec_by_bank[0] & ~enq_bank_ack_one_hot_by_bank[0];
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK1_LOWER_THRESHOLD_PE (
        .req_vec(enq_lower_threshold_bank_req_vec_by_bank[1]),
        .ack_one_hot(enq_lower_threshold_bank_ack_one_hot_by_bank[1])
    );
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK1_UPPER_THRESHOLD_PE (
        .req_vec(enq_not_upper_threshold_bank_req_vec_by_bank[1]),
        .ack_one_hot(enq_not_upper_threshold_bank_ack_one_hot_by_bank[1])
    );
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK1_NOT_FULL_PE (
        .req_vec(enq_not_full_bank_req_vec_by_bank[1]),
        .ack_one_hot(enq_not_full_bank_ack_one_hot_by_bank[1])
    );

    /////////////////////////
    // enQ Request Bank 2: //
    /////////////////////////
    assign enq_lower_threshold_bank_req_vec_by_bank[2] = enq_lower_threshold_bank_req_vec_by_bank[1] & ~enq_bank_ack_one_hot_by_bank[1];
    assign enq_not_upper_threshold_bank_req_vec_by_bank[2] = enq_not_upper_threshold_bank_req_vec_by_bank[1] & ~enq_bank_ack_one_hot_by_bank[1];
    assign enq_not_full_bank_req_vec_by_bank[2] = enq_not_full_bank_req_vec_by_bank[1] & ~enq_bank_ack_one_hot_by_bank[1];
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK2_LOWER_THRESHOLD_PE (
        .req_vec(enq_lower_threshold_bank_req_vec_by_bank[2]),
        .ack_one_hot(enq_lower_threshold_bank_ack_one_hot_by_bank[2])
    );
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK2_UPPER_THRESHOLD_PE (
        .req_vec(enq_not_upper_threshold_bank_req_vec_by_bank[2]),
        .ack_one_hot(enq_not_upper_threshold_bank_ack_one_hot_by_bank[2])
    );
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK2_NOT_FULL_PE (
        .req_vec(enq_not_full_bank_req_vec_by_bank[2]),
        .ack_one_hot(enq_not_full_bank_ack_one_hot_by_bank[2])
    );

    /////////////////////////
    // enQ Request Bank 3: //
    /////////////////////////
    assign enq_lower_threshold_bank_req_vec_by_bank[3] = enq_lower_threshold_bank_req_vec_by_bank[2] & ~enq_bank_ack_one_hot_by_bank[2];
    assign enq_not_upper_threshold_bank_req_vec_by_bank[3] = enq_not_upper_threshold_bank_req_vec_by_bank[2] & ~enq_bank_ack_one_hot_by_bank[2];
    assign enq_not_full_bank_req_vec_by_bank[3] = enq_not_full_bank_req_vec_by_bank[2] & ~enq_bank_ack_one_hot_by_bank[2];
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK3_LOWER_THRESHOLD_PE (
        .req_vec(enq_lower_threshold_bank_req_vec_by_bank[3]),
        .ack_one_hot(enq_lower_threshold_bank_ack_one_hot_by_bank[3])
    );
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK3_UPPER_THRESHOLD_PE (
        .req_vec(enq_not_upper_threshold_bank_req_vec_by_bank[3]),
        .ack_one_hot(enq_not_upper_threshold_bank_ack_one_hot_by_bank[3])
    );
    pe_lsb #(
        .WIDTH(FREE_LIST_BANK_COUNT),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) ENQ_BANK3_NOT_FULL_PE (
        .req_vec(enq_not_full_bank_req_vec_by_bank[3]),
        .ack_one_hot(enq_not_full_bank_ack_one_hot_by_bank[3])
    );

    // final array enQ
    always_comb begin
        for (int req_bank = 0; req_bank < FREE_LIST_BANK_COUNT; req_bank++) begin

            if (enq_req_valid_by_bank[req_bank]) begin
                if (|enq_lower_threshold_bank_req_vec_by_bank[req_bank]) begin
                    enq_bank_ack_one_hot_by_bank[req_bank] = enq_lower_threshold_bank_ack_one_hot_by_bank[req_bank];
                // end else if (|enq_not_upper_threshold_bank_req_vec_by_bank[req_bank]) begin
                //     enq_bank_ack_one_hot_by_bank[req_bank] = enq_not_upper_threshold_bank_ack_one_hot_by_bank[req_bank];
                end else begin
                    enq_bank_ack_one_hot_by_bank[req_bank] = enq_not_full_bank_ack_one_hot_by_bank[req_bank];
                end
            end else begin
                enq_bank_ack_one_hot_by_bank[req_bank] = '0;
            end

            array_enq_valid_by_bank[req_bank] = |enq_bank_ack_one_hot_by_bank[req_bank];
            enq_resp_ack_by_bank[req_bank] = array_enq_valid_by_bank[req_bank];
            
            array_enq_PR_by_bank[req_bank] = '0;
            for (int resp_bank = 0; resp_bank < FREE_LIST_BANK_COUNT; resp_bank++) begin
                if (enq_bank_ack_one_hot_by_bank[req_bank][resp_bank]) begin
                    array_enq_PR_by_bank[req_bank] |= enq_req_PR_by_bank[resp_bank];
                end
            end
        end
    end

    // ----------------------------------------------------------------
    // deQ Logic:

    // give PR's following deq ptr
    always_comb begin
        for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin
            array_deq_PR_by_bank[bank] = free_list_by_bank[bank][deq_ptr_by_bank[bank].index];
        end
    end

    // deQ to shift reg:

    // deq to shift reg when can fit all banks into deq
    assign deq_to_shift_reg_condition = ~shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-FREE_LIST_BANK_COUNT];

    // way 0
    assign shift_reg_open_mask_by_bank[0] = ~shift_reg_valid_by_entry;
    pe_lsb #(
        .WIDTH(FREE_LIST_SHIFT_REG_ENTRIES),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) DEQ_TO_SHIFT_REG_PE_WAY0 (
        .req_vec(shift_reg_open_mask_by_bank[0]),
        .ack_one_hot(shift_reg_pe_one_hot_by_bank[0])
    );
    assign shift_reg_one_hot_by_bank[0] = 
        shift_reg_pe_one_hot_by_bank[0] 
        & 
        {FREE_LIST_SHIFT_REG_ENTRIES{~empty_by_bank[0] & deq_to_shift_reg_condition}}
    ;

    // way 1
    assign shift_reg_open_mask_by_bank[1] = shift_reg_open_mask_by_bank[0] & ~shift_reg_one_hot_by_bank[0];
    pe_lsb #(
        .WIDTH(FREE_LIST_SHIFT_REG_ENTRIES),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) DEQ_TO_SHIFT_REG_PE_WAY1 (
        .req_vec(shift_reg_open_mask_by_bank[1]),
        .ack_one_hot(shift_reg_pe_one_hot_by_bank[1])
    );
    assign shift_reg_one_hot_by_bank[1] = 
        shift_reg_pe_one_hot_by_bank[1] 
        & 
        {FREE_LIST_SHIFT_REG_ENTRIES{~empty_by_bank[1] & deq_to_shift_reg_condition}}
    ;

    // way 2
    assign shift_reg_open_mask_by_bank[2] = shift_reg_open_mask_by_bank[1] & ~shift_reg_one_hot_by_bank[1];
    pe_lsb #(
        .WIDTH(FREE_LIST_SHIFT_REG_ENTRIES),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) DEQ_TO_SHIFT_REG_PE_WAY2 (
        .req_vec(shift_reg_open_mask_by_bank[2]),
        .ack_one_hot(shift_reg_pe_one_hot_by_bank[2])
    );
    assign shift_reg_one_hot_by_bank[2] = 
        shift_reg_pe_one_hot_by_bank[2] 
        & 
        {FREE_LIST_SHIFT_REG_ENTRIES{~empty_by_bank[2] & deq_to_shift_reg_condition}}
    ;

    // way 3
    assign shift_reg_open_mask_by_bank[3] = shift_reg_open_mask_by_bank[2] & ~shift_reg_one_hot_by_bank[2];
    pe_lsb #(
        .WIDTH(FREE_LIST_SHIFT_REG_ENTRIES),
        .USE_ONE_HOT(1),
        .USE_COLD(0),
        .USE_INDEX(0)
    ) DEQ_TO_SHIFT_REG_PE_WAY3 (
        .req_vec(shift_reg_open_mask_by_bank[3]),
        .ack_one_hot(shift_reg_pe_one_hot_by_bank[3])
    );
    assign shift_reg_one_hot_by_bank[3] = 
        shift_reg_pe_one_hot_by_bank[3] 
        & 
        {FREE_LIST_SHIFT_REG_ENTRIES{~empty_by_bank[3] & deq_to_shift_reg_condition}}
    ;

    // perform array deq's
    always_comb begin
        for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin
            array_deq_valid_by_bank[bank] = ~empty_by_bank[bank] & deq_to_shift_reg_condition;
        end
    end

    // route deq's to shift reg entries
    always_comb begin

        new_shift_reg_valid_by_entry = '0;
        new_shift_reg_PR_by_entry = '0;

        for (int entry = 0; entry < FREE_LIST_SHIFT_REG_ENTRIES; entry++) begin

            for (int bank = 0; bank < 4; bank++) begin
                
                if (shift_reg_one_hot_by_bank[bank][entry]) begin
                    new_shift_reg_valid_by_entry[entry] = 1'b1;
                    new_shift_reg_PR_by_entry[entry] |= array_deq_PR_by_bank[bank];
                end
            end
        end
    end

    // stall follows lowest 4 empty entries
    assign deq_resp_ready_by_bank = shift_reg_valid_by_entry[FREE_LIST_BANK_COUNT-1:0];

    // deq from shift reg
    assign shift_reg_deq_by_bank = deq_req_valid_by_bank & deq_resp_ready_by_bank;

    // PR follows lowest 4 empty entries
    assign deq_req_PR_by_bank = shift_reg_PR_by_entry[FREE_LIST_BANK_COUNT-1:0];

    assign upper_take_1_above = |shift_reg_deq_by_bank;
    assign upper_take_2_above = 
        shift_reg_deq_by_bank[0] & shift_reg_deq_by_bank[1]
        |
        shift_reg_deq_by_bank[0] & shift_reg_deq_by_bank[2]
        |
        shift_reg_deq_by_bank[0] & shift_reg_deq_by_bank[3]
        |
        shift_reg_deq_by_bank[1] & shift_reg_deq_by_bank[2]
        |
        shift_reg_deq_by_bank[1] & shift_reg_deq_by_bank[3]
        |
        shift_reg_deq_by_bank[2] & shift_reg_deq_by_bank[3]
    ;
    assign upper_take_3_above =
        shift_reg_deq_by_bank[0] & shift_reg_deq_by_bank[1] & shift_reg_deq_by_bank[2]
        |
        shift_reg_deq_by_bank[0] & shift_reg_deq_by_bank[1] & shift_reg_deq_by_bank[3]
        |
        shift_reg_deq_by_bank[0] & shift_reg_deq_by_bank[2] & shift_reg_deq_by_bank[3]
        |
        shift_reg_deq_by_bank[1] & shift_reg_deq_by_bank[2] & shift_reg_deq_by_bank[3]
    ;
    assign upper_take_4_above = &shift_reg_deq_by_bank;

    // shift reg logic
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            // reset with lowest 12 PR's above 32 AR's
            for (int entry = 0; entry < FREE_LIST_SHIFT_REG_ENTRIES; entry++) begin
                shift_reg_valid_by_entry[entry] <= 1'b1;
                shift_reg_PR_by_entry[entry] <= 32 + entry[LOG_PR_COUNT-1:0];
            end
        end
        else begin

            // --------------------------------------------------------
            // highest entry only takes self:
                // FREE_LIST_SHIFT_REG_ENTRIES-1

            // check take any of above
                // take 1 above covers this
            if (upper_take_1_above) begin
                shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1] <= 1'b0;
            end
            // otherwise take self
            else begin
                // take self valid entry
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                end 
                // take self new entry
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                end
            end

            // --------------------------------------------------------
            // second-highest entry takes self or above:
                // above: [FREE_LIST_SHIFT_REG_ENTRIES-1]
                // self: [FREE_LIST_SHIFT_REG_ENTRIES-2]
            
            // check take 2 or more above
                // take 2 above covers this
            if (upper_take_2_above) begin
                shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= 1'b0;
            end
            // check take above
            else if (upper_take_1_above) begin
                // take valid entry above
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                end 
                // take new entry above
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                end
            end
            // otherwise take self
            else begin
                // take self valid entry
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                end 
                // take self new entry
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                end
            end

            // --------------------------------------------------------
            // third-highest entry takes self or above or 2 above:
                // 2 above: [FREE_LIST_SHIFT_REG_ENTRIES-1]
                // above: [FREE_LIST_SHIFT_REG_ENTRIES-2]
                // self: [FREE_LIST_SHIFT_REG_ENTRIES-3]
            
            // check take 3 or more above
                // take 3 above covers this
            if (upper_take_3_above) begin
                shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= 1'b0;
            end
            // check take 2 above
            else if (upper_take_2_above) begin
                // take valid entry 2 above
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                end 
                // take new entry 2 above
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                end
            end
            // check take above
            else if (upper_take_1_above) begin
                // take valid entry above
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                end 
                // take new entry above
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                end
            end
            // otherwise take self
            else begin
                // take self valid entry
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3];
                end 
                // take self new entry
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3];
                end
            end

            // --------------------------------------------------------
            // fourth-highest entry takes self or above or 2 above or 3 above:
                // 3 above: [FREE_LIST_SHIFT_REG_ENTRIES-1]
                // 2 above: [FREE_LIST_SHIFT_REG_ENTRIES-2]
                // above: [FREE_LIST_SHIFT_REG_ENTRIES-3]
                // self: [FREE_LIST_SHIFT_REG_ENTRIES-4]
            
            // check take 4 above
            if (upper_take_4_above) begin
                shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= 1'b0;
            end
            // check take 3 above
            else if (upper_take_3_above) begin
                // take valid entry 3 above
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                end 
                // take new entry 3 above
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-1];
                end
            end
            // check take 2 above
            else if (upper_take_2_above) begin
                // take valid entry 2 above
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                end 
                // take new entry 2 above
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-2];
                end
            end
            // check take above
            else if (upper_take_1_above) begin
                // take valid entry above
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3];
                end 
                // take new entry above
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-3];
                end
            end
            // otherwise take self
            else begin
                // take self valid entry
                if (shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4]) begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4];
                end 
                // take self new entry
                else begin
                    shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= new_shift_reg_valid_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4];
                    shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4] <= new_shift_reg_PR_by_entry[FREE_LIST_SHIFT_REG_ENTRIES-4];
                end
            end

            // --------------------------------------------------------
            // entries between bottom 4 and top 4 can take self, above, 2 above, or 3 above

            for (int entry = 4; entry < FREE_LIST_SHIFT_REG_ENTRIES - 4; entry++) begin

                // check take 4 above
                if (upper_take_4_above) begin
                    // take valid entry 4 above
                    if (shift_reg_valid_by_entry[entry+4]) begin
                        shift_reg_valid_by_entry[entry] <= shift_reg_valid_by_entry[entry+4];
                        shift_reg_PR_by_entry[entry] <= shift_reg_PR_by_entry[entry+4];
                    end 
                    // take new entry 4 above
                    else begin
                        shift_reg_valid_by_entry[entry] <= new_shift_reg_valid_by_entry[entry+4];
                        shift_reg_PR_by_entry[entry] <= new_shift_reg_PR_by_entry[entry+4];
                    end
                end
                // check take 3 above
                else if (upper_take_3_above) begin
                    // take valid entry 3 above
                    if (shift_reg_valid_by_entry[entry+3]) begin
                        shift_reg_valid_by_entry[entry] <= shift_reg_valid_by_entry[entry+3];
                        shift_reg_PR_by_entry[entry] <= shift_reg_PR_by_entry[entry+3];
                    end 
                    // take new entry 3 above
                    else begin
                        shift_reg_valid_by_entry[entry] <= new_shift_reg_valid_by_entry[entry+3];
                        shift_reg_PR_by_entry[entry] <= new_shift_reg_PR_by_entry[entry+3];
                    end
                end
                // check take 2 above
                else if (upper_take_2_above) begin
                    // take valid entry 2 above
                    if (shift_reg_valid_by_entry[entry+2]) begin
                        shift_reg_valid_by_entry[entry] <= shift_reg_valid_by_entry[entry+2];
                        shift_reg_PR_by_entry[entry] <= shift_reg_PR_by_entry[entry+2];
                    end 
                    // take new entry 2 above
                    else begin
                        shift_reg_valid_by_entry[entry] <= new_shift_reg_valid_by_entry[entry+2];
                        shift_reg_PR_by_entry[entry] <= new_shift_reg_PR_by_entry[entry+2];
                    end
                end
                // check take 1 above
                else if (upper_take_1_above) begin
                    // take valid entry 1 above
                    if (shift_reg_valid_by_entry[entry+1]) begin
                        shift_reg_valid_by_entry[entry] <= shift_reg_valid_by_entry[entry+1];
                        shift_reg_PR_by_entry[entry] <= shift_reg_PR_by_entry[entry+1];
                    end 
                    // take new entry 1 above
                    else begin
                        shift_reg_valid_by_entry[entry] <= new_shift_reg_valid_by_entry[entry+1];
                        shift_reg_PR_by_entry[entry] <= new_shift_reg_PR_by_entry[entry+1];
                    end
                end
                // check take self
                else begin
                    // take self valid entry
                    if (shift_reg_valid_by_entry[entry]) begin
                        shift_reg_valid_by_entry[entry] <= shift_reg_valid_by_entry[entry];
                        shift_reg_PR_by_entry[entry] <= shift_reg_PR_by_entry[entry];
                    end 
                    // take self new entry
                    else begin
                        shift_reg_valid_by_entry[entry] <= new_shift_reg_valid_by_entry[entry];
                        shift_reg_PR_by_entry[entry] <= new_shift_reg_PR_by_entry[entry];
                    end
                end
            end

            // --------------------------------------------------------
            // entry 0:
                // custom

            // check take entry 4
                // all 4 deq
            if (
                upper_take_4_above
            ) begin
                // take valid entry 4
                if (shift_reg_valid_by_entry[4]) begin
                    shift_reg_valid_by_entry[0] <= shift_reg_valid_by_entry[4];
                    shift_reg_PR_by_entry[0] <= shift_reg_PR_by_entry[4];
                end 
                // take new entry 4
                else begin
                    shift_reg_valid_by_entry[0] <= new_shift_reg_valid_by_entry[4];
                    shift_reg_PR_by_entry[0] <= new_shift_reg_PR_by_entry[4];
                end
            end
            // check take entry 3
                // deq lower 3
            else if (
                &shift_reg_deq_by_bank[2:0]
            ) begin
                // take valid entry 3
                if (shift_reg_valid_by_entry[3]) begin
                    shift_reg_valid_by_entry[0] <= shift_reg_valid_by_entry[3];
                    shift_reg_PR_by_entry[0] <= shift_reg_PR_by_entry[3];
                end 
                // take new entry 3
                else begin
                    shift_reg_valid_by_entry[0] <= new_shift_reg_valid_by_entry[3];
                    shift_reg_PR_by_entry[0] <= new_shift_reg_PR_by_entry[3];
                end
            end
            // check take entry 2
                // deq lower 2
            else if (
                &shift_reg_deq_by_bank[1:0]
            ) begin
                // take valid entry 2
                if (shift_reg_valid_by_entry[2]) begin
                    shift_reg_valid_by_entry[0] <= shift_reg_valid_by_entry[2];
                    shift_reg_PR_by_entry[0] <= shift_reg_PR_by_entry[2];
                end 
                // take new entry 2
                else begin
                    shift_reg_valid_by_entry[0] <= new_shift_reg_valid_by_entry[2];
                    shift_reg_PR_by_entry[0] <= new_shift_reg_PR_by_entry[2];
                end
            end
            // check take entry 1
                // deq entry 0
            else if (
                shift_reg_deq_by_bank[0]
            ) begin
                // take valid entry 1
                if (shift_reg_valid_by_entry[1]) begin
                    shift_reg_valid_by_entry[0] <= shift_reg_valid_by_entry[1];
                    shift_reg_PR_by_entry[0] <= shift_reg_PR_by_entry[1];
                end 
                // take new entry 1
                else begin
                    shift_reg_valid_by_entry[0] <= new_shift_reg_valid_by_entry[1];
                    shift_reg_PR_by_entry[0] <= new_shift_reg_PR_by_entry[1];
                end
            end
            // otherwise, take entry 0
            else begin
                // take valid entry 0
                if (shift_reg_valid_by_entry[0]) begin
                    shift_reg_valid_by_entry[0] <= shift_reg_valid_by_entry[0];
                    shift_reg_PR_by_entry[0] <= shift_reg_PR_by_entry[0];
                end 
                // take new entry 0
                else begin
                    shift_reg_valid_by_entry[0] <= new_shift_reg_valid_by_entry[0];
                    shift_reg_PR_by_entry[0] <= new_shift_reg_PR_by_entry[0];
                end
            end

            // --------------------------------------------------------
            // entry 1:
                // custom

            // check take entry 5
                // all 4 deq
            if (
                upper_take_4_above
            ) begin
                // take valid entry 5
                if (shift_reg_valid_by_entry[5]) begin
                    shift_reg_valid_by_entry[1] <= shift_reg_valid_by_entry[5];
                    shift_reg_PR_by_entry[1] <= shift_reg_PR_by_entry[5];
                end 
                // take new entry 5
                else begin
                    shift_reg_valid_by_entry[1] <= new_shift_reg_valid_by_entry[5];
                    shift_reg_PR_by_entry[1] <= new_shift_reg_PR_by_entry[5];
                end
            end
            // check take entry 4
                // deq 3 of 4
            else if (
                upper_take_3_above
            ) begin
                // take valid entry 4
                if (shift_reg_valid_by_entry[4]) begin
                    shift_reg_valid_by_entry[1] <= shift_reg_valid_by_entry[4];
                    shift_reg_PR_by_entry[1] <= shift_reg_PR_by_entry[4];
                end 
                // take new entry 4
                else begin
                    shift_reg_valid_by_entry[1] <= new_shift_reg_valid_by_entry[4];
                    shift_reg_PR_by_entry[1] <= new_shift_reg_PR_by_entry[4];
                end
            end
            // check take entry 3
                // deq 2 of lower 3
            else if (
                shift_reg_deq_by_bank[2] & shift_reg_deq_by_bank[1]
                |
                shift_reg_deq_by_bank[2] & shift_reg_deq_by_bank[0]
                |
                shift_reg_deq_by_bank[1] & shift_reg_deq_by_bank[0]
            ) begin
                // take valid entry 3
                if (shift_reg_valid_by_entry[3]) begin
                    shift_reg_valid_by_entry[1] <= shift_reg_valid_by_entry[3];
                    shift_reg_PR_by_entry[1] <= shift_reg_PR_by_entry[3];
                end 
                // take new entry 3
                else begin
                    shift_reg_valid_by_entry[1] <= new_shift_reg_valid_by_entry[3];
                    shift_reg_PR_by_entry[1] <= new_shift_reg_PR_by_entry[3];
                end
            end
            // check take entry 2
                // deq 1 of lower 2
            else if (
                shift_reg_deq_by_bank[1]
                |
                shift_reg_deq_by_bank[0]
            ) begin
                // take valid entry 2
                if (shift_reg_valid_by_entry[2]) begin
                    shift_reg_valid_by_entry[1] <= shift_reg_valid_by_entry[2];
                    shift_reg_PR_by_entry[1] <= shift_reg_PR_by_entry[2];
                end 
                // take new entry 2
                else begin
                    shift_reg_valid_by_entry[1] <= new_shift_reg_valid_by_entry[2];
                    shift_reg_PR_by_entry[1] <= new_shift_reg_PR_by_entry[2];
                end
            end
            // otherwise, take entry 1
            else begin
                // take valid entry 1
                if (shift_reg_valid_by_entry[1]) begin
                    shift_reg_valid_by_entry[1] <= shift_reg_valid_by_entry[1];
                    shift_reg_PR_by_entry[1] <= shift_reg_PR_by_entry[1];
                end 
                // take new entry 1
                else begin
                    shift_reg_valid_by_entry[1] <= new_shift_reg_valid_by_entry[1];
                    shift_reg_PR_by_entry[1] <= new_shift_reg_PR_by_entry[1];
                end
            end

            // --------------------------------------------------------
            // entry 2:
                // custom

            // check take entry 6
                // all 4 deq
            if (
                upper_take_4_above
            ) begin
                // take valid entry 6
                if (shift_reg_valid_by_entry[6]) begin
                    shift_reg_valid_by_entry[2] <= shift_reg_valid_by_entry[6];
                    shift_reg_PR_by_entry[2] <= shift_reg_PR_by_entry[6];
                end 
                // take new entry 6
                else begin
                    shift_reg_valid_by_entry[2] <= new_shift_reg_valid_by_entry[6];
                    shift_reg_PR_by_entry[2] <= new_shift_reg_PR_by_entry[6];
                end
            end
            // check take entry 5
                // deq 3 of 4
            else if (
                upper_take_3_above
            ) begin
                // take valid entry 5
                if (shift_reg_valid_by_entry[5]) begin
                    shift_reg_valid_by_entry[2] <= shift_reg_valid_by_entry[5];
                    shift_reg_PR_by_entry[2] <= shift_reg_PR_by_entry[5];
                end 
                // take new entry 5
                else begin
                    shift_reg_valid_by_entry[2] <= new_shift_reg_valid_by_entry[5];
                    shift_reg_PR_by_entry[2] <= new_shift_reg_PR_by_entry[5];
                end
            end
            // check take entry 4
                // deq 2 of 4
            else if (
                upper_take_2_above
            ) begin
                // take valid entry 4
                if (shift_reg_valid_by_entry[4]) begin
                    shift_reg_valid_by_entry[2] <= shift_reg_valid_by_entry[4];
                    shift_reg_PR_by_entry[2] <= shift_reg_PR_by_entry[4];
                end 
                // take new entry 4
                else begin
                    shift_reg_valid_by_entry[2] <= new_shift_reg_valid_by_entry[4];
                    shift_reg_PR_by_entry[2] <= new_shift_reg_PR_by_entry[4];
                end
            end
            // check take entry 3
                // deq 1 of lower 3
            else if (
                shift_reg_deq_by_bank[2]
                |
                shift_reg_deq_by_bank[1]
                |
                shift_reg_deq_by_bank[0]
            ) begin
                // take valid entry 3
                if (shift_reg_valid_by_entry[3]) begin
                    shift_reg_valid_by_entry[2] <= shift_reg_valid_by_entry[3];
                    shift_reg_PR_by_entry[2] <= shift_reg_PR_by_entry[3];
                end 
                // take new entry 3
                else begin
                    shift_reg_valid_by_entry[2] <= new_shift_reg_valid_by_entry[3];
                    shift_reg_PR_by_entry[2] <= new_shift_reg_PR_by_entry[3];
                end
            end
            // otherwise, take entry 2
            else begin
                // take valid entry 2
                if (shift_reg_valid_by_entry[2]) begin
                    shift_reg_valid_by_entry[2] <= shift_reg_valid_by_entry[2];
                    shift_reg_PR_by_entry[2] <= shift_reg_PR_by_entry[2];
                end 
                // take new entry 2
                else begin
                    shift_reg_valid_by_entry[2] <= new_shift_reg_valid_by_entry[2];
                    shift_reg_PR_by_entry[2] <= new_shift_reg_PR_by_entry[2];
                end
            end

            // --------------------------------------------------------
            // entry 3:
                // custom

            // check take entry 7
                // all 4 deq
            if (
                upper_take_4_above
            ) begin
                // take valid entry 7
                if (shift_reg_valid_by_entry[7]) begin
                    shift_reg_valid_by_entry[3] <= shift_reg_valid_by_entry[7];
                    shift_reg_PR_by_entry[3] <= shift_reg_PR_by_entry[7];
                end 
                // take new entry 7
                else begin
                    shift_reg_valid_by_entry[3] <= new_shift_reg_valid_by_entry[7];
                    shift_reg_PR_by_entry[3] <= new_shift_reg_PR_by_entry[7];
                end
            end
            // check take entry 6
                // deq 3 of 4
            else if (
                upper_take_3_above
            ) begin
                // take valid entry 6
                if (shift_reg_valid_by_entry[6]) begin
                    shift_reg_valid_by_entry[3] <= shift_reg_valid_by_entry[6];
                    shift_reg_PR_by_entry[3] <= shift_reg_PR_by_entry[6];
                end 
                // take new entry 6
                else begin
                    shift_reg_valid_by_entry[3] <= new_shift_reg_valid_by_entry[6];
                    shift_reg_PR_by_entry[3] <= new_shift_reg_PR_by_entry[6];
                end
            end
            // check take entry 5
                // deq 2 of 4
            else if (
                upper_take_2_above
            ) begin
                // take valid entry 5
                if (shift_reg_valid_by_entry[5]) begin
                    shift_reg_valid_by_entry[3] <= shift_reg_valid_by_entry[5];
                    shift_reg_PR_by_entry[3] <= shift_reg_PR_by_entry[5];
                end 
                // take new entry 5
                else begin
                    shift_reg_valid_by_entry[3] <= new_shift_reg_valid_by_entry[5];
                    shift_reg_PR_by_entry[3] <= new_shift_reg_PR_by_entry[5];
                end
            end
            // check take entry 4
                // deq 1 of lower 4
            else if (
                upper_take_1_above
            ) begin
                // take valid entry 4
                if (shift_reg_valid_by_entry[4]) begin
                    shift_reg_valid_by_entry[3] <= shift_reg_valid_by_entry[4];
                    shift_reg_PR_by_entry[3] <= shift_reg_PR_by_entry[4];
                end 
                // take new entry 4
                else begin
                    shift_reg_valid_by_entry[3] <= new_shift_reg_valid_by_entry[4];
                    shift_reg_PR_by_entry[3] <= new_shift_reg_PR_by_entry[4];
                end
            end
            // otherwise, take entry 3
            else begin
                // take valid entry 3
                if (shift_reg_valid_by_entry[3]) begin
                    shift_reg_valid_by_entry[3] <= shift_reg_valid_by_entry[3];
                    shift_reg_PR_by_entry[3] <= shift_reg_PR_by_entry[3];
                end 
                // take new entry 3
                else begin
                    shift_reg_valid_by_entry[3] <= new_shift_reg_valid_by_entry[3];
                    shift_reg_PR_by_entry[3] <= new_shift_reg_PR_by_entry[3];
                end
            end
        end
    end

    // ----------------------------------------------------------------
    // Array Logic: 

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            // init with 32 AR's mapped to 32 lowest PR's
                // 8 PR's per bank
            for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin
                enq_ptr_by_bank[bank].msb <= 1'b1;
                enq_ptr_by_bank[bank].index <= '0;
                deq_ptr_by_bank[bank] <= (AR_COUNT+12) / FREE_LIST_BANK_COUNT;
            end
        end
        else begin
            enq_ptr_by_bank <= next_enq_ptr_by_bank;
            deq_ptr_by_bank <= next_deq_ptr_by_bank;
        end
    end

    always_comb begin
        for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin

            // enq
            if (array_enq_valid_by_bank[bank]) begin
                next_enq_ptr_by_bank[bank] = enq_ptr_by_bank[bank] + 1;
            end else begin
                next_enq_ptr_by_bank[bank] = enq_ptr_by_bank[bank];
            end

            // deq
            if (array_deq_valid_by_bank[bank]) begin
                next_deq_ptr_by_bank[bank] = deq_ptr_by_bank[bank] + 1;
            end else begin
                next_deq_ptr_by_bank[bank] = deq_ptr_by_bank[bank];
            end
        end
    end

    // empty check (combinational w/ curr pointers)
    always_comb begin
        for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin
            empty_by_bank[bank] = 
                deq_ptr_by_bank[bank].index == enq_ptr_by_bank[bank].index
                &
                deq_ptr_by_bank[bank].msb == enq_ptr_by_bank[bank].msb
            ;
        end
    end

    // full check (sequential w/ curr pointers and worst case -> enq + 1)
    always_comb begin
        for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin
            worst_case_next_enq_ptr_by_bank[bank] = enq_ptr_by_bank[bank] + 1;
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            full_by_bank <= '0;
        end
        else begin
            for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin
                full_by_bank[bank] <= 
                    (
                        deq_ptr_by_bank[bank].index == worst_case_next_enq_ptr_by_bank[bank].index
                        &
                        deq_ptr_by_bank[bank].msb != worst_case_next_enq_ptr_by_bank[bank].msb
                    )
                    |
                    (
                        deq_ptr_by_bank[bank].index == enq_ptr_by_bank[bank].index
                        &
                        deq_ptr_by_bank[bank].msb != enq_ptr_by_bank[bank].msb
                    )
                ;
            end
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            // simple reset with all PR's in ordered slot
                // ptr resets take care of the initially non-free PR's
            free_list_by_bank <= '0;
            
            // interleave values over banks
            for (int pr = 0; pr < PR_COUNT; pr++) begin
                free_list_by_bank[pr[LOG_FREE_LIST_BANK_COUNT-1:0]][pr[LOG_PR_COUNT-1:LOG_FREE_LIST_BANK_COUNT]] <= pr[LOG_PR_COUNT-1:0];
            end

            // // first 12 pr's follow interleave over banks
            // for (int pr = 0; pr < 12; pr++) begin
            //     free_list_by_bank[pr[LOG_FREE_LIST_BANK_COUNT-1:0]][pr[LOG_PR_COUNT-1:LOG_FREE_LIST_BANK_COUNT]] <= pr[LOG_PR_COUNT-1:0];
            // end
            // // put remaining pr's in banks so that get uniform distr over mod4
            // // bank0: 12:40
            // // bank1: 41:69
            // // bank2: 70:98
            // // bank3: 99:127
            // for (int bank = 0; bank < 4; bank++) begin
            //     for (int rem_per_bank = 0; rem_per_bank < 29; rem_per_bank++) begin
            //         free_list_by_bank[bank][rem_per_bank + 3] <= 12 + 29 * bank + rem_per_bank;
            //     end
            // end
        end
        else begin
            for (int bank = 0; bank < FREE_LIST_BANK_COUNT; bank++) begin
                if (array_enq_valid_by_bank[bank]) begin
                    free_list_by_bank[bank][enq_ptr_by_bank[bank].index] <= array_enq_PR_by_bank[bank];
                end
            end
        end
    end

endmodule
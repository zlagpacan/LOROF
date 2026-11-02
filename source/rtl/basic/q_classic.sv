/*
    Filename: q_classic.sv
    Author: zlagpacan
    Description: RTL for ready-valid Queue using classic msb + index method
    Spec: LOROF/spec/design/q_classic.md
*/

module q_classic #(
    parameter DATA_WIDTH = 32,
    parameter NUM_ENTRIES = 4,
    parameter LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES)
) (
    // seq
    input logic CLK,
    input logic nRST,

    // enq
    input logic                     enq_valid,
    input logic [DATA_WIDTH-1:0]    enq_data,

    // enq feedback
    output logic                    enq_ready,

    // deq
    output logic                    deq_valid,
    output logic [DATA_WIDTH-1:0]   deq_data,

    // deq feedback
    input logic                     deq_ready
);

    // ----------------------------------------------------------------
    // Signals: 

    logic [NUM_ENTRIES-1:0][DATA_WIDTH-1:0] q_entries;

    typedef struct packed {
        logic                           msb;
        logic [LOG_NUM_ENTRIES-1:0]     index;
    } q_ptr_t;
    
    q_ptr_t enq_ptr, enq_ptr_plus_1;
    q_ptr_t deq_ptr, deq_ptr_plus_1;

    // ----------------------------------------------------------------
    // Logic: 

    assign deq_data = q_entries[deq_ptr.index];

    generate
        // power-of-2 # entries can use simple +1 for ptr's
        if (NUM_ENTRIES & (NUM_ENTRIES - 1) == 0) begin
            assign enq_ptr_plus_1 = enq_ptr + 1;
            assign deq_ptr_plus_1 = deq_ptr + 1;
        end

        // otherwise, manual wraparound for ptr's
        else begin
            always_comb begin
                if (enq_ptr.index == NUM_ENTRIES - 1) begin
                    enq_ptr_plus_1.msb = ~enq_ptr.msb;
                    enq_ptr_plus_1.index = 0;
                end
                else begin
                    enq_ptr_plus_1.msb = enq_ptr.msb;
                    enq_ptr_plus_1.index = enq_ptr + 1;
                end
                if (deq_ptr.index == NUM_ENTRIES - 1) begin
                    deq_ptr_plus_1.msb = ~deq_ptr.msb;
                    deq_ptr_plus_1.index = 0;
                end
                else begin
                    deq_ptr_plus_1.msb = deq_ptr.msb;
                    deq_ptr_plus_1.index = deq_ptr + 1;
                end
            end
        end
    endgenerate

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            q_entries <= '0;
            enq_ptr <= 0;
            deq_ptr <= 0;
        end
        else begin
            if (enq_ready & enq_valid) begin
                q_entries[enq_ptr.index] <= enq_data;
                enq_ptr <= enq_ptr_plus_1;
            end

            if (deq_ready & deq_valid) begin
                deq_ptr <= deq_ptr_plus_1;
            end
        end
    end

    // enq -> not full
    assign enq_ready = (enq_ptr.index != deq_ptr.index) | (enq_ptr.msb == deq_ptr.msb);

    // deq -> not empty
    assign deq_valid = (enq_ptr.index != deq_ptr.index) | (enq_ptr.msb != deq_ptr.msb);

endmodule
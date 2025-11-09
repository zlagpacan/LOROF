/*
    Filename: cb.sv
    Author: zlagpacan
    Description: RTL for circular buffer
    Spec: LOROF/spec/design/cb.md
*/

module cb #(
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

    // deq
    output logic                    deq_valid,
    output logic [DATA_WIDTH-1:0]   deq_data,

    // deq feedback
    input logic                     deq_ready
);

    // ----------------------------------------------------------------
    // Signals: 

    logic [NUM_ENTRIES-1:0][DATA_WIDTH-1:0] cb_entries;

    logic [NUM_ENTRIES-1:0] valid_by_entry;

    logic [LOG_NUM_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_NUM_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;

    // ----------------------------------------------------------------
    // Logic: 

    assign deq_data = cb_entries[deq_ptr];

    assign deq_valid = valid_by_entry[deq_ptr];

    assign enq_ptr_plus_1 = enq_ptr + 1;
    assign deq_ptr_plus_1 = deq_ptr + 1;

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            cb_entries <= '0;

            valid_by_entry <= '0;
            
            enq_ptr <= 0;
            deq_ptr <= 0;
        end
        else begin
            if (deq_ready & deq_valid) begin
                
                valid_by_entry[deq_ptr] <= 1'b0;

                deq_ptr <= deq_ptr_plus_1;
            end

            if (enq_valid) begin
                cb_entries[enq_ptr] <= enq_data;

                valid_by_entry[enq_ptr] <= 1'b1;
                
                enq_ptr <= enq_ptr_plus_1;
            end
        end
    end

endmodule
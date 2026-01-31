/*
    Filename: q_fast_ready.sv
    Author: zlagpacan
    Description: RTL for ready-valid Queue which clocks its enq ready signal
    Spec: LOROF/spec/design/q_fast_ready.md
*/

module q_fast_ready #(
    parameter DATA_WIDTH = 32,
    parameter NUM_ENTRIES = 32,
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

    logic [LOG_NUM_ENTRIES-1:0] enq_ptr, enq_ptr_plus_1;
    logic [LOG_NUM_ENTRIES-1:0] deq_ptr, deq_ptr_plus_1;

    // ----------------------------------------------------------------
    // Logic: 

    generate
        // power-of-2 # entries can use simple +1 for ptr's
        if (NUM_ENTRIES & (NUM_ENTRIES - 1) == 0) begin
            assign enq_ptr_plus_1 = enq_ptr + 1;
            assign deq_ptr_plus_1 = deq_ptr + 1;
        end

        // otherwise, manual wraparound for ptr's
        else begin
            always_comb begin
                if (enq_ptr == NUM_ENTRIES - 1) begin
                    enq_ptr_plus_1 = 0;
                end
                else begin
                    enq_ptr_plus_1 = enq_ptr + 1;
                end
                if (deq_ptr == NUM_ENTRIES - 1) begin
                    deq_ptr_plus_1 = 0;
                end
                else begin
                    deq_ptr_plus_1 = deq_ptr + 1;
                end
            end
        end
    endgenerate

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            enq_ptr <= 0;
            deq_ptr <= 0;
            enq_ready <= 1'b1;
            deq_valid <= 1'b0;
        end
        else begin
            if (enq_ready & enq_valid) begin
                enq_ptr <= enq_ptr_plus_1;
            end

            if (deq_ready & deq_valid) begin
                deq_ptr <= deq_ptr_plus_1;
            end

            if ((enq_ready & enq_valid) & ~(deq_ready & deq_valid)) begin
                enq_ready <= enq_ptr_plus_1 != deq_ptr;
                deq_valid <= 1'b1;
            end

            if ((deq_ready & deq_valid) & ~(enq_ready & enq_valid)) begin
                enq_ready <= 1'b1;
                deq_valid <= deq_ptr_plus_1 != enq_ptr;
            end
        end
    end

    distram_1rport_1wport #(
        .INNER_WIDTH(DATA_WIDTH),
        .OUTER_WIDTH(NUM_ENTRIES)
    ) DISTRAM_BUFFER (
        .CLK(CLK),
        .rindex(deq_ptr),
        .rdata(deq_data),
        .wen(enq_ready & enq_valid),
        .windex(enq_ptr),
        .wdata(enq_data)
    );

endmodule
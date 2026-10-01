/*
    Filename: free_list.sv
    Author: zlagpacan
    Description: RTL for Physical Register Free List
    Spec: LOROF/spec/design/free_list.md
*/

`include "corep.vh"

module free_list #(
    parameter int unsigned INGRESS_BUFFER_ENTRIES = 16,
    parameter int unsigned EGRESS_BUFFER_ENTRIES = 16,
    
    parameter string INIT_FILES_BY_WAY [0:3] = {"free_list_way0.mem", "free_list_way1.mem", "free_list_way2.mem", "free_list_way3.mem"}
) (
    // seq
    input logic CLK,
    input logic nRST,

    // enq
    input logic [3:0]           enq_valid_by_way,
    input corep::pr_t [3:0]     enq_pr_by_way,

    // enq feedback
    output logic [3:0]          enq_ready_by_way,

    // deq
    output logic [3:0]          deq_valid_by_way,
    output corep::pr_t [3:0]    deq_pr_by_way,

    // deq feedback
    input logic [3:0]           deq_ready_by_way
);

    // ----------------------------------------------------------------
    // Signals:
    
    // ingress buffer
    logic [3:0]         ingress_enq_valid_by_way;
    corep::pr_t [3:0]   ingress_enq_pr_by_way;
    logic [3:0]         ingress_enq_ready_by_way;

    logic [3:0]         ingress_deq_valid_by_way;
    corep::pr_t [3:0]   ingress_deq_pr_by_way;
    logic [3:0]         ingress_deq_ready_by_way;

    // rotator
    logic [1:0]         rotator;
    logic [3:0][1:0]    rotation_by_way;
    
    // egress buffer
    logic [3:0]         egress_enq_valid_by_way;
    corep::pr_t [3:0]   egress_enq_pr_by_way;
    logic [3:0]         egress_enq_ready_by_way;

    logic [3:0]         egress_deq_valid_by_way;
    corep::pr_t [3:0]   egress_deq_pr_by_way;
    logic [3:0]         egress_deq_ready_by_way;

    // ----------------------------------------------------------------
    // Logic:

    // rotator FSM
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            rotator <= 2'h0;
        end
        else begin
            rotator <= rotator + 2'h1;
        end
    end

    // ingress buffers
    always_comb begin
        for (int way = 0; way < 4; way++) begin
            ingress_enq_valid_by_way[way] = enq_valid_by_way[way];
            ingress_enq_pr_by_way[way] = enq_pr_by_way[way];

            enq_ready_by_way[way] = ingress_enq_ready_by_way[way];
        end
    end

    genvar ingress_way;
    generate
        for (ingress_way = 0; ingress_way < 4; ingress_way++) begin
            q_fast_ready #(
                .DATA_WIDTH($bits(corep::pr_t)),
                .NUM_ENTRIES(INGRESS_BUFFER_ENTRIES)
            ) INGRESS_BUFFER (
                .CLK(CLK),
                .nRST(nRST),
                .enq_valid(ingress_enq_valid_by_way[ingress_way]),
                .enq_data(ingress_enq_pr_by_way[ingress_way]),
                .enq_ready(ingress_enq_ready_by_way[ingress_way]),
                .deq_valid(ingress_deq_valid_by_way[ingress_way]),
                .deq_data(ingress_deq_pr_by_way[ingress_way]),
                .deq_ready(ingress_deq_ready_by_way[ingress_way])
            );
        end
    endgenerate

    // rotator mux
    always_comb begin
        for (int way = 0; way < 4; way++) begin
            rotation_by_way[way] = way + rotator;

            egress_enq_valid_by_way[way] = ingress_deq_valid_by_way[rotation_by_way[way]];
            egress_enq_pr_by_way[way] = ingress_deq_pr_by_way[rotation_by_way[way]];

            ingress_deq_ready_by_way[rotation_by_way[way]] = egress_enq_ready_by_way[way];
        end
    end

    // egress buffer
    genvar egress_way;
    generate
        for (egress_way = 0; egress_way < 4; egress_way++) begin
            q_fast_ready #(
                .DATA_WIDTH($bits(corep::pr_t)),
                .NUM_ENTRIES(EGRESS_BUFFER_ENTRIES),
                .INIT_ENQ_PTR(0),
                .INIT_DEQ_PTR(0),
                .INIT_ENQ_READY(1'b0),
                .INIT_DEQ_VALID(1'b1),
                .INIT_FILE(INIT_FILES_BY_WAY[egress_way])
            ) EGRESS_BUFFER (
                .CLK(CLK),
                .nRST(nRST),
                .enq_valid(egress_enq_valid_by_way[egress_way]),
                .enq_data(egress_enq_pr_by_way[egress_way]),
                .enq_ready(egress_enq_ready_by_way[egress_way]),
                .deq_valid(egress_deq_valid_by_way[egress_way]),
                .deq_data(egress_deq_pr_by_way[egress_way]),
                .deq_ready(egress_deq_ready_by_way[egress_way])
            );
        end
    endgenerate

    always_comb begin
        for (int way = 0; way < 4; way++) begin
            deq_valid_by_way[way] = egress_deq_valid_by_way[way];
            deq_pr_by_way[way] = egress_deq_pr_by_way[way];

            egress_deq_ready_by_way[way] = deq_ready_by_way[way];
        end
    end

endmodule
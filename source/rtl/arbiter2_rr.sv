/*
    Filename: arbiter2_rr.sv
    Author: zlagpacan
    Description: RTL for 2x Round-Robin Arbiter
    Spec: LOROF/spec/design/arbiter2_rr.md
*/

module arbiter2_rr #(
    parameter REQUESTOR_COUNT = 8,
    parameter LOG_REQUESTOR_COUNT = $clog2(REQUESTOR_COUNT)
) (
    // seq
    input logic CLK,
    input logic nRST,
 
    input logic                         req_valid,
    input logic [REQUESTOR_COUNT-1:0]   req_vec,

    output logic                        port0_ack_valid,
    output logic [REQUESTOR_COUNT-1:0]  port0_ack_one_hot,

    output logic                        port1_ack_valid,
    output logic [REQUESTOR_COUNT-1:0]  port1_ack_one_hot
);

    logic [REQUESTOR_COUNT-1:0] req_mask, next_req_mask;

    logic [REQUESTOR_COUNT-1:0] masked_req_vec;

    logic [REQUESTOR_COUNT-1:0] port0_masked_ack_one_hot;
    logic [REQUESTOR_COUNT-1:0] port0_unmasked_ack_one_hot;

    logic [REQUESTOR_COUNT-1:0] port1_masked_ack_one_hot;
    logic [REQUESTOR_COUNT-1:0] port1_unmasked_ack_one_hot;

    logic masked_found_second;
    logic unmasked_found_second;

    always_ff @ (posedge CLK, negedge nRST) begin
    // always_ff @ (posedge CLK) begin
        if (~nRST) begin
            req_mask <= '0;
        end
        else if (req_valid) begin
            req_mask <= next_req_mask;
        end
    end
    
    always_comb begin
        masked_req_vec = req_vec & req_mask;
    end

    pe_lsb #(
        .WIDTH(REQUESTOR_COUNT)
    ) MASKED_PORT0_PE_LSB (
        .req_vec(masked_req_vec),
        .ack_one_hot(port0_masked_ack_one_hot)
    );

    pe_lsb #(
        .WIDTH(REQUESTOR_COUNT)
    ) UNMASKED_PORT0_PE_LSB (
        .req_vec(req_vec),
        .ack_one_hot(port0_unmasked_ack_one_hot)
    );

    pe2_lsb #(
        .WIDTH(REQUESTOR_COUNT)
    ) MASKED_PORT1_PE2_LSB (
        .req_vec(req_vec),
        .ack_one_hot(port1_masked_ack_one_hot),
        .found_first(),
        .found_second(masked_found_second)
    );

    pe2_lsb #(
        .WIDTH(REQUESTOR_COUNT)
    ) UNMASKED_PORT1_PE2_LSB (
        .req_vec(masked_req_vec),
        .ack_one_hot(port1_unmasked_ack_one_hot),
        .found_first(),
        .found_second(unmasked_found_second)
    );

    always_comb begin
        port0_ack_valid = |req_vec;
        port1_ack_valid = unmasked_found_second;

        if (|masked_req_vec) begin
            port0_ack_one_hot = port0_masked_ack_one_hot;
        end
        else begin
            port0_ack_one_hot = port0_unmasked_ack_one_hot;
        end

        if (masked_found_second) begin
            port1_ack_one_hot = port1_masked_ack_one_hot;
        end
        else if (|masked_req_vec) begin
            port1_ack_one_hot = port0_unmasked_ack_one_hot;
        end
        else begin
            port1_ack_one_hot = port1_unmasked_ack_one_hot;
        end

        next_req_mask[0] = 1'b0;
        for (int i = 1; i < REQUESTOR_COUNT; i++) begin
            next_req_mask[i] = next_req_mask[i-1] | port1_ack_one_hot[i-1];
        end
    end

endmodule
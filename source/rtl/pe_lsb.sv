/*
    Filename: pe_lsb.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing lsb
*/

module pe_lsb #(
    parameter WIDTH = 8,
    parameter USE_ONE_HOT = 1,
    parameter USE_COLD = 0,
    parameter USE_INDEX = 0
)(
    input logic [WIDTH-1:0]             req_vec,

    output logic [WIDTH-1:0]            ack_one_hot,
    output logic [WIDTH-1:0]            ack_mask,
    output logic [WIDTH-1:0]            cold_ack_mask,
    output logic [$clog2(WIDTH)-1:0]    ack_index
);

    always_comb begin

        // init clear vec
        ack_mask = '0;
        if (USE_ONE_HOT) ack_one_hot = '0;
        if (USE_COLD) cold_ack_mask = '0;
        if (USE_INDEX) ack_index = 0;

        // lsb bit: special since no lower mask bit
        begin
            // check this req hot
            if (req_vec[0]) begin
                // enable this mask bit
                ack_mask[0] = 1'b1;
                // one-hot
                if (USE_ONE_HOT) ack_one_hot[0] = 1'b1;
                // set index
                if (USE_INDEX) ack_index = 0;
            end
            // otherwise, nothing hot yet
            else begin
                // disable this mask bit
                ack_mask[0] = 1'b0;
                // not one-hot
                if (USE_ONE_HOT) ack_one_hot[0] = 1'b0;
            end
            // lsb guaranteed cold
            if (USE_COLD) cold_ack_mask[0] = 1'b0;
        end

        // go through req vec bits after lsb
        for (int i = 1; i < WIDTH; i++) begin

            // check previous mask
            if (ack_mask[i-1]) begin
                // enable this mask bit
                ack_mask[i] = 1'b1;
                // not one-hot
                if (USE_ONE_HOT) ack_one_hot[i] = 1'b0;
                // enable this cold mask bit
                if (USE_COLD) cold_ack_mask[i] = 1'b1;
            end
            // otherwise, check this req hot
            else if (req_vec[i]) begin
                // enable this mask bit
                ack_mask[i] = 1'b1;
                // one-hot
                if (USE_ONE_HOT) ack_one_hot[i] = 1'b1;
                // mask still cold
                if (USE_COLD) cold_ack_mask[i] = 1'b0;
                // set index
                if (USE_INDEX) ack_index = i;
            end
            // otherwise, nothing hot yet
            else begin
                // disable this mask bit
                ack_mask[i] = 1'b0;
                // not one-hot
                if (USE_ONE_HOT) ack_one_hot[i] = 1'b0;
                // mask still cold
                if (USE_COLD) cold_ack_mask[i] = 1'b0;
            end
        end
    end

endmodule
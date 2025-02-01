/*
    Filename: pq_lsb.sv
    Author: zlagpacan
    Description: RTL for Priority Queue prioritizing lsb
*/

module pq_lsb #(
    parameter WIDTH = 8
)(
    input logic [WIDTH-1:0]             req_vec,

    output logic [WIDTH-1:0]            ack_one_hot,
    output logic [WIDTH-1:0]            ack_mask,
    output logic [WIDTH-1:0]            cold_ack_mask,
    output logic [$clog2(WIDTH)-1:0]    ack_index
);

    always_comb begin

        // init clear vec
        ack_one_hot = '0;
        ack_mask = '0;
        cold_ack_mask = '0;
        ack_index = 0;

        // lsb bit: special since no lower mask bit
        begin
            // check this req hot
            if (req_vec[0]) begin
                // one-hot
                ack_one_hot[0] = 1'b1;
                // enable this mask bit
                ack_mask[0] = 1'b1;
                // set index
                ack_index = 0;
            end
            // otherwise, nothing hot yet
            else begin
                // not one-hot
                ack_one_hot[0] = 1'b0;
                // disable this mask bit
                ack_mask[0] = 1'b0;
            end
            // lsb guaranteed cold
            cold_ack_mask[0] = 1'b0;
        end

        // go through req vec bits after lsb
        for (int i = 1; i < WIDTH; i++) begin

            // check previous mask
            if (ack_mask[i-1]) begin
                // not one-hot
                ack_one_hot[i] = 1'b0;
                // enable this mask bit
                ack_mask[i] = 1'b1;
                // enable this cold mask bit
                cold_ack_mask[i] = 1'b1;
            end
            // otherwise, check this req hot
            else if (req_vec[i]) begin
                // one-hot
                ack_one_hot[i] = 1'b1;
                // enable this mask bit
                ack_mask[i] = 1'b1;
                // mask still cold
                cold_ack_mask[i] = 1'b0;
                // set index
                ack_index = i;
            end
            // otherwise, nothing hot yet
            else begin
                // not one-hot
                ack_one_hot[i] = 1'b0;
                // disable this mask bit
                ack_mask[i] = 1'b0;
                // mask still cold
                cold_ack_mask[i] = 1'b0;
            end
        end
    end

endmodule
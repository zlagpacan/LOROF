/*
    Filename: pq_lsb.sv
    Author: zlagpacan
    Description: RTL for priority queue prioritizing lsb
    Spec: LOROF/spec/design/pq_lsb.md
*/

module pq_lsb #(
    parameter WIDTH = 8
)(
    input logic [WIDTH-1:0]     req_vec,
    output logic [WIDTH-1:0]    ack_one_hot,
    output logic [WIDTH-1:0]    ack_mask
);

    always_comb begin

        // init clear vec
        ack_one_hot = '0;
        ack_mask = '0;

        // msb bit: special since no higher mask bit
        begin

            // check this req hot
            if (req_vec[WIDTH-1]) begin

                // new one-hot ack vec
                ack_one_hot = '0;
                ack_one_hot[WIDTH-1] = 1'b1;

                // enable this mask bit
                ack_mask[WIDTH-1] = 1'b1;
            end
        end


        // go through req vec bits after msb
            // msb to lsb so lsb gets last say
        for (int i = WIDTH-2; i >= 0; i--) begin
            
            // check this req hot
            if (req_vec[i]) begin

                // new one-hot ack vec
                    // override any higher bit one-hot
                ack_one_hot = '0;
                ack_one_hot[i] = 1'b1;

                // enable this mask bit
                ack_mask[i] = 1'b1;
            end

            // turn on this mask bit if previous was on (not possible for msb)
            if (ack_mask[i+1]) begin
                ack_mask[i] = 1'b1;
            end
        end
    end

endmodule
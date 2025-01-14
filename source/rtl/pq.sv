module pq #(
    parameter WIDTH = 14
)(
    input logic [WIDTH-1:0] req_vec,
    output logic [WIDTH-1:0] pq_vec
);

    always_comb begin
        
        // init clear vec
        pq_vec = '0;

        // go through req vec
        for (int i = 0; i < WIDTH; i++) begin
            
            // check this req hot
            if (req_vec[i]) begin

                // new one-hot vec
                    // override any lsb one-hot
                pq_vec = '0;
                pq_vec[i] = 1'b1;
            end
        end
    end

endmodule
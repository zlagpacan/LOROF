/*
    Filename: peN_lsb_tree.sv
    Author: zlagpacan
    Description: RTL for Priority Encoder prioritizing first N lsb's using for tree logic
        - ChatGPT help
*/

module peN_lsb_tree #(
    parameter int unsigned WIDTH = 8,
    parameter int unsigned N = 3,
    parameter int unsigned LOG_WIDTH = $clog2(WIDTH)
)(
    input  logic [WIDTH-1:0]                req_vec,

    output logic [N-1:0]                    ack_valid_by_n,
    output logic [N-1:0][LOG_WIDTH-1:0]     ack_index_by_n
);

    function automatic logic [LOG_WIDTH:0] first_one (
        input logic [WIDTH-1:0] vec
    );
        // Returns {valid, index}
        logic [WIDTH-1:0] stage   [0:$clog2(WIDTH)];
        logic [LOG_WIDTH-1:0] idx     [0:$clog2(WIDTH)][WIDTH-1:0];

        int levels;
        levels = (WIDTH > 1) ? $clog2(WIDTH) : 1;

        stage[0] = vec;

        // Initialize indices
        for (int i = 0; i < WIDTH; i++)
            idx[0][i] = i[LOG_WIDTH-1:0];

        // Build tree
        for (int l = 0; l < levels; l++) begin
            int stride = 1 << l;
            for (int i = 0; i < WIDTH; i += (stride << 1)) begin
                int L = i;
                int R = i + stride;

                if (R < WIDTH) begin
                    stage[l+1][i] = stage[l][L] | stage[l][R];
                    idx[l+1][i]   = stage[l][L] ? idx[l][L]
                                                : idx[l][R];
                end
                else begin
                    stage[l+1][i] = stage[l][L];
                    idx[l+1][i]   = idx[l][L];
                end
            end
        end

        return {stage[levels][0], idx[levels][0]};
    endfunction

    logic [WIDTH-1:0]       masked;
    logic [LOG_WIDTH:0]     result;

    always_comb begin
        masked = req_vec;

        for (int j = 0; j < N; j++) begin
            result = first_one(masked);

            ack_valid_by_n[j] = result[LOG_WIDTH];
            ack_index_by_n[j] = result[LOG_WIDTH-1:0];

            if (result[LOG_WIDTH])
                masked[result[LOG_WIDTH-1:0]] = 1'b0;
        end
    end

endmodule

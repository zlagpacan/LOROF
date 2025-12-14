/*
    Filename: plru.sv
    Author: zlagpacan
    Description: RTL for Power-of-2 Pseudo-LRU Combinational Block
    Spec: LOROF/spec/design/plru.md
*/

module plru #(
    parameter NUM_ENTRIES = 4,
    parameter LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES)
) (
    input logic [NUM_ENTRIES-2:0]       plru_in,

    input logic                         new_valid,
    output logic [LOG_NUM_ENTRIES-1:0]  new_index,

    input logic                         touch_valid,
    input logic [LOG_NUM_ENTRIES-1:0]   touch_index,

    output logic [NUM_ENTRIES-2:0]      plru_out
);

    genvar level;
    generate
        always_comb begin
            new_index[0] = plru_in[0];

            if (new_valid) begin
                plru_out[0] = ~new_index[0];
            end
            else if (touch_valid) begin
                plru_out[0] = ~touch_index[0];
            end
            else begin
                plru_out[0] = plru_in[0];
            end
        end

        for (level = 1; level < LOG_NUM_ENTRIES; level++) begin
            always_comb begin
                plru_out[(2**(level+1))-2:(2**level)-1] = plru_in[(2**(level+1))-2:(2**level)-1];
                if (new_valid) begin
                    plru_out[(2**(level+1))-2:(2**level)-1][new_index[level-1:0]] = ~new_index[level];
                end
                else if (touch_valid) begin
                    plru_out[(2**(level+1))-2:(2**level)-1][touch_index[level-1:0]] = ~touch_index[level];
                end
            end
        end
    endgenerate

    // always_comb begin
    //     for (int level = 0; level < LOG_NUM_ENTRIES; level++) begin
    //         new_index[level] = plru_in[(2**(level+1))-2:(2**level)-1];
    //     end

    //     plru_out = plru_in;
    //     if (new_valid) begin
    //         plru_out[0] = ~new_index[0];
    //         for (int level = 1; level < LOG_NUM_ENTRIES; level++) begin
    //             // plru_out[(2**(level+1))-2:(2**level)-1][plru_in[(2**(level-1+1))-2:(2**(level-1))-1]] = ~plru_in[(2**(level+1))-2:(2**level)-1][plru_in[(2**(level-1+1))-2:(2**(level-1))-1]];
    //             plru_out[(2**(level+1))-2:(2**level)-1][new_index[level-1:0]] = ~new_index[level];
    //         end
    //     end
    //     else if (touch_valid) begin
    //         plru_out[0] = ~touch_index[0];
    //         for (int level = 1; level < LOG_NUM_ENTRIES; level++) begin
    //             plru_out[(2**(level+1))-2:(2**level)-1][touch_index[level-1:0]] = ~touch_index[level];
    //         end
    //     end
    // end

endmodule
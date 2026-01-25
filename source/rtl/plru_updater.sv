/*
    Filename: plru_updater.sv
    Author: zlagpacan
    Description: RTL for Power-of-2 Pseudo-LRU Combinational Block
    Spec: LOROF/spec/design/plru_updater.md
*/

module plru_updater #(
    parameter int unsigned NUM_ENTRIES = 8,
    parameter int unsigned LOG_NUM_ENTRIES = $clog2(NUM_ENTRIES)
) (
    input logic [NUM_ENTRIES-2:0]       plru_in,

    input logic                         new_valid,
    output logic [LOG_NUM_ENTRIES-1:0]  new_way,

    input logic                         touch_valid,
    input logic [LOG_NUM_ENTRIES-1:0]   touch_way,

    output logic [NUM_ENTRIES-2:0]      plru_out
);

    genvar level;
    generate
        always_comb begin
            new_way[0] = plru_in[0];

            if (new_valid) begin
                plru_out[0] = ~new_way[0];
            end
            else if (touch_valid) begin
                plru_out[0] = ~touch_way[0];
            end
            else begin
                plru_out[0] = plru_in[0];
            end
        end

        for (level = 1; level < LOG_NUM_ENTRIES; level++) begin
            logic [(2**level)-1:0] sub_plru_in;
            logic [(2**level)-1:0] sub_plru_out;

            always_comb begin
                sub_plru_in = plru_in[(2**(level+1))-2:(2**level)-1];

                new_way[level] = sub_plru_in[new_way[level-1:0]];

                sub_plru_out = sub_plru_in;
                if (new_valid) begin
                    sub_plru_out[new_way[level-1:0]] = ~new_way[level];
                end
                else if (touch_valid) begin
                    sub_plru_out[touch_way[level-1:0]] = ~touch_way[level];
                end
                
                plru_out[(2**(level+1))-2:(2**level)-1] = sub_plru_out;
            end
        end
    endgenerate

endmodule
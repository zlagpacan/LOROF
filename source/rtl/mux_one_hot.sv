/*
    Filename: mux_one_hot.sv
    Author: zlagpacan
    Description: RTL for 2x Round-Robin Arbiter
    Spec: LOROF/spec/design/mux_one_hot.md
*/

module mux_one_hot #(
    parameter COUNT = 4,
    parameter WIDTH = 32
) (
    input logic [COUNT-1:0]             sel_one_hot,
    input logic [COUNT-1:0][WIDTH-1:0]  data_by_requestor,

    output logic [WIDTH-1:0] selected_data
);
    always_comb begin
        selected_data = '0;
        for (int i = 0; i < COUNT; i++) begin
            if (sel_one_hot[i]) begin
                selected_data |= data_by_requestor[i];
            end
        end
    end

endmodule
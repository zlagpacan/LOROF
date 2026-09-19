/*
    Filename: pmux_lsb_for.sv
    Author: zlagpacan
    Description: RTL for Priority Mux
*/

module pmux_lsb_for #(
    parameter int unsigned SEL_WIDTH = 8,
    parameter int unsigned DATA_WIDTH = 8
) (
    input logic [SEL_WIDTH-1:0]                     req_valid_vec,
    input logic [SEL_WIDTH-1:0][DATA_WIDTH-1:0]     req_data_vec,

    output logic [DATA_WIDTH-1:0]                   rsp_data
);

    logic found_data;

    always_comb begin
        rsp_data = req_data_vec[SEL_WIDTH-1];
        
        for (int i = 0; i < SEL_WIDTH; i++) begin
            if (req_valid_vec[i]) begin
                rsp_data = req_data_vec[i];
                break;
            end
        end
    end

endmodule
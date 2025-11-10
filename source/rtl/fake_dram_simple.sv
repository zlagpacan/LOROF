/*
    Filename: fake_dram_simple.sv
    Author: zlagpacan
    Description: RTL for Fake DRAM with simple byte-wide async read interface. Not intended to be synthesized.
    Spec: LOROF/spec/design/fake_dram_simple.md
*/

`include "system_types_pkg.vh"
import system_types_pkg::*;

module fake_dram_simple #(
    parameter SIZE = 2**16,
    parameter INDEX_WIDTH = $clog2(SIZE),
    parameter INIT_FILE = ""
) (
    // seq
    input logic CLK,
    input logic nRST,
    
    input logic [INDEX_WIDTH-1:0] rindex,
    output logic [7:0] rbyte,
    
    input logic wen,
    input logic [INDEX_WIDTH-1:0] windex,
    input logic [7:0] wbyte
);

    logic [7:0] dram_byte_array [0:SIZE-1];  
    
    // init values
    initial begin
        // default to 0's, overwrite with INIT_FILE if present
        for (int i = 0; i < SIZE; i++) begin
            dram_byte_array[i] = '0;
        end
        if (INIT_FILE != "") begin
            $display("fake_dram_simple: initializing from %s", INIT_FILE);
            $readmemh(INIT_FILE, dram_byte_array, 0, SIZE-1);
        end
        else begin
            $display("fake_dram_simple: initializing all zero's", INIT_FILE);
        end
    end

    // distram read ports
    assign rbyte = dram_byte_array[rindex];
    
    // distram write port
    always @ (posedge CLK) begin
        if (wen) dram_byte_array[windex] <= wbyte;
    end

endmodule
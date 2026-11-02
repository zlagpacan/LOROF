/*
    Filename: bram_1rwport.sv
    Author: zlagpacan
    Description: RTL for BRAM with 1 read/write port
*/

module bram_1rwport #(
    parameter INNER_WIDTH = 32,
    parameter OUTER_WIDTH = 32,
    parameter INIT_FILE = ""
)(
    input logic CLK,
    input logic nRST,
    
    input logic ren,
    input logic [INNER_WIDTH/8-1:0] wen_byte,
    input logic [$clog2(OUTER_WIDTH)-1:0] rwindex,
    output logic [INNER_WIDTH-1:0] rdata,
    input logic [INNER_WIDTH-1:0] wdata
);

    logic [INNER_WIDTH-1:0] bram_array [0:OUTER_WIDTH-1];
    logic [INNER_WIDTH-1:0] rreg;
    
    // bram init values
    generate
        if (INIT_FILE != "") begin: use_init_file
            initial begin
                $readmemh(INIT_FILE, bram_array, 0, (OUTER_WIDTH * INNER_WIDTH/8)-1);
            end
        end 
        else begin: init_bram_to_zero
            initial begin
                for (int i = 0; i < OUTER_WIDTH; i++) begin
                    bram_array[i] = '0;
                end
            end
        end
    endgenerate

    // bram read ports
    always @ (posedge CLK, negedge nRST) begin : bram_read
        if (~nRST) begin
            rreg <= '0;
        end
        else begin
            if (ren) rreg <= bram_array[rwindex];
        end
    end
    
    // bram write port
    generate
        genvar wbyte;
        for (wbyte = 0; wbyte < INNER_WIDTH/8; wbyte++) begin: bram_write
            always @ (posedge CLK) begin
                if (wen_byte[wbyte]) bram_array[rwindex][(wbyte+1)*8-1:wbyte*8] <= wdata[(wbyte+1)*8-1:wbyte*8];
            end
        end
    endgenerate 
    
    // read port to output connection
        // if register these, get better freq
    assign rdata = rreg;

endmodule

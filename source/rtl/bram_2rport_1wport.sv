/*
    Filename: bram_2rport_1wport.sv
    Author: zlagpacan
    Description: RTL for BRAM with 2 read ports and 1 write port
*/

module bram_2rport_1wport #(
    parameter INNER_WIDTH = 32,
    parameter OUTER_WIDTH = 32,
    parameter INIT_FILE = ""
)(
    input logic CLK,
    input logic nRST,
    
    input logic port0_ren,
    input logic [$clog2(OUTER_WIDTH)-1:0] port0_rindex,
    output logic [INNER_WIDTH-1:0] port0_rdata,
    
    input logic port1_ren,
    input logic [$clog2(OUTER_WIDTH)-1:0] port1_rindex,
    output logic [INNER_WIDTH-1:0] port1_rdata,
    
    input logic [INNER_WIDTH/8-1:0] wen_byte,
    input logic [$clog2(OUTER_WIDTH)-1:0] windex,
    input logic [INNER_WIDTH-1:0] wdata
);

    logic [INNER_WIDTH-1:0] bram_array [OUTER_WIDTH-1:0];
    logic [INNER_WIDTH-1:0] port0_rreg;
    logic [INNER_WIDTH-1:0] port1_rreg;    
    
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
            port0_rreg <= '0;
            port1_rreg <= '0;
        end
        else begin
            if (port0_ren) port0_rreg <= bram_array[port0_rindex];
            if (port1_ren) port1_rreg <= bram_array[port1_rindex];
        end
    end
    
    // bram write port
    generate
        genvar wbyte;
        for (wbyte = 0; wbyte < INNER_WIDTH/8; wbyte++) begin: bram_write
            always @ (posedge CLK) begin
                if (wen_byte[wbyte]) bram_array[windex][(wbyte+1)*8-1:wbyte*8] <= wdata[(wbyte+1)*8-1:wbyte*8];
            end
        end
    endgenerate 
    
    // read port to output connection
        // if register these, get better freq
    assign port0_rdata = port0_rreg;
    assign port1_rdata = port1_rreg;

endmodule

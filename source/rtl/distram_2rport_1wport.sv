module distram_2rport_1wport #(
    parameter INNER_WIDTH = 32,
    parameter OUTER_WIDTH = 32,
    parameter INIT_FILE = ""
)(
    input logic CLK,
    
    input logic [$clog2(OUTER_WIDTH)-1:0] port0_rindex,
    output logic [INNER_WIDTH-1:0] port0_rdata,
    
    input logic [$clog2(OUTER_WIDTH)-1:0] port1_rindex,
    output logic [INNER_WIDTH-1:0] port1_rdata,
    
    input logic wen,
    input logic [$clog2(OUTER_WIDTH)-1:0] windex,
    input logic [INNER_WIDTH-1:0] wdata
);

    logic [INNER_WIDTH-1:0] distram_array [OUTER_WIDTH-1:0];  
    
    // distram init values
    generate
        if (INIT_FILE != "") begin: use_init_file
            initial begin
                $readmemh(INIT_FILE, distram_array, 0, (OUTER_WIDTH * INNER_WIDTH/8)-1);
            end
        end 
        else begin: init_distram_to_zero
            initial begin
                for (int i = 0; i < OUTER_WIDTH; i++) begin
                    distram_array[i] = '0;
                end
            end
        end
    endgenerate

    // distram read ports
    assign port0_rdata = distram_array[port0_rindex];
    assign port1_rdata = distram_array[port1_rindex];
    
    // distram write port
    always @ (posedge CLK) begin
        if (wen) distram_array[windex] <= wdata;
    end

endmodule

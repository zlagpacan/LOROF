module progctr #(parameter PC_NUM_BITS = 16) (
    input  logic clk,
    input  logic n_rst,
    input  logic count_en,
    output logic [(PC_NUM_BITS-1):0] pc
);
    // --- Configuration --- //
    parameter MAX_COUNT = (2 ** PC_NUM_BITS) - 1;\
    // comment above and uncomment below to trip assertion
    // parameter MAX_COUNT = (2 ** PC_NUM_BITS) - 3; // bug

    // --- Registers --- //
    logic [(PC_NUM_BITS-1):0] pc_reg;
    logic [(PC_NUM_BITS-1):0] nxt_pc_reg;

    // --- Flip Flop --- //
    always_ff @ (posedge clk, negedge n_rst) begin : PROGCTR_FF
        if (!n_rst) begin
            pc_reg <= '0;
        end else begin
            pc_reg <= nxt_pc_reg;
        end
    end

    // --- Comb Logic --- //
    always_comb begin : PROGCTR_COMB
        nxt_pc_reg = pc_reg;

        if (!count_en) begin
            nxt_pc_reg = nxt_pc_reg;
        end else if (nxt_pc_reg == MAX_COUNT) begin
            nxt_pc_reg = '0;
        end else begin
            nxt_pc_reg += 1;
        end
    end

    // --- Interface --- //
    assign pc = pc_reg;


`ifdef FORMAL

    always @(posedge clk) begin
        if (n_rst) begin
            a_max_count: assert (pc <= MAX_COUNT);
        end
    end

`endif

endmodule
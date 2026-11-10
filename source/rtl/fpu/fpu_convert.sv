/*
    Filename: fpu_easy.sv
    Author: zlagpacan
    Description: Easy FPU Instructions
    Spec: LOROF/spec/design/fpu_easy.md
*/

`include "fpp.vh"
`include "corep.vh"

module fpu_easy #(

) (
    // seq
    input logic CLK,
    input logic nRST,

    // input control
    input logic             in_valid,
    input corep::pr_t       in_dest_pr,
    input corep::rob_idx_t  in_rob_idx,

    output logic            in_ready,

    // instr components
    input logic [6:0]       in_funct7,
    input logic [2:0]       in_funct3,

    // operands
    input fpp::double_t     in_A_d,
    input fpp::double_t     in_B_d,

    input fpp::single_t     in_A_s_boxed, // post NaN-box check
    input fpp::single_t     in_B_s_boxed, // post NaN-box check

    // output control
    output logic                out_valid,
    output corep::pr_t          out_dest_pr,
    output corep::rob_idx_t     out_rob_idx,

    input logic                 out_ready,

    // fp output
    output fpp::double_t        out_result_d,
    output fpp::fpu_except_t    out_except
);

    // 1x reg in middle

    // ----------------------------------------------------------------
    // Signals:

    logic pass_reg;

    // ----------------------------------------------------------------
    // Logic:

    // control logic
    always_comb begin
        pass_reg = ~out_valid | out_ready;
        in_ready = pass_reg;
    end
    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            out_valid <= 1'b0;
            out_dest_pr <= 0;
            out_dest_rob_idx <= 0;
        end
        else if (pass_reg) begin
            out_valid <= in_valid;
            out_dest_pr <= in_dest_pr;
            out_rob_idx <= in_rob_idx;
        end
    end

    // possible exceptions
        // fp -> int
            // NV, NX

        // int -> fp
            // OF, NX

        // fp -> fp
            // NV, OF, UF, NX
            // only double -> single

endmodule
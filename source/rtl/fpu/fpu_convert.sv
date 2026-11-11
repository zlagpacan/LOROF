/*
    Filename: fpu_convert.sv
    Author: zlagpacan
    Description: FPU Conversion Instructions
    Spec: LOROF/spec/design/fpu_convert.md
*/

`include "fpp.vh"
`include "corep.vh"

module fpu_convert #(

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
    input logic [4:0]       in_funct5,
    input logic [2:0]       in_instr_rm,
    input logic [2:0]       in_fcsr_rm,

    // fp input
    input fpp::double_t     in_A_d,
    input fpp::single_t     in_A_s_boxed, // post NaN-box check

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

    // possible exceptions
        // fp -> int
            // NV, NX

        // int -> fp
            // OF, NX

        // fp -> fp
            // NV, OF, UF, NX
            // only double -> single
            // single -> double is always exact

    // ----------------------------------------------------------------
    // Signals:

    logic pass_reg;

    fpp::double_t        next_out_result_d;
    fpp::fpu_except_t    next_out_except;

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

            out_result_d <= 64'h0;
            out_except <= 5'h0;
        end
        else if (pass_reg) begin
            out_valid <= in_valid;
            out_dest_pr <= in_dest_pr;
            out_rob_idx <= in_rob_idx;

            out_result_d <= next_out_result_d;
            out_except <= next_out_except;
        end
    end

    // conversion logic
    always_comb begin

        // activate exception flags where relevant in case
        next_out_except.NV = 1'b0;
        next_out_except.DZ = 1'b0;
        next_out_except.OF = 1'b0;
        next_out_except.UF = 1'b0;
        next_out_except.NX = 1'b0;

        casez (funct7)

            7'b0100000: begin
                // double -> single
                // FCVT.S.D

                // funct5 = 5'b00001 but don't care


            end

            7'b0100001: begin
                // single -> double
                // FCVT.D.S

                // funct5 = 5'b00000 but don't care

                // TODO: special case NaN -> sNaN NV, output cNaN

                // TODO: special case inf

                // TODO: special case zero

                // TODO: special case subnormal
                
                next_out_result_d.sign = in_A_s_boxed.sign;
                next_out_result_d.exp = in_A_s_boxed.exp + 11'b011_1000_0000;
                next_out_result_d.mant = {in_A_s_boxed.mant, 29'h0};
            end

            7'b1100000: begin
                // single -> int
            end

            7'b1101000: begin
                // int -> single
            end

            7'b1100001: begin
                // double -> int
            end

            7'b1101001: begin
                // int -> double
            end

        endcase
    end

endmodule
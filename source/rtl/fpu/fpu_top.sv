/*
    Filename: fpu_top.sv
    Author: zlagpacan
    Description: Unified FPU instruction issue and result interface.
    Spec: LOROF/spec/design/fpu_top.md
*/

`include "fpp.vh"
`include "corep.vh"

module fpu_top #(

) (
    // seq
    input logic CLK,
    input logic nRST,

    // Input instruction and transaction metadata
    input logic                 in_valid,
    output logic                in_ready,
    input logic [4:0]           in_opcode5,      // instruction[6:2]
    input logic [4:0]           in_funct5_op,    // instruction[31:27]
    input logic                 in_fmt,          // instruction[25], S=0/D=1
    input logic [4:0]           in_rs2,          // instruction[24:20], conversion subtype
    input logic [2:0]           in_funct3,
    input corep::pr_t           in_dest_pr,
    input corep::rob_idx_t      in_rob_idx,
    input logic [2:0]           in_fcsr_rm,

    // Decoded operands, with single precision values already NaN-box checked
    input fpp::double_t         in_A_d,
    input fpp::single_t         in_A_s_boxed,
    input fpp::double_t         in_B_d,
    input fpp::single_t         in_B_s_boxed,
    input fpp::double_t         in_C_d,
    input fpp::single_t         in_C_s_boxed,

    // Unified result interface
    output logic                out_valid,
    input logic                 out_ready,
    output corep::pr_t          out_dest_pr,
    output corep::rob_idx_t     out_rob_idx,
    output fpp::double_t        out_result_d,
    output fpp::fpu_except_t    out_except
);

    localparam logic [1:0] ROUTE_ARITH = 2'd0;
    localparam logic [1:0] ROUTE_CONVERT = 2'd1;
    localparam logic [1:0] ROUTE_FUSE = 2'd2;
    localparam logic [1:0] ROUTE_EASY = 2'd3;

    logic [1:0] in_route;
    logic [6:0] unit_funct7;
    logic [6:0] unit_opcode7;
    logic [1:0] unit_funct2;

    logic ar_in_valid, ar_in_ready;
    logic cv_in_valid, cv_in_ready;
    logic fu_in_valid, fu_in_ready;
    logic easy_in_ready;

    logic ar_out_valid, ar_out_ready;
    logic cv_out_valid, cv_out_ready;
    logic fu_out_valid, fu_out_ready;
    logic easy_out_valid, easy_out_ready;

    corep::pr_t ar_out_dest_pr, cv_out_dest_pr, fu_out_dest_pr;
    corep::rob_idx_t ar_out_rob_idx, cv_out_rob_idx, fu_out_rob_idx;
    fpp::double_t ar_out_result_d, cv_out_result_d, fu_out_result_d;
    fpp::fpu_except_t ar_out_except, cv_out_except, fu_out_except;

    fpp::double_t easy_result_d;
    fpp::fpu_except_t easy_except;
    logic easy_valid;
    corep::pr_t easy_dest_pr;
    corep::rob_idx_t easy_rob_idx;
    fpp::double_t easy_result_reg;
    fpp::fpu_except_t easy_except_reg;

    logic [3:0] response_valid;
    logic [3:0] response_ready;
    logic [3:0] response_grant;
    corep::pr_t response_dest_pr [0:3];
    corep::rob_idx_t response_rob_idx [0:3];
    fpp::double_t response_result_d [0:3];
    fpp::fpu_except_t response_except [0:3];
    logic [1:0] rr_pointer;
    logic arb_locked;
    logic [1:0] locked_response;
    logic [1:0] selected_response;
    logic selected_response_valid;
    integer arb_offset;
    integer arb_index;

    // The incoming decode omits opcode and format bits that are fixed for the
    // supported FPU instruction set. Rebuild the existing unit fields using
    // only the bits that distinguish supported operations.
    assign unit_funct7 = {in_funct5_op, 1'b0, in_fmt};
    assign unit_opcode7 = {in_opcode5, 2'b11};
    assign unit_funct2 = {1'b0, in_fmt};

    // Route by the reduced opcode prefix and operation function bits.
    always_comb begin
        in_route = ROUTE_EASY;
        if (in_opcode5[4:2] == 3'b100) begin
            in_route = ROUTE_FUSE;
        end
        else if (in_opcode5 == 5'b10100) begin
            case (in_funct5_op)
                5'b00000, 5'b00001, 5'b00010, 5'b00011, 5'b01011:
                    in_route = ROUTE_ARITH;
                5'b01000, 5'b11000, 5'b11010:
                    in_route = ROUTE_CONVERT;
                default: in_route = ROUTE_EASY;
            endcase
        end
    end

    assign ar_in_valid = in_valid && (in_route == ROUTE_ARITH);
    assign cv_in_valid = in_valid && (in_route == ROUTE_CONVERT);
    assign fu_in_valid = in_valid && (in_route == ROUTE_FUSE);

    always_comb begin
        case (in_route)
            ROUTE_ARITH:   in_ready = ar_in_ready;
            ROUTE_CONVERT: in_ready = cv_in_ready;
            ROUTE_FUSE:    in_ready = fu_in_ready;
            default:       in_ready = easy_in_ready;
        endcase
    end

    fpu_arithmetic arithmetic_unit (
        .CLK(CLK),
        .nRST(nRST),
        .in_valid(ar_in_valid),
        .in_dest_pr(in_dest_pr),
        .in_rob_idx(in_rob_idx),
        .in_ready(ar_in_ready),
        .in_funct7(unit_funct7),
        .in_funct5(5'b0),
        .in_instr_rm(in_funct3),
        .in_fcsr_rm(in_fcsr_rm),
        .in_A_d(in_A_d),
        .in_A_s_boxed(in_A_s_boxed),
        .in_B_d(in_B_d),
        .in_B_s_boxed(in_B_s_boxed),
        .out_valid(ar_out_valid),
        .out_dest_pr(ar_out_dest_pr),
        .out_rob_idx(ar_out_rob_idx),
        .out_ready(ar_out_ready),
        .out_result_d(ar_out_result_d),
        .out_except(ar_out_except)
    );

    fpu_convert convert_unit (
        .CLK(CLK),
        .nRST(nRST),
        .in_valid(cv_in_valid),
        .in_dest_pr(in_dest_pr),
        .in_rob_idx(in_rob_idx),
        .in_ready(cv_in_ready),
        .in_funct7(unit_funct7),
        .in_funct5(in_rs2),
        .in_instr_rm(in_funct3),
        .in_fcsr_rm(in_fcsr_rm),
        .in_A_d(in_A_d),
        .in_A_s_boxed(in_A_s_boxed),
        .out_valid(cv_out_valid),
        .out_dest_pr(cv_out_dest_pr),
        .out_rob_idx(cv_out_rob_idx),
        .out_ready(cv_out_ready),
        .out_result_d(cv_out_result_d),
        .out_except(cv_out_except)
    );

    fpu_fuse fuse_unit (
        .CLK(CLK),
        .nRST(nRST),
        .in_valid(fu_in_valid),
        .in_dest_pr(in_dest_pr),
        .in_rob_idx(in_rob_idx),
        .in_ready(fu_in_ready),
        .in_opcode7(unit_opcode7),
        .in_funct2(unit_funct2),
        .in_instr_rm(in_funct3),
        .in_fcsr_rm(in_fcsr_rm),
        .in_A_d(in_A_d),
        .in_A_s_boxed(in_A_s_boxed),
        .in_B_d(in_B_d),
        .in_B_s_boxed(in_B_s_boxed),
        .in_C_d(in_C_d),
        .in_C_s_boxed(in_C_s_boxed),
        .out_valid(fu_out_valid),
        .out_dest_pr(fu_out_dest_pr),
        .out_rob_idx(fu_out_rob_idx),
        .out_ready(fu_out_ready),
        .out_result_d(fu_out_result_d),
        .out_except(fu_out_except)
    );

    fpu_easy easy_unit (
        .funct7(unit_funct7),
        .funct3(in_funct3),
        .A_d(in_A_d),
        .B_d(in_B_d),
        .A_s_boxed(in_A_s_boxed),
        .B_s_boxed(in_B_s_boxed),
        .result_d(easy_result_d),
        .except(easy_except)
    );

    assign response_valid[0] = ar_out_valid;
    assign response_valid[1] = cv_out_valid;
    assign response_valid[2] = fu_out_valid;
    assign response_valid[3] = easy_valid;

    assign response_dest_pr[0] = ar_out_dest_pr;
    assign response_dest_pr[1] = cv_out_dest_pr;
    assign response_dest_pr[2] = fu_out_dest_pr;
    assign response_dest_pr[3] = easy_dest_pr;
    assign response_rob_idx[0] = ar_out_rob_idx;
    assign response_rob_idx[1] = cv_out_rob_idx;
    assign response_rob_idx[2] = fu_out_rob_idx;
    assign response_rob_idx[3] = easy_rob_idx;
    assign response_result_d[0] = ar_out_result_d;
    assign response_result_d[1] = cv_out_result_d;
    assign response_result_d[2] = fu_out_result_d;
    assign response_result_d[3] = easy_result_reg;
    assign response_except[0] = ar_out_except;
    assign response_except[1] = cv_out_except;
    assign response_except[2] = fu_out_except;
    assign response_except[3] = easy_except_reg;

    // Rotate priority after each accepted response to prevent starvation.
    always_comb begin
        response_grant = 4'b0000;
        selected_response = rr_pointer;
        selected_response_valid = 1'b0;
        if (arb_locked) begin
            selected_response = locked_response;
            selected_response_valid = response_valid[locked_response];
            response_grant[locked_response] = selected_response_valid;
        end
        else begin
            for (arb_offset = 0; arb_offset < 4; arb_offset = arb_offset + 1) begin
                arb_index = rr_pointer + arb_offset;
                if (arb_index >= 4) arb_index = arb_index - 4;
                if (!selected_response_valid && response_valid[arb_index]) begin
                    response_grant[arb_index] = 1'b1;
                    selected_response = arb_index[1:0];
                    selected_response_valid = 1'b1;
                end
            end
        end

        out_valid = selected_response_valid;
        out_dest_pr = '0;
        out_rob_idx = '0;
        out_result_d = '0;
        out_except = '0;
        if (selected_response_valid) begin
            out_dest_pr = response_dest_pr[selected_response];
            out_rob_idx = response_rob_idx[selected_response];
            out_result_d = response_result_d[selected_response];
            out_except = response_except[selected_response];
        end

        response_ready = 4'b0000;
        if (out_ready && selected_response_valid)
            response_ready[selected_response] = 1'b1;
    end

    assign ar_out_ready = response_ready[0];
    assign cv_out_ready = response_ready[1];
    assign fu_out_ready = response_ready[2];
    assign easy_out_ready = response_ready[3];

    // fpu_easy is combinational; retain its accepted result until selected
    // by the shared response arbiter and consumed downstream.
    assign easy_in_ready = ~easy_valid || (easy_out_valid && easy_out_ready);
    assign easy_out_valid = easy_valid;

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            easy_valid <= 1'b0;
            easy_dest_pr <= '0;
            easy_rob_idx <= '0;
            easy_result_reg <= '0;
            easy_except_reg <= '0;
            rr_pointer <= 2'd0;
            arb_locked <= 1'b0;
            locked_response <= 2'd0;
        end
        else begin
            if (in_valid && in_ready && (in_route == ROUTE_EASY)) begin
                easy_valid <= 1'b1;
                easy_dest_pr <= in_dest_pr;
                easy_rob_idx <= in_rob_idx;
                easy_result_reg <= easy_result_d;
                easy_except_reg <= easy_except;
            end
            else if (easy_out_valid && easy_out_ready) begin
                easy_valid <= 1'b0;
            end

            if (out_valid && out_ready) begin
                if (selected_response == 2'd3) rr_pointer <= 2'd0;
                else rr_pointer <= selected_response + 2'd1;
                arb_locked <= 1'b0;
            end
            else if (out_valid && !arb_locked) begin
                arb_locked <= 1'b1;
                locked_response <= selected_response;
            end
        end
    end

endmodule

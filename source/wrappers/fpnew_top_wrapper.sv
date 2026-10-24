/*
    Filename: fpnew_top_wrapper.sv
    Author: zlagpacan
    Description: RTL wrapper around fpnew_top module. 
    Spec: LOROF/spec/design/fpnew_top.md
*/

`timescale 1ns/100ps

module fpnew_top_wrapper #(
	// parameter fpnew_pkg::fpu_features_t Features = fpnew_pkg::RV64D_Xsflt,
	parameter fpnew_pkg::fpu_features_t Features = fpnew_pkg::RV64D,
	// parameter fpnew_pkg::fpu_implementation_t Implementation = fpnew_pkg::DEFAULT_NOREGS,
	// parameter fpnew_pkg::fpu_implementation_t Implementation = fpnew_pkg::INSIDE_REGS,
	parameter fpnew_pkg::fpu_implementation_t Implementation = fpnew_pkg::CUSTOM_REGS,
	// parameter fpnew_pkg::fpu_implementation_t Implementation = fpnew_pkg::DEFAULT_NO_DIVSQRT,
	// parameter fpnew_pkg::fpu_implementation_t Implementation = fpnew_pkg::DEFAULT_SNITCH,
	parameter fpnew_pkg::divsqrt_unit_t DivSqrtSel = fpnew_pkg::THMULTI,
	// parameter fpnew_pkg::divsqrt_unit_t DivSqrtSel = fpnew_pkg::PULP,
	parameter type TagType = logic,
	parameter int unsigned TrueSIMDClass = 0,
	parameter int unsigned EnableSIMDMask = 0,
    // Do not change
    localparam int unsigned NumLanes     = fpnew_pkg::max_num_lanes(Features.Width, Features.FpFmtMask, Features.EnableVectors),
    localparam type         MaskType     = logic [NumLanes-1:0],
    localparam int unsigned WIDTH        = Features.Width,
    localparam int unsigned NUM_OPERANDS = 3
) (

    // seq
    input logic CLK,
    input logic nRST,
    // Input signals
	input logic [NUM_OPERANDS-1:0][WIDTH-1:0] next_operands_i,
	input fpnew_pkg::roundmode_e next_rnd_mode_i,
	input fpnew_pkg::operation_e next_op_i,
	input logic next_op_mod_i,
	input fpnew_pkg::fp_format_e next_src_fmt_i,
	input fpnew_pkg::fp_format_e next_dst_fmt_i,
	input fpnew_pkg::int_format_e next_int_fmt_i,
	input logic next_vectorial_op_i,
	input TagType next_tag_i,
	input MaskType next_simd_mask_i,
    // Input Handshake
	input logic next_in_valid_i,
	output logic last_in_ready_o,
	input logic next_flush_i,
    // Output signals
	output logic [WIDTH-1:0] last_result_o,
	output fpnew_pkg::status_t last_status_o,
	output TagType last_tag_o,
    // Output handshake
	output logic last_out_valid_o,
	input logic next_out_ready_i,
    // Indication of valid data in flight
	output logic last_busy_o,
	output logic last_early_valid_o
);

    // ----------------------------------------------------------------
    // Direct Module Connections:
    // Input signals
	logic [NUM_OPERANDS-1:0][WIDTH-1:0] operands_i;
	fpnew_pkg::roundmode_e rnd_mode_i;
	fpnew_pkg::operation_e op_i;
	logic op_mod_i;
	fpnew_pkg::fp_format_e src_fmt_i;
	fpnew_pkg::fp_format_e dst_fmt_i;
	fpnew_pkg::int_format_e int_fmt_i;
	logic vectorial_op_i;
	TagType tag_i;
	MaskType simd_mask_i;
    // Input Handshake
	logic in_valid_i;
	logic in_ready_o;
	logic flush_i;
    // Output signals
	logic [WIDTH-1:0] result_o;
	fpnew_pkg::status_t status_o;
	TagType tag_o;
    // Output handshake
	logic out_valid_o;
	logic out_ready_i;
    // Indication of valid data in flight
	logic busy_o;
	logic early_valid_o;

    // ----------------------------------------------------------------
    // Module Instantiation:

	fpnew_top #(
		.Features(Features),
		.Implementation(Implementation),
		.DivSqrtSel(DivSqrtSel),
		.TagType(TagType),
		.TrueSIMDClass(TrueSIMDClass),
		.EnableSIMDMask(EnableSIMDMask)
	) WRAPPED_MODULE (
		.clk_i(CLK),
		.rst_ni(nRST),
	    // Input signals
		.operands_i(operands_i),
		.rnd_mode_i(rnd_mode_i),
		.op_i(op_i),
		.op_mod_i(op_mod_i),
		.src_fmt_i(src_fmt_i),
		.dst_fmt_i(dst_fmt_i),
		.int_fmt_i(int_fmt_i),
		.vectorial_op_i(vectorial_op_i),
		.tag_i(tag_i),
		.simd_mask_i(simd_mask_i),
	    // Input Handshake
		.in_valid_i(in_valid_i),
		.in_ready_o(in_ready_o),
		.flush_i(flush_i),
	    // Output signals
		.result_o(result_o),
		.status_o(status_o),
		.tag_o(tag_o),
	    // Output handshake
		.out_valid_o(out_valid_o),
		.out_ready_i(out_ready_i),
	    // Indication of valid data in flight
		.busy_o(busy_o),
		.early_valid_o(early_valid_o)
	);

    // ----------------------------------------------------------------
    // Wrapper Registers:

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            // Input signals
            operands_i <= '0;
            rnd_mode_i <= fpnew_pkg::roundmode_e'(0);
            op_i <= fpnew_pkg::operation_e'(0);
            op_mod_i <= '0;
            src_fmt_i <= fpnew_pkg::fp_format_e'(0);
            dst_fmt_i <= fpnew_pkg::fp_format_e'(0);
            int_fmt_i <= fpnew_pkg::int_format_e'(0);
            vectorial_op_i <= '0;
            tag_i <= '0;
            simd_mask_i <= '0;
            // Input Handshake
            in_valid_i <= '0;
            last_in_ready_o <= '0;
            flush_i <= '0;
            // Output signals
            last_result_o <= '0;
            last_status_o <= '0;
            last_tag_o <= '0;
            // Output handshake
            last_out_valid_o <= '0;
            out_ready_i <= '0;
            // Indication of valid data in flight
            last_busy_o <= '0;
            last_early_valid_o <= '0;
        end
        else begin
		    // Input signals
			operands_i <= next_operands_i;
			rnd_mode_i <= next_rnd_mode_i;
			op_i <= next_op_i;
			op_mod_i <= next_op_mod_i;
			src_fmt_i <= next_src_fmt_i;
			dst_fmt_i <= next_dst_fmt_i;
			int_fmt_i <= next_int_fmt_i;
			vectorial_op_i <= next_vectorial_op_i;
			tag_i <= next_tag_i;
			simd_mask_i <= next_simd_mask_i;
		    // Input Handshake
			in_valid_i <= next_in_valid_i;
			last_in_ready_o <= in_ready_o;
			flush_i <= next_flush_i;
		    // Output signals
			last_result_o <= result_o;
			last_status_o <= status_o;
			last_tag_o <= tag_o;
		    // Output handshake
			last_out_valid_o <= out_valid_o;
			out_ready_i <= next_out_ready_i;
		    // Indication of valid data in flight
			last_busy_o <= busy_o;
			last_early_valid_o <= early_valid_o;
        end
    end

endmodule
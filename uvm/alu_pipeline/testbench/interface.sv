/*
    Module   : alu_pipeline
    Filename : interface.sv
    Author   : Adam Keith
*/

`ifndef ALU_PIPELINE_IF_SV
`define ALU_PIPELINE_IF_SV

// --- Dependencies --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;

// --- ALU Pipeline Interface --- //
interface alu_pipeline_if (input CLK);

    // --- Sequence --- //    
    logic                            nRST;

    // --- OP Issue From IQ --- //
    logic                             valid_in;
    logic [3:0]                       op_in;
    logic                             is_imm_in;
    logic [31:0]                      imm_in;
    logic                             A_unneeded_in;
    logic                             A_forward_in;
    logic [LOG_PRF_BANK_COUNT-1:0]    A_bank_in;
    logic                             B_forward_in;
    logic [LOG_PRF_BANK_COUNT-1:0]    B_bank_in;
    logic [LOG_PR_COUNT-1:0]          dest_PR_in;

    // --- PRF --- //
    logic                             A_reg_read_valid_in;
    logic                             B_reg_read_valid_in;
    logic [PRF_BANK_COUNT-1:0][31:0]  reg_read_data_by_bank_in;

    // --- Forward PRF --- //
    logic [PRF_BANK_COUNT-1:0][31:0]  forward_data_by_bank_in;

    // --- Ready -> IQ --- //
    logic                            ready_out;

    // --- PRF Writeback --- //
    logic                            WB_valid_out;
    logic [31:0]                     WB_data_out;
    logic [LOG_PR_COUNT-1:0]         WB_PR_out;

    // --- DUT Modport --- //
    modport mp_dut (
        // --- Inputs --- //
        input  logic nRST,
        input  logic valid_in,
        input  logic op_in,
        input  logic imm_in,
        input  logic is_imm_in,
        input  logic A_forward_in,
        input  logic A_unneeded_in,
        input  logic B_forward_in,
        input  logic A_bank_in,
        input  logic B_forward_in,
        input  logic B_bank_in,
        input  logic dest_PR_in,
        input  logic B_bank_in,
        input  logic B_reg_read_valid_in,
        input  logic A_reg_read_valid_in,
        input  logic forward_data_by_bank_in,
        input  logic reg_read_data_by_bank_in,

        // --- Outputs --- //
        output logic ready_out,
        output logic WB_valid_out,
        output logic WB_data_out,
        output logic WB_PR_out
    );

    modport mp_uvm (
        // --- Inputs --- //
        input  logic ready_out,
        input  logic WB_valid_out,
        input  logic WB_data_out,
        input  logic WB_PR_out
        
        // --- Outputs --- //
        output logic valid_in,
        output logic op_in,
        output logic imm_in,
        output logic is_imm_in,
        output logic A_forward_in,
        output logic A_unneeded_in,
        output logic B_forward_in,
        output logic A_bank_in,
        output logic B_forward_in,
        output logic B_bank_in,
        output logic dest_PR_in,
        output logic B_bank_in,
        output logic B_reg_read_valid_in,
        output logic A_reg_read_valid_in,
        output logic forward_data_by_bank_in,
        output logic reg_read_data_by_bank_in,
    );

endinterface : alu_pipeline_if

`endif
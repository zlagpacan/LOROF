/*
  Module        : alu_reg_mdu_iq
  UMV Component : interface
  Author        : 
*/

`ifndef ALU_REG_MDU_IQ_INTERFACE_SV
`define ALU_REG_MDU_IQ_INTERFACE_SV

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //

// --- Interface --- //
interface alu_reg_mdu_iq_if (input logic CLK);

  // --- Reset --- //
  logic nRST;

  // --- Inputs --- //
  logic [3:0]                                                     dispatch_attempt_by_way;
  logic [3:0]                                                     dispatch_valid_alu_reg_by_way;
  logic [3:0]                                                     dispatch_valid_mdu_by_way;
  logic [3:0][3:0]                                                dispatch_op_by_way;
  logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_A_PR_by_way;
  logic [3:0]                                                     dispatch_A_ready_by_way;
  logic [3:0]                                                     dispatch_A_is_zero_by_way;
  logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_B_PR_by_way;
  logic [3:0]                                                     dispatch_B_ready_by_way;
  logic [3:0]                                                     dispatch_B_is_zero_by_way;
  logic [3:0][LOG_PR_COUNT-1:0]                                   dispatch_dest_PR_by_way;
  logic [3:0][LOG_ROB_ENTRIES-1:0]                                dispatch_ROB_index_by_way;
  logic                                                           alu_reg_pipeline_ready;
  logic                                                           mdu_pipeline_ready;
  logic [PRF_BANK_COUNT-1:0]                                      WB_bus_valid_by_bank;
  logic [PRF_BANK_COUNT-1:0][LOG_PR_COUNT-LOG_PRF_BANK_COUNT-1:0] WB_bus_upper_PR_by_bank;
  
  // --- Outputs --- // 29 
  logic [3:0]                                                     dispatch_ack_by_way;
  logic                                                           issue_alu_reg_valid;
  logic [3:0]                                                     issue_alu_reg_op;
  logic                                                           issue_alu_reg_A_forward;
  logic                                                           issue_alu_reg_A_is_zero;
  logic [LOG_PRF_BANK_COUNT-1:0]                                  issue_alu_reg_A_bank;
  logic                                                           issue_alu_reg_B_forward;
  logic                                                           issue_alu_reg_B_is_zero;
  logic [LOG_PRF_BANK_COUNT-1:0]                                  issue_alu_reg_B_bank;
  logic [LOG_PR_COUNT-1:0]                                        issue_alu_reg_dest_PR;
  logic [LOG_ROB_ENTRIES-1:0]                                     issue_alu_reg_ROB_index;
  logic                                                           PRF_alu_reg_req_A_valid;
  logic [LOG_PR_COUNT-1:0]                                        PRF_alu_reg_req_A_PR;
  logic                                                           PRF_alu_reg_req_B_valid;
  logic [LOG_PR_COUNT-1:0]                                        PRF_alu_reg_req_B_PR;
  logic                                                           issue_mdu_valid;
  logic [3:0]                                                     issue_mdu_op;
  logic                                                           issue_mdu_A_forward;
  logic                                                           issue_mdu_A_is_zero;
  logic [LOG_PRF_BANK_COUNT-1:0]                                  issue_mdu_A_bank;
  logic                                                           issue_mdu_B_forward;
  logic                                                           issue_mdu_B_is_zero;
  logic [LOG_PRF_BANK_COUNT-1:0]                                  issue_mdu_B_bank;
  logic [LOG_PR_COUNT-1:0]                                        issue_mdu_dest_PR;
  logic [LOG_ROB_ENTRIES-1:0]                                     issue_mdu_ROB_index;
  logic                                                           PRF_mdu_req_A_valid;
  logic [LOG_PR_COUNT-1:0]                                        PRF_mdu_req_A_PR;
  logic                                                           PRF_mdu_req_B_valid;
  logic [LOG_PR_COUNT-1:0]                                        PRF_mdu_req_B_PR;
  
endinterface : alu_reg_mdu_iq_if

`endif
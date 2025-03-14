/*
  Module        : alu_imm_pipeline
  UMV Component : scoreboard
  Author        : Adam Keith
*/

`ifndef ALU_IMM_PIPELINE_PREDICTOR_SV
`define ALU_IMM_PIPELINE_PREDICTOR_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
class alu_imm_pipeline_predictor extends uvm_subscriber#(alu_imm_pipeline_sequence_item); 
    `uvm_component_utils(alu_imm_pipeline_predictor)

    uvm_analysis_port#(alu_imm_pipeline_sequence_item) pred_ap;
    alu_imm_pipeline_sequence_item expected_tx;
    alu_imm_pipeline_sequence_item past_tx; // Store the previous transaction

    // --- //
    // Internal registers to simulate the 3-cycle delay prediction
    reg [31:0] stage1_imm;
    reg [31:0] stage2_A, stage2_imm;
    reg [31:0] stage3_A, stage3_imm;
    reg [31:0] stage4_A, stage4_imm;
    reg [3:0]  stage1_op, stage2_op, stage3_op, stage4_op;
    reg [LOG_PRF_BANK_COUNT-1:0] stage1_A_bank;

    function new(string name = "alu_imm_pipeline_predictor", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        pred_ap = new("pred_ap", this);
    endfunction : build_phase

    // Function to perform the prediction calculation
    function automatic [31:0] predict_WB_data(input [3:0] op, input [31:0] A, input [31:0] imm);
        case (op)
            4'b0000: predict_WB_data = A + imm;  // ADDI
            // Add other operations here as needed
            default: predict_WB_data = 32'b0;
        endcase
    endfunction

    function void write(alu_imm_pipeline_sequence_item t);
        if (expected_tx == null) begin
            expected_tx = alu_imm_pipeline_sequence_item::type_id::create("expected_tx");
        end
        expected_tx.copy(t);

        if (t.nRST == 1'b0) begin
            expected_tx.issue_ready  = '1;
            expected_tx.WB_valid     = '0;
            expected_tx.WB_data      = '0;
            expected_tx.WB_PR        = '0;
            expected_tx.WB_ROB_index = '0;
        end 
        else begin
            // stage1_A_bank <= t.issue_A_bank;
            // stage1_A_bank   <= t.forward_data_by_bank[t.issue_A_bank];
            // stage1_imm <= {{20{t.issue_imm12[11]}}, t.issue_imm12};
            // stage1_op  <= t.issue_op;

            // stage2_A   <= t.forward_data_by_bank[stage1_A_bank];
            // stage2_imm <= stage1_imm;
            // stage2_op  <= stage1_op;

            // FIXME: going once cycle too early
            if (t.WB_ready) begin
                stage1_A_bank   <= t.forward_data_by_bank[t.issue_A_bank];
                stage1_imm <= {{20{t.issue_imm12[11]}}, t.issue_imm12};
                stage1_op  <= t.issue_op;
                expected_tx.WB_data = stage1_A_bank | stage1_imm;
            end else begin

            end

            // stage3_A   <= stage2_A;
            // stage3_imm <= stage2_imm;
            // stage3_op  <= stage2_op;

            // stage4_A   <= stage3_A;
            // stage4_imm <= stage3_imm;
            // stage4_op  <= stage3_op;

            // expected_tx.WB_data = predict_WB_data(stage2_op, stage2_A, stage2_imm);
            // expected_tx.WB_PR   = t.issue_dest_PR;
            // expected_tx.WB_ROB_index = t.issue_ROB_index;
            // expected_tx.WB_valid = 1'b1;
        end

        pred_ap.write(expected_tx);
    endfunction : write

endclass

`endif
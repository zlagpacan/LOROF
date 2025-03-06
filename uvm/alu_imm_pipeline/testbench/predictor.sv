`ifndef ALU_IMM_PIPELINE_PRED_SV
`define ALU_IMM_PIPELINE_PRED_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Includes --- //
`include "sequence_item.sv"

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Predictor --- //
class alu_imm_pipeline_predictor extends uvm_subscriber#(alu_imm_pipeline_sequence_item); 
    `uvm_component_utils(alu_imm_pipeline_predictor)

    uvm_analysis_port#(alu_imm_pipeline_sequence_item) pred_ap;
    alu_imm_pipeline_sequence_item expected_tx;

    function new(string name = "alu_imm_pipeline_predictor", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        pred_ap = new("pred_ap", this);
    endfunction : build_phase

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
            pred_ap.write(expected_tx);
        end

        // end else begin
        //     // TODO:
        //     expected_tx.issue_ready  = 'x;
        //     expected_tx.WB_valid     = 'x;
        //     expected_tx.WB_data      = 'x;
        //     expected_tx.WB_PR        = 'x;
        //     expected_tx.WB_ROB_index = 'x;
        // end

        // `uvm_info(get_type_name(), $sformatf("Predicted TX: %s", expected_tx.sprint()), UVM_MEDIUM)

        // pred_ap.write(expected_tx);
    endfunction : write
    
endclass

`endif

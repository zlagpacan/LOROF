/*
  Module        : alu_reg_mdu_iq
  UMV Component : predictor
  Author        : 
*/

`ifndef ALU_REG_MDU_IQ_PREDICTOR_SV
`define ALU_REG_MDU_IQ_PREDICTOR_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"

class alu_reg_mdu_iq_predictor extends uvm_subscriber#(alu_reg_mdu_iq_sequence_item); 
    `uvm_component_utils(alu_reg_mdu_iq_predictor)
    uvm_analysis_port#(alu_reg_mdu_iq_sequence_item) pred_ap;
    alu_reg_mdu_iq_sequence_item output_tx;

    function new(string name = "alu_reg_mdu_iq_predictor", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        pred_ap = new("pred_ap", this);
    endfunction

    function void write(alu_reg_mdu_iq_sequence_item t);
        output_tx = alu_reg_mdu_iq_sequence_item::type_id::create("output_tx");
        output_tx.copy(t);

        // If Reset 
        if(output_tx.nRST == 1'b0) begin
            output_tx.dispatch_ack_by_way = '0;  
            output_tx.issue_alu_reg_valid = '0;
            output_tx.issue_alu_reg_op = '0;
            output_tx.issue_alu_reg_A_forward = '0;
            output_tx.issue_alu_reg_A_bank = '0;
            output_tx.issue_alu_reg_B_forward = '0;
            output_tx.issue_alu_reg_B_bank = '0;
            output_tx.issue_alu_reg_dest_PR = '0;
            output_tx.issue_alu_reg_ROB_index = '0;
            output_tx.PRF_alu_reg_req_A_valid = '0;
            output_tx.PRF_alu_reg_req_A_PR = '0;
            output_tx.PRF_alu_reg_req_B_valid = '0;
            output_tx.PRF_alu_reg_req_B_PR = '0;
            output_tx.issue_mdu_valid = '0;
            output_tx.issue_mdu_op = '0;
            output_tx.issue_mdu_A_forward = '0;
            output_tx.issue_mdu_A_bank = '0;
            output_tx.issue_mdu_B_forward = '0;
            output_tx.issue_mdu_B_bank = '0;
            output_tx.issue_mdu_dest_PR = '0;
            output_tx.issue_mdu_ROB_index = '0;
            output_tx.PRF_mdu_req_A_valid = '0;
            output_tx.PRF_mdu_req_A_PR = '0;
            output_tx.PRF_mdu_req_B_valid = '0;
            output_tx.PRF_mdu_req_B_PR = '0;
        end

        // else begin

        // end
        
        // --- Write to SB --- //
        pred_ap.write(output_tx);
    endfunction
endclass

`endif
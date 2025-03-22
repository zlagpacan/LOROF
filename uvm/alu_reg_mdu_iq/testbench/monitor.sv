/*
  Module        : alu_reg_mdu_iq
  UMV Component : monitor
  Author        : 
*/

`ifndef ALU_REG_MDU_IQ_MONITOR_SV
`define ALU_REG_MDU_IQ_MONITOR_SV

// --- UVM --- //
`include "uvm_macros.svh"
import uvm_pkg::*;

// --- Packages --- //
`include "core_types_pkg.vh"
import core_types_pkg::*;
    
// --- Includes --- //
`include "sequence_item.sv"
`include "interface.sv"

// --- Monitor --- //
class alu_reg_mdu_iq_monitor extends uvm_monitor;
  `uvm_component_utils(alu_reg_mdu_iq_monitor)
  
  // --- Monitor Components --- //
  virtual alu_reg_mdu_iq_if vif;
  alu_reg_mdu_iq_sequence_item item;
  
  uvm_analysis_port #(alu_reg_mdu_iq_sequence_item) monitor_port;
  uvm_analysis_port #(alu_reg_mdu_iq_sequence_item) predictor_port;
  
  // --- Constructor --- //
  function new(string name = "alu_reg_mdu_iq_monitor", uvm_component parent);
    super.new(name, parent);
    `uvm_info("MONITOR_CLASS", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("MONITOR_CLASS", "Build Phase", UVM_HIGH)
    
    // --- Build Monitor Port --- //
    monitor_port = new("monitor_port", this);
    // --- Build Monitor Port --- //
    predictor_port = new("predictor_port",this);
    
    // --- Virtual Interface Failure --- //
    if(!(uvm_config_db #(virtual alu_reg_mdu_iq_if)::get(this, "*", "vif", vif))) begin
      `uvm_error("MONITOR_CLASS", "Failed to get virtual interface")
    end
    
  endfunction : build_phase
  
  // --- Connect Phase --- //
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("MONITOR_CLASS", "Connect Phase", UVM_HIGH)
    
  endfunction : connect_phase
  
  // --- Run Phase --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("MONITOR_CLASS", "Run Phase", UVM_HIGH)
    
    wait(vif.nRST != 0 || vif.nRST != 1)
    // --- Capture DUT Interface --- //
    forever begin
      item = alu_reg_mdu_iq_sequence_item::type_id::create("item");
      
      // wait(vif.nRST); // SENDING RST TO SB

      // --- Input Sample --- //
      item.nRST                          = vif.nRST;

      // @(posedge vif.CLK);
      item.dispatch_attempt_by_way       = vif.dispatch_attempt_by_way;
      item.dispatch_valid_alu_reg_by_way = vif.dispatch_valid_alu_reg_by_way;
      item.dispatch_valid_mdu_by_way     = vif.dispatch_valid_mdu_by_way;
      item.dispatch_op_by_way            = vif.dispatch_op_by_way;
      item.dispatch_A_PR_by_way          = vif.dispatch_A_PR_by_way;
      item.dispatch_A_ready_by_way       = vif.dispatch_A_ready_by_way;
      item.dispatch_A_is_zero_by_way     = vif.dispatch_A_is_zero_by_way;
      item.dispatch_B_PR_by_way          = vif.dispatch_B_PR_by_way;
      item.dispatch_B_ready_by_way       = vif.dispatch_B_ready_by_way;
      item.dispatch_B_is_zero_by_way     = vif.dispatch_B_is_zero_by_way;
      item.dispatch_dest_PR_by_way       = vif.dispatch_dest_PR_by_way;
      item.dispatch_ROB_index_by_way     = vif.dispatch_ROB_index_by_way;
      item.alu_reg_pipeline_ready        = vif.alu_reg_pipeline_ready;
      item.mdu_pipeline_ready            = vif.mdu_pipeline_ready;
      item.WB_bus_valid_by_bank          = vif.WB_bus_valid_by_bank;
      item.WB_bus_upper_PR_by_bank       = vif.WB_bus_upper_PR_by_bank;

      // $display("MONITOR TO PREDICTO dispatch_op_by_way[0] == %d, at time %t",item.dispatch_op_by_way[0],$time);

      // Write Item to Predictor // 
      // if(item.nRST == 0) begin 
      predictor_port.write(item);
      //   // $display("MONITOR TO PREDICTO nRST == %d, at time %t",item.nRST,$time);
      // end
      
      // --- Output Sample --- //
      @(posedge vif.CLK);
      item.dispatch_ack_by_way           = vif.dispatch_ack_by_way;
      item.issue_alu_reg_valid           = vif.issue_alu_reg_valid;
      item.issue_alu_reg_op              = vif.issue_alu_reg_op;
      item.issue_alu_reg_A_forward       = vif.issue_alu_reg_A_forward;
      item.issue_alu_reg_A_is_zero       = vif.issue_alu_reg_A_is_zero;
      item.issue_alu_reg_A_bank          = vif.issue_alu_reg_A_bank;
      item.issue_alu_reg_B_forward       = vif.issue_alu_reg_B_forward;
      item.issue_alu_reg_B_is_zero       = vif.issue_alu_reg_B_is_zero;
      item.issue_alu_reg_B_bank          = vif.issue_alu_reg_B_bank;
      item.issue_alu_reg_dest_PR         = vif.issue_alu_reg_dest_PR;
      item.issue_alu_reg_ROB_index       = vif.issue_alu_reg_ROB_index;
      item.PRF_alu_reg_req_A_valid       = vif.PRF_alu_reg_req_A_valid;
      item.PRF_alu_reg_req_A_PR          = vif.PRF_alu_reg_req_A_PR;
      item.PRF_alu_reg_req_B_valid       = vif.PRF_alu_reg_req_B_valid;
      item.PRF_alu_reg_req_B_PR          = vif.PRF_alu_reg_req_B_PR;
      item.issue_mdu_valid               = vif.issue_mdu_valid;
      item.issue_mdu_op                  = vif.issue_mdu_op;
      item.issue_mdu_A_forward           = vif.issue_mdu_A_forward;
      item.issue_mdu_A_is_zero           = vif.issue_mdu_A_is_zero;
      item.issue_mdu_A_bank              = vif.issue_mdu_A_bank;
      item.issue_mdu_B_forward           = vif.issue_mdu_B_forward;
      item.issue_mdu_B_is_zero           = vif.issue_mdu_B_is_zero;
      item.issue_mdu_B_bank              = vif.issue_mdu_B_bank;
      item.issue_mdu_dest_PR             = vif.issue_mdu_dest_PR;
      item.issue_mdu_ROB_index           = vif.issue_mdu_ROB_index;
      item.PRF_mdu_req_A_valid           = vif.PRF_mdu_req_A_valid;
      item.PRF_mdu_req_A_PR              = vif.PRF_mdu_req_A_PR;
      item.PRF_mdu_req_B_valid           = vif.PRF_mdu_req_B_valid;
      item.PRF_mdu_req_B_PR              = vif.PRF_mdu_req_B_PR;
      
      // --- Send to Scoreboard --- //
      // $display("MONITOR TO SCORE dispatch_op_by_way[0] == %d, at time %t",item.dispatch_op_by_way[0],$time);
      // if(item.nRST == 0) begin
        // $display("MONITOR TO SCORE nRST == %d, at time %t",item.nRST,$time);
      // item.print_transaction("item");
      monitor_port.write(item);
      // end
      
    end
        
  endtask : run_phase
  
endclass : alu_reg_mdu_iq_monitor

`endif
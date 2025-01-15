// --- Reset Packet --- //
class alu_sequence extends uvm_sequence;
  `uvm_object_utils(alu_sequence)
  
  alu_sequence_item reset_pkt;
  
  // --- Constructor --- //
  function new(string name= "alu_sequence");
    super.new(name);
    `uvm_info("BASE_SEQ", "Inside Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Body Task --- //
  task body();
    `uvm_info("BASE_SEQ", "Inside body task", UVM_HIGH)
    
    // --- Randomize With Reset --- //
    reset_pkt = alu_sequence_item::type_id::create("reset_pkt");
    start_item(reset_pkt);
    reset_pkt.randomize() with {n_rst==0;};
    finish_item(reset_pkt);
        
  endtask : body
  
endclass : alu_sequence
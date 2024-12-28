class alu_pipeline_test extends uvm_test;
  `uvm_component_utils(alu_pipeline_test)

  // --- Test Components --- //
  alu_pipeline_env         env;
  alu_pipeline_garbage_seq garbage_seq;
  alu_pipeline_rst_seq     rst_seq;

  // --- Clocking --- //
  parameter CLK_PERIOD = 4;

  // --- Constructor --- //
  function new (string name = "alu_pipeline_test", uvm_component parent);
    super.new(name, parent);
    `uvm_info("alu_pipeline_test", "Constructor", UVM_HIGH)
  endfunction : new
  
  // --- Build Phase --- //
  function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("alu_pipeline_test", "Build Phase", UVM_HIGH)

    // --- Build Environment --- //
    env = alu_pipeline_env::type_id::create("env", this);

  endfunction : build_phase

  // --- Connect Phase --- //
  function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("alu_pipeline_test", "Connect Phase", UVM_HIGH)

  endfunction : connect_phase

  // --- Test Procedure --- //
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("alu_pipeline_test", "Run Phase", UVM_HIGH)

    phase.raise_objection(this);

    // --- Garbage Sequence - Prime DUT For Realistic Reset --- //
    repeat (4 * CLK_PERIOD) begin
        bogus_pkt = alu_pipeline_garbage_seq::type_id::create("bogus_pkt");
        bogus_pkt.start(env.alu_pipeline_agnt.alu_pipeline_sqr);
        #(2 * CLK_PERIOD);
    end

    // --- Reset Sequence --- //

    phase.drop_objection(this);

  endtask : run_phase

endclass : alu_pipeline_test
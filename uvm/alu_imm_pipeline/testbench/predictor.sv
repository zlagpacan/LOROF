// Add past values as class members
class alu_imm_pipeline_predictor extends uvm_subscriber#(alu_imm_pipeline_sequence_item); 
    `uvm_component_utils(alu_imm_pipeline_predictor)

    uvm_analysis_port#(alu_imm_pipeline_sequence_item) pred_ap;
    alu_imm_pipeline_sequence_item expected_tx;
    alu_imm_pipeline_sequence_item past_tx; // Store the previous transaction

    function new(string name = "alu_imm_pipeline_predictor", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        pred_ap = new("pred_ap", this);
        past_tx = alu_imm_pipeline_sequence_item::type_id::create("past_tx");
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
        end 
        else begin
            if (t.WB_ready == 1'b0) begin
                expected_tx.WB_valid     = past_tx.WB_valid;
                expected_tx.WB_data      = past_tx.WB_data;
                expected_tx.WB_PR        = past_tx.WB_PR;
                expected_tx.WB_ROB_index = past_tx.WB_ROB_index;
            end
        end

        // Store the current transaction as the past transaction for the next cycle
        past_tx.copy(t);

        pred_ap.write(expected_tx);
    endfunction : write

endclass

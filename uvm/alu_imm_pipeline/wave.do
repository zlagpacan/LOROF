onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /top/alu_imm_pipeline_intf/CLK
add wave -noupdate /top/alu_imm_pipeline_intf/nRST
add wave -noupdate /top/alu_imm_pipeline_intf/issue_valid
add wave -noupdate /top/alu_imm_pipeline_intf/issue_op
add wave -noupdate /top/alu_imm_pipeline_intf/issue_imm12
add wave -noupdate /top/alu_imm_pipeline_intf/issue_A_forward
add wave -noupdate /top/alu_imm_pipeline_intf/issue_A_is_zero
add wave -noupdate /top/alu_imm_pipeline_intf/issue_A_bank
add wave -noupdate /top/alu_imm_pipeline_intf/issue_dest_PR
add wave -noupdate /top/alu_imm_pipeline_intf/issue_ROB_index
add wave -noupdate /top/alu_imm_pipeline_intf/A_reg_read_ack
add wave -noupdate /top/alu_imm_pipeline_intf/A_reg_read_port
add wave -noupdate /top/alu_imm_pipeline_intf/reg_read_data_by_bank_by_port
add wave -noupdate /top/alu_imm_pipeline_intf/forward_data_by_bank
add wave -noupdate /top/alu_imm_pipeline_intf/WB_ready
add wave -noupdate /top/alu_imm_pipeline_intf/issue_ready
add wave -noupdate /top/alu_imm_pipeline_intf/WB_valid
add wave -noupdate /top/alu_imm_pipeline_intf/WB_data
add wave -noupdate /top/alu_imm_pipeline_intf/WB_PR
add wave -noupdate /top/alu_imm_pipeline_intf/WB_ROB_index
when -create sim:/uvm_test_top/alu_imm_pipeline_scoreboard/expected_tx \
    add wave -r sim:/uvm_test_top/alu_imm_pipeline_scoreboard/expected_tx
when -create sim:/uvm_test_top/alu_imm_pipeline_scoreboard/actual_tx \
    add wave -r sim:/uvm_test_top/alu_imm_pipeline_scoreboard/actual_tx
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {7 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {59 ns}

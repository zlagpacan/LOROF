onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {alu_imm_pipeline tb}
add wave -noupdate -color {Medium Spring Green} -label CLK /top/alu_imm_pipeline_intf/CLK
add wave -noupdate -color Gold -label nRST /top/alu_imm_pipeline_intf/nRST
add wave -noupdate -divider {DUT Inputs}
add wave -noupdate -expand -group {Issue API} -color {Medium Spring Green} -label issue_valid /top/alu_imm_pipeline_intf/issue_valid
add wave -noupdate -expand -group {Issue API} -color {Medium Spring Green} -label issue_op /top/alu_imm_pipeline_intf/issue_op
add wave -noupdate -expand -group {Issue API} -color {Medium Spring Green} -label issue_imm12 /top/alu_imm_pipeline_intf/issue_imm12
add wave -noupdate -expand -group {Issue API} -color {Medium Spring Green} -label issue_A_forward /top/alu_imm_pipeline_intf/issue_A_forward
add wave -noupdate -expand -group {Issue API} -color {Medium Spring Green} -label issue_A_is_zero /top/alu_imm_pipeline_intf/issue_A_is_zero
add wave -noupdate -expand -group {Issue API} -color {Medium Spring Green} -label issue_A_bank /top/alu_imm_pipeline_intf/issue_A_bank
add wave -noupdate -expand -group {Issue API} -color {Light Steel Blue} -label issue_dest_PR /top/alu_imm_pipeline_intf/issue_dest_PR
add wave -noupdate -expand -group {Issue API} -color Violet -label issue_ROB_index /top/alu_imm_pipeline_intf/issue_ROB_index
add wave -noupdate -expand -group {PRF API} -color {Medium Spring Green} -label A_reg_read_ack /top/alu_imm_pipeline_intf/A_reg_read_ack
add wave -noupdate -expand -group {PRF API} -color {Medium Spring Green} -label A_reg_read_port /top/alu_imm_pipeline_intf/A_reg_read_port
add wave -noupdate -expand -group {PRF API} -color Wheat -label reg_read_data_by_bank_by_port /top/alu_imm_pipeline_intf/reg_read_data_by_bank_by_port
add wave -noupdate -expand -group {PRF API} -color Wheat -label forward_data_by_bank /top/alu_imm_pipeline_intf/forward_data_by_bank
add wave -noupdate -expand -group {WB API} -color {Medium Spring Green} -label WB_ready /top/alu_imm_pipeline_intf/WB_ready
add wave -noupdate -divider {DUT Outputs}
add wave -noupdate -expand -group {Issue Outputs} -color Violet -label issue_ready /top/alu_imm_pipeline_intf/issue_ready
add wave -noupdate -expand -group {WB Outputs} -color Violet -label WB_valid /top/alu_imm_pipeline_intf/WB_valid
add wave -noupdate -expand -group {WB Outputs} -label WB_data /top/alu_imm_pipeline_intf/WB_data
add wave -noupdate -expand -group {WB Outputs} -color {Light Steel Blue} -label WB_PR /top/alu_imm_pipeline_intf/WB_PR
add wave -noupdate -expand -group {WB Outputs} -color Violet -label WB_ROB_index /top/alu_imm_pipeline_intf/WB_ROB_index
add wave -noupdate -divider SVA
add wave -noupdate -expand -group {WB Stall} -color White -label a_tc_WB_valid_stall /top/SVA/a_tc_WB_valid_stall
add wave -noupdate -expand -group {WB Stall} -color White -label a_tc_WB_data_stall /top/SVA/a_tc_WB_data_stall
add wave -noupdate -expand -group {WB Stall} -color White -label a_tc_WB_PR_stall /top/SVA/a_tc_WB_PR_stall
add wave -noupdate -expand -group {WB Stall} -color White -label a_tc_WB_ROB_index_stall /top/SVA/a_tc_WB_ROB_index_stall
add wave -noupdate -divider {Test Case Tracking}
add wave -noupdate -color White -label test_case /top/test.tc_name
add wave -noupdate -color White -label failures -radix decimal /top/test.env.scb.m_mismatches
add wave -noupdate -divider {Sequence Utilization}
add wave -noupdate -expand -group Sequences -color Salmon -label reset_seq /top/test.reset_seq
add wave -noupdate -expand -group Sequences -color Salmon -label garbage_seq /top/test.garbage_seq
add wave -noupdate -expand -group Sequences -color Salmon -label wb_stall_seq /top/test.wb_stall_seq
add wave -noupdate -expand -group Sequences -color Salmon -label ideal_seq /top/test.ideal_seq
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {70 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 313
configure wave -valuecolwidth 98
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
WaveRestoreZoom {0 ns} {156 ns}

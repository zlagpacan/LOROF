onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /top/alu_reg_mdu_iq_intf/CLK
add wave -noupdate /top/alu_reg_mdu_iq_intf/nRST
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_attempt_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_valid_alu_reg_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_valid_mdu_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_op_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_A_PR_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_A_ready_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_B_PR_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_B_ready_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_dest_PR_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_ROB_index_by_way
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/alu_reg_pipeline_ready
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/mdu_pipeline_ready
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/WB_bus_valid_by_bank
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/WB_bus_upper_PR_by_bank
add wave -noupdate -expand -group Inputs /top/alu_reg_mdu_iq_intf/dispatch_ack_by_way
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_alu_reg_valid
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_alu_reg_op
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_alu_reg_A_forward
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_alu_reg_A_bank
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_alu_reg_B_forward
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_alu_reg_B_bank
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_alu_reg_dest_PR
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_alu_reg_ROB_index
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/PRF_alu_reg_req_A_valid
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/PRF_alu_reg_req_A_PR
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/PRF_alu_reg_req_B_valid
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/PRF_alu_reg_req_B_PR
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_mdu_valid
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_mdu_op
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_mdu_A_forward
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_mdu_A_bank
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_mdu_B_forward
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_mdu_B_bank
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_mdu_dest_PR
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/issue_mdu_ROB_index
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/PRF_mdu_req_A_valid
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/PRF_mdu_req_A_PR
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/PRF_mdu_req_B_valid
add wave -noupdate -expand -group outputs /top/alu_reg_mdu_iq_intf/PRF_mdu_req_B_PR
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {20 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 187
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
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
WaveRestoreZoom {0 ns} {42 ns}

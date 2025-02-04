onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {Timing - Control}
add wave -noupdate -expand -group Timing -color {Spring Green} /top/DUT/CLK
add wave -noupdate -expand -group Timing -color Coral /top/DUT/nRST
add wave -noupdate -divider {Issue Queue Interface}
add wave -noupdate -divider Inputs
add wave -noupdate -expand -group {IQ Inputs} -color {Spring Green} /top/DUT/issue_valid
add wave -noupdate -expand -group {IQ Inputs} -color {Spring Green} /top/DUT/issue_op
add wave -noupdate -expand -group {IQ Inputs} -color Orange /top/DUT/issue_A_forward
add wave -noupdate -expand -group {IQ Inputs} -color Orange /top/DUT/issue_A_bank
add wave -noupdate -expand -group {IQ Inputs} -color {Cornflower Blue} /top/DUT/issue_B_forward
add wave -noupdate -expand -group {IQ Inputs} -color {Cornflower Blue} /top/DUT/issue_B_bank
add wave -noupdate -expand -group {IQ Inputs} -color {Spring Green} /top/DUT/issue_dest_PR
add wave -noupdate -expand -group {IQ Inputs} -color {Spring Green} /top/DUT/issue_ROB_index
add wave -noupdate -divider Outputs
add wave -noupdate -expand -group {IQ Outputs} -color Orchid /top/DUT/issue_ready
add wave -noupdate -divider {PRF Interface}
add wave -noupdate -divider Inputs
add wave -noupdate -expand -group {Reg Read Inputs} -color Orange /top/DUT/A_reg_read_ack
add wave -noupdate -expand -group {Reg Read Inputs} -color Orange /top/DUT/A_reg_read_port
add wave -noupdate -expand -group {Reg Read Inputs} -color {Cornflower Blue} /top/DUT/B_reg_read_ack
add wave -noupdate -expand -group {Reg Read Inputs} -color {Cornflower Blue} /top/DUT/B_reg_read_port
add wave -noupdate -expand -group {Reg Read Inputs} -color Tan /top/DUT/reg_read_data_by_bank_by_port
add wave -noupdate -expand -group {Forward Inputs} -color Tan /top/DUT/forward_data_by_bank
add wave -noupdate -expand -group {Writeback Inputs} -color Tan /top/DUT/WB_ready
add wave -noupdate -divider Outputs
add wave -noupdate -expand -group {Writeback Outputs} -color Orchid /top/DUT/WB_valid
add wave -noupdate -expand -group {Writeback Outputs} -color Orchid /top/DUT/WB_data
add wave -noupdate -expand -group {Writeback Outputs} -color Orchid /top/DUT/WB_PR
add wave -noupdate -expand -group {Writeback Outputs} -color Orchid /top/DUT/WB_ROB_index
add wave -noupdate -divider Debug
add wave -noupdate -expand -group SVA /top/SVA/a_ALURP_1_WB_VALID
add wave -noupdate -expand -group SVA /top/SVA/a_ALURP_1_WB_DATA
add wave -noupdate -expand -group SVA /top/SVA/a_ALURP_1_WB_PR
add wave -noupdate -expand -group SVA /top/SVA/a_ALURP_1_WB_ROB
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {215 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 266
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
WaveRestoreZoom {81 ns} {308 ns}

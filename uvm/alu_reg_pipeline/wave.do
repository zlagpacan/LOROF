onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /top/DUT/CLK
add wave -noupdate /top/DUT/nRST
add wave -noupdate /top/DUT/issue_valid
add wave -noupdate /top/DUT/issue_op
add wave -noupdate /top/DUT/issue_A_forward
add wave -noupdate /top/DUT/issue_A_bank
add wave -noupdate /top/DUT/issue_B_forward
add wave -noupdate /top/DUT/issue_B_bank
add wave -noupdate /top/DUT/issue_dest_PR
add wave -noupdate /top/DUT/issue_ROB_index
add wave -noupdate /top/DUT/issue_ready
add wave -noupdate /top/DUT/A_reg_read_ack
add wave -noupdate /top/DUT/A_reg_read_port
add wave -noupdate /top/DUT/B_reg_read_ack
add wave -noupdate /top/DUT/B_reg_read_port
add wave -noupdate /top/DUT/reg_read_data_by_bank_by_port
add wave -noupdate /top/DUT/forward_data_by_bank
add wave -noupdate /top/DUT/WB_valid
add wave -noupdate /top/DUT/WB_data
add wave -noupdate /top/DUT/WB_PR
add wave -noupdate /top/DUT/WB_ROB_index
add wave -noupdate /top/DUT/WB_ready
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {72 ns} 0}
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
WaveRestoreZoom {48 ns} {124 ns}

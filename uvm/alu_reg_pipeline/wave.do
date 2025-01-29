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
add wave -noupdate -expand -group {Reg Read Inputs} -color Tan -subitemconfig {{/top/DUT/reg_read_data_by_bank_by_port[3]} {-color Tan} {/top/DUT/reg_read_data_by_bank_by_port[3][1]} {-color Tan} {/top/DUT/reg_read_data_by_bank_by_port[3][0]} {-color Tan} {/top/DUT/reg_read_data_by_bank_by_port[2]} {-color Tan} {/top/DUT/reg_read_data_by_bank_by_port[1]} {-color Tan} {/top/DUT/reg_read_data_by_bank_by_port[0]} {-color Tan}} /top/DUT/reg_read_data_by_bank_by_port
add wave -noupdate -expand -group {Forward Inputs} -color Tan -subitemconfig {{/top/DUT/forward_data_by_bank[3]} {-color Tan} {/top/DUT/forward_data_by_bank[3][31]} {-color Tan} {/top/DUT/forward_data_by_bank[3][30]} {-color Tan} {/top/DUT/forward_data_by_bank[3][29]} {-color Tan} {/top/DUT/forward_data_by_bank[3][28]} {-color Tan} {/top/DUT/forward_data_by_bank[3][27]} {-color Tan} {/top/DUT/forward_data_by_bank[3][26]} {-color Tan} {/top/DUT/forward_data_by_bank[3][25]} {-color Tan} {/top/DUT/forward_data_by_bank[3][24]} {-color Tan} {/top/DUT/forward_data_by_bank[3][23]} {-color Tan} {/top/DUT/forward_data_by_bank[3][22]} {-color Tan} {/top/DUT/forward_data_by_bank[3][21]} {-color Tan} {/top/DUT/forward_data_by_bank[3][20]} {-color Tan} {/top/DUT/forward_data_by_bank[3][19]} {-color Tan} {/top/DUT/forward_data_by_bank[3][18]} {-color Tan} {/top/DUT/forward_data_by_bank[3][17]} {-color Tan} {/top/DUT/forward_data_by_bank[3][16]} {-color Tan} {/top/DUT/forward_data_by_bank[3][15]} {-color Tan} {/top/DUT/forward_data_by_bank[3][14]} {-color Tan} {/top/DUT/forward_data_by_bank[3][13]} {-color Tan} {/top/DUT/forward_data_by_bank[3][12]} {-color Tan} {/top/DUT/forward_data_by_bank[3][11]} {-color Tan} {/top/DUT/forward_data_by_bank[3][10]} {-color Tan} {/top/DUT/forward_data_by_bank[3][9]} {-color Tan} {/top/DUT/forward_data_by_bank[3][8]} {-color Tan} {/top/DUT/forward_data_by_bank[3][7]} {-color Tan} {/top/DUT/forward_data_by_bank[3][6]} {-color Tan} {/top/DUT/forward_data_by_bank[3][5]} {-color Tan} {/top/DUT/forward_data_by_bank[3][4]} {-color Tan} {/top/DUT/forward_data_by_bank[3][3]} {-color Tan} {/top/DUT/forward_data_by_bank[3][2]} {-color Tan} {/top/DUT/forward_data_by_bank[3][1]} {-color Tan} {/top/DUT/forward_data_by_bank[3][0]} {-color Tan} {/top/DUT/forward_data_by_bank[2]} {-color Tan} {/top/DUT/forward_data_by_bank[1]} {-color Tan} {/top/DUT/forward_data_by_bank[0]} {-color Tan}} /top/DUT/forward_data_by_bank
add wave -noupdate -expand -group {Writeback Inputs} -color Tan /top/DUT/WB_ready
add wave -noupdate -divider Outputs
add wave -noupdate -expand -group {Writeback Outputs} -color Orchid /top/DUT/WB_valid
add wave -noupdate -expand -group {Writeback Outputs} -color Orchid /top/DUT/WB_data
add wave -noupdate -expand -group {Writeback Outputs} -color Orchid /top/DUT/WB_PR
add wave -noupdate -expand -group {Writeback Outputs} -color Orchid /top/DUT/WB_ROB_index
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {40 ns} 0}
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
WaveRestoreZoom {0 ns} {227 ns}

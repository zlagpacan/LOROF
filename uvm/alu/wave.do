onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /top/alu_intf/CLK
add wave -noupdate /top/alu_intf/op
add wave -noupdate /top/alu_intf/A
add wave -noupdate /top/alu_intf/B
add wave -noupdate /top/alu_intf/out
add wave -noupdate /top/DUT/op
add wave -noupdate /top/DUT/A
add wave -noupdate /top/DUT/B
add wave -noupdate /top/DUT/out
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1162 ns} 0}
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
WaveRestoreZoom {0 ns} {1680 ns}

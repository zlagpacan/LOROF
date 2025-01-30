onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group {TB - Clock} -color {Spring Green} /top/alu_intf/CLK
add wave -noupdate -divider {DUT Inputs}
add wave -noupdate -expand -group {ALU Inputs} -color Orange /top/alu_intf/op
add wave -noupdate -expand -group {ALU Inputs} -color {Spring Green} /top/alu_intf/A
add wave -noupdate -expand -group {ALU Inputs} -color {Spring Green} /top/alu_intf/B
add wave -noupdate -divider {DUT Outputs}
add wave -noupdate -expand -group {ALU Outputs} -color Orchid /top/alu_intf/out
add wave -noupdate -divider {SVA - Debug}
add wave -noupdate -expand -group SVA -color Gray80 -subitemconfig {/top/SVA/CLK {-color Gray80} /top/SVA/op {-color Gray80} /top/SVA/B {-color Gray80} /top/SVA/A {-color Gray80} /top/SVA/out {-color Gray80}} /top/SVA/assert__sva_alu_add
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_shift_left
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_signed_lt
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_unsigned_lt
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_xor
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_shift_right
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_or
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_and
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_sub
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_shift_left_repeat
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_signed_lt_repeat
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_unsigned_lt_repeat
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_xor_repeat
add wave -noupdate -expand -group SVA -color Gray80 -subitemconfig {/top/SVA/CLK {-color Gray80} /top/SVA/op {-color Gray80} {/top/SVA/B[4:0]} {-color Gray80} /top/SVA/A {-color Gray80} /top/SVA/out {-color Gray80}} /top/SVA/assert__sva_alu_arith_shift_right
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_or_repeat
add wave -noupdate -expand -group SVA -color Gray80 /top/SVA/assert__sva_alu_and_repeat
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {132 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 233
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
WaveRestoreZoom {0 ns} {319 ns}

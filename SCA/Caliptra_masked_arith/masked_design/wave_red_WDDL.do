onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group redu_WDDL -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/naive
add wave -noupdate -expand -group redu_WDDL -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/reducted
add wave -noupdate -expand -group redu_WDDL -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/reducted_n
add wave -noupdate -expand -group redu_WDDL -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/x
add wave -noupdate -expand -group redu_WDDL -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/y
add wave -noupdate -expand -group redu_WDDL -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/x_n
add wave -noupdate -expand -group redu_WDDL -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/y_n
add wave -noupdate -expand -group add_1 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/A
add wave -noupdate -expand -group add_1 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/B
add wave -noupdate -expand -group add_1 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/C
add wave -noupdate -expand -group add_1 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/C_n
add wave -noupdate -expand -group add_1 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/carry
add wave -noupdate -expand -group add_1 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/carry_n
add wave -noupdate -expand -group add2 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add2/A
add wave -noupdate -expand -group add2 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add2/B
add wave -noupdate -expand -group add2 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add2/C
add wave -noupdate -expand -group add2 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add2/C_n
add wave -noupdate -expand -group add2 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add2/carry
add wave -noupdate -expand -group add2 -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add2/carry_n
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/i_bit1
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/i_bit2
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/i_carry
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/o_sum
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/o_carry
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/o_sum_n
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/o_carry_n
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/w_WIRE_1
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/w_WIRE_2
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/w_WIRE_3
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/i_bit1_n
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/i_bit2_n
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/i_carry_n
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/w_WIRE_1_n
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/w_WIRE_2_n
add wave -noupdate -expand -group first_add -radix hexadecimal -radixshowbase 1 /reduction_WDDL_tb/dut3/add1/u1/w_WIRE_3_n
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {63942 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
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
configure wave -timeline 1
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {210 ns}

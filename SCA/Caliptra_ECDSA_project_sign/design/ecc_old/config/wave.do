onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/ecc_cmd_i
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/addr_i
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/secret_key
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/busy_o
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/busy_o
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/reg_dinb_r
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/reg_dout_r
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/reg_addr_r
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/addrb_mux_s
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/i_ram_tdp_file/enb
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/i_ram_tdp_file/web
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/i_ram_tdp_file/addrb
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/i_ram_tdp_file/dinb
add wave -noupdate -radix hexadecimal -radixshowbase 1 /ecc_arith_unit_tb/dut/i_ram_tdp_file/doutb
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
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
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {873 ps}

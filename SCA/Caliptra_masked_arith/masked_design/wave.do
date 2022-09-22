onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal -radixshowbase 1 /PRNG_tb/dut/xor1/x
add wave -noupdate -radix hexadecimal -radixshowbase 1 /PRNG_tb/dut/xor1/random_number
add wave -noupdate -radix hexadecimal -radixshowbase 1 /PRNG_tb/dut/xor1/y
add wave -noupdate -radix hexadecimal -radixshowbase 1 /PRNG_tb/dut/xor1/z
add wave -noupdate -radix hexadecimal -radixshowbase 1 /PRNG_tb/dut/xor1/q
add wave -noupdate /PRNG_tb/dut/rst_n
add wave -noupdate /PRNG_tb/dut/PRNG_on
add wave -noupdate /PRNG_tb/dut/state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {399314 ps} 0}
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
WaveRestoreZoom {0 ps} {420 ns}

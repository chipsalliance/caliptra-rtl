onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /masked_arith_tb/dut/clock
add wave -noupdate /masked_arith_tb/dut/rst_n
add wave -noupdate -radix unsigned /masked_arith_tb/dut/state
add wave -noupdate /masked_arith_tb/dut/start
add wave -noupdate /masked_arith_tb/dut/done
add wave -noupdate -radix unsigned /masked_arith_tb/dut/kInv
add wave -noupdate -radix unsigned /masked_arith_tb/dut/R
add wave -noupdate -radix unsigned /masked_arith_tb/dut/P1
add wave -noupdate -radix unsigned /masked_arith_tb/dut/P2
add wave -noupdate -radix unsigned /masked_arith_tb/H1
add wave -noupdate -radix unsigned /masked_arith_tb/H2
add wave -noupdate -radix unsigned /masked_arith_tb/dut/s1
add wave -noupdate -radix unsigned /masked_arith_tb/dut/s2
add wave -noupdate -expand -group unprotected -radix unsigned /masked_arith_tb/unprotected/privKey
add wave -noupdate -expand -group unprotected -radix unsigned /masked_arith_tb/unprotected/r
add wave -noupdate -expand -group unprotected -radix unsigned /masked_arith_tb/unprotected/h
add wave -noupdate -expand -group unprotected -radix unsigned /masked_arith_tb/unprotected/add
add wave -noupdate -expand -group unprotected -radix unsigned /masked_arith_tb/unprotected/k_inv
add wave -noupdate -expand -group unprotected -radix unsigned /masked_arith_tb/unprotected/PR
add wave -noupdate -expand -group unprotected -radix unsigned /masked_arith_tb/unprotected/s
add wave -noupdate -expand -group unprotected -radix unsigned /masked_arith_tb/unprotected/PRH
add wave -noupdate -expand -group splitting -radix unsigned /masked_arith_tb/splitting_two/P
add wave -noupdate -expand -group splitting -radix unsigned /masked_arith_tb/splitting_two/key_or_message
add wave -noupdate -expand -group splitting -radix unsigned /masked_arith_tb/splitting_two/D1
add wave -noupdate -expand -group splitting -radix unsigned /masked_arith_tb/splitting_two/PD
add wave -noupdate -expand -group splitting -radix unsigned /masked_arith_tb/splitting_two/QD
add wave -noupdate -expand -group splitting -radix unsigned /masked_arith_tb/splitting_two/D2
add wave -noupdate -expand -group splitting -radix unsigned /masked_arith_tb/splitting_two/d
add wave -noupdate -expand -group PR_side -radix unsigned /masked_arith_tb/dut/red1/reducted
add wave -noupdate -expand -group PR_side -radix unsigned /masked_arith_tb/dut/red1/naive
add wave -noupdate -expand -group PR_side -radix unsigned /masked_arith_tb/dut/PR_dut/A
add wave -noupdate -expand -group PR_side -radix unsigned /masked_arith_tb/dut/PR_dut/B
add wave -noupdate -expand -group PR_side -radix unsigned /masked_arith_tb/dut/PR_dut/P
add wave -noupdate -radix unsigned /masked_arith_tb/dut/red2/reducted
add wave -noupdate -radix unsigned /masked_arith_tb/dut/red3/reducted
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {414937 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 208
configure wave -valuecolwidth 107
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
WaveRestoreZoom {401 ns} {821 ns}

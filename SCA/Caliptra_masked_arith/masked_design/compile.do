
#cd ../../Users/t-ekarabulut/OneDrive\ -\ Microsoft/Caliptra_masked_arith/masked_design

vlib work


vlog -work work "./xorshift.v"
vlog -work work "./PRNG.v"
vlog -work work "./reduction.v"
vlog -work work "./adder.v"
vlog -work work "./multiplier.v"
vlog -work work "./masked_arith.v"
vlog -work work "./full_adder_WDDL.v"
vlog -work work "./adder_13_bit_WDDL.v"
vlog -work work "./reduction_WDDL.v"
vlog -work work "./tb/PRNG_tb.sv"
vlog -work work "./tb/reduction_tb.sv"
vlog -work work "./tb/masked_arith_tb.sv"
vlog -work work "./tb/reduction_WDDL_tb.sv"



#vsim -l 115.log -t 1ps -vopt -lib work work.reduction_WDDL_tb -voptargs=+acc
vsim -l transcript.log -t 1ps -lib work reduction_WDDL_tb

view wave
view structure
view signals

#do wave.do
#do wave_red.do
#do wave_mask.do
do wave_red_WDDL.do
run 1ms
#run 200ns
    
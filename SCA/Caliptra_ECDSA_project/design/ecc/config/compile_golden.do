
#cd ../../Users/t-ekarabulut/OneDrive\ -\ Microsoft/Caliptra_ECDSA_project/design/ecc/config

vlib work2

vlog -work work2 "../../ecc/tb/ecc_arith_unit_tb.sv"
vlog -work work2 "../../ecc/rtl/ecc_arith_unit.sv"
vlog -work work2 "../../ecc/rtl/ecc_ctrl.sv"
vlog -work work2 "../../ecc/rtl/ecc_uop.sv"
vlog -work work2 "../../ecc/rtl/ecc_sequencer.sv"
vlog -work work2 "../../ecc/rtl/fau.sv"
vlog -work work2 "../../ecc/rtl/mm.sv"
vlog -work work2 "../../ecc/rtl/PE_first.sv"
vlog -work work2 "../../ecc/rtl/PE.sv"
vlog -work work2 "../../ecc/rtl/PE_final.sv"
vlog -work work2 "../../ecc/rtl/mult_dsp.sv"
vlog -work work2 "../../ecc/rtl/add_sub_mod_alter.sv"
vlog -work work2 "../../ecc/rtl/add_sub_mod.sv"
vlog -work work2 "../../ecc/rtl/add_sub_gen.sv"
vlog -work work2 "../../ecc/rtl/adder.sv"
vlog -work work2 "../../ecc/rtl/expand.sv"
vlog -work work2 "../../ecc/rtl/compact.sv"
vlog -work work2 "../../ecc/rtl/ram_tdp_file.sv"



#vsim -l 115.log -t 1ps -vopt -lib work work.SAKURA_G_host_if_tb -voptargs=+acc
vsim -l transcript.log -t 1ps -lib work2 ecc_arith_unit_tb

view wave
view structure
view signals

do wave.do

run 1ms
    

#cd ../../Users/t-ekarabulut/OneDrive\ -\ Microsoft/Caliptra_ECDSA_project_sign/design/compile_git_files/Sakura_G_modules

vlib work

vlog -work work "../../ecc/tb/MontgomeryMultiplier_tb.sv"
vlog -work work "../../ecc/rtl/ecc_MontgomeryMultiplier.v"
vlog -work work "../../ecc/rtl/ecc_PE_first.v"
vlog -work work "../../ecc/rtl/ecc_PE.v"
vlog -work work "../../ecc/rtl/ecc_PE_final.v"
vlog -work work "../../ecc/rtl/ecc_mult_dsp.v"



#vsim -l 115.log -t 1ps -vopt -lib work work.MontgomeryMultiplier_tb -voptargs=+acc
vsim -l transcript.log -t 1ps -lib work MontgomeryMultiplier_tb

view wave
view structure
view signals

do wave.do
run 1ms
    
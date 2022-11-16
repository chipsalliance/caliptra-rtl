####################
# Common Setup.

INCDIRS = +incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv \
          +incdir+../config_policies

HVL_SV_SOURCE = ${QUESTA_MVC_HOME}/include/questa_mvc_svapi.sv \
            +define+MAP_PROT_ATTR ${QUESTA_MVC_HOME}/questa_mvc_src/sv/mvc_pkg.sv \
            +incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv/ahb ${QUESTA_MVC_HOME}/questa_mvc_src/sv/ahb/mgc_ahb_v2_0_pkg.sv \
            ../config_policies/qvip_ahb_lite_slave_params_pkg.sv \
            qvip_ahb_lite_slave_pkg.sv \
            hvl_qvip_ahb_lite_slave.sv
HDL_SV_SOURCE = \
            +incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv/ahb/modules ${QUESTA_MVC_HOME}/questa_mvc_src/sv/ahb/modules/ahb_lite_slave.sv \
            default_clk_gen.sv \
            default_reset_gen.sv \
            hdl_qvip_ahb_lite_slave.sv

UVM_OPTIONS = +UVM_TESTNAME=qvip_ahb_lite_slave_test_base +SEQ=qvip_ahb_lite_slave_example_vseq

####################
# Questa support.

all: work sv opt sim

sv: hvl_sv hdl_sv

vis: work sv vis_opt vis_sim

work:
	vlib work

hvl_sv:
	vlog $(INCDIRS) $(HVL_SV_SOURCE)

hdl_sv:
	vlog $(INCDIRS) $(HDL_SV_SOURCE)

opt:
	vopt hdl_qvip_ahb_lite_slave hvl_qvip_ahb_lite_slave -o top_opt

vis_opt:
	vopt hdl_qvip_ahb_lite_slave hvl_qvip_ahb_lite_slave -o top_opt -debug -designfile design.bin

sim:
	vsim -mvchome ${QUESTA_MVC_HOME} top_opt $(UVM_OPTIONS) +nowarnTSCALE -t 1ns -c -do "run -all; quit"

vis_sim:
	vsim -mvchome ${QUESTA_MVC_HOME} top_opt $(UVM_OPTIONS) +nowarnTSCALE -t 1ns -c -do "run -all; quit" -qwavedb=+signal+transaction+class+uvm_schematic
	visualizer -designfile design.bin -wavefile qwave.db

vis_int: work sv vis_opt
	vsim -mvchome ${QUESTA_MVC_HOME} top_opt $(UVM_OPTIONS) +nowarnTSCALE -t 1ns -visualizer=design.bin -qwavedb=+signal+transaction+class+uvm_schematic

gui:
	vsim -mvchome ${QUESTA_MVC_HOME} top_opt $(UVM_OPTIONS) +nowarnTSCALE -t 1ns

####################
# Incisive support.

ius32:
	env LD_LIBRARY_PATH=${QUESTA_MVC_HOME}/questa_mvc_core/linux_gcc-6.3_ius:${IUS_HOME}/tools/cdsgcc/gcc/6.3/install/lib:${LD_LIBRARY_PATH} \
         xrun -sv -uvm -quiet -access +rwc -timescale 1ns/1ns $(INCDIRS) $(HVL_SV_SOURCE) $(HDL_SV_SOURCE) \
         -sv_root ${QUESTA_MVC_HOME}/questa_mvc_core/linux_gcc-6.3_ius \
         -sv_lib libahb_IN_SystemVerilog_IUS_full \
         $(UVM_OPTIONS)

ius64:
	env LD_LIBRARY_PATH=${QUESTA_MVC_HOME}/questa_mvc_core/linux_x86_64_gcc-6.3_ius:${IUS_HOME}/tools/cdsgcc/gcc/6.3/install/lib64:${LD_LIBRARY_PATH} \
         xrun -sv -uvm -quiet -access +rwc -64bit -timescale 1ns/1ns $(INCDIRS) $(HVL_SV_SOURCE) $(HDL_SV_SOURCE) \
         -sv_root ${QUESTA_MVC_HOME}/questa_mvc_core/linux_x86_64_gcc-6.3_ius \
         -sv_lib libahb_IN_SystemVerilog_IUS_full \
         $(UVM_OPTIONS)

####################
# VCS support.

vcs32:
	env LD_LIBRARY_PATH=${QUESTA_MVC_HOME}/questa_mvc_core/linux_gcc-6.2.0_vcs:${VCS_HOME}/gnu/linux/gcc-6.2.0/lib:${LD_LIBRARY_PATH} \
        vcs -sverilog -ntb_opts uvm -debug_access+w -quiet  -timescale=1ns/1ns \
        -ld ${VCS_HOME}/gnu/linux/gcc-6.2.0/xbin/g++ \
        $(INCDIRS) $(HVL_SV_SOURCE) $(HDL_SV_SOURCE)                     \
        -syslib ${QUESTA_MVC_HOME}/questa_mvc_core/linux_gcc-6.2.0_vcs/libahb_IN_SystemVerilog_VCS_full.so
	env LD_LIBRARY_PATH=${QUESTA_MVC_HOME}/questa_mvc_core/linux_gcc-6.2.0_vcs:${VCS_HOME}/gnu/linux/gcc-6.2.0/lib:${LD_LIBRARY_PATH} \
        ./simv $(UVM_OPTIONS)

vcs64:
	env LD_LIBRARY_PATH=${QUESTA_MVC_HOME}/questa_mvc_core/linux_x86_64_gcc-6.2.0_vcs:${VCS_HOME}/gnu/linux/gcc-6.2.0/lib64:${LD_LIBRARY_PATH} \
        vcs -sverilog -ntb_opts uvm -debug_access+w -quiet  -full64 -timescale=1ns/1ns \
        -ld ${VCS_HOME}/gnu/linux/gcc-6.2.0/xbin/g++ \
        $(INCDIRS) $(HVL_SV_SOURCE) $(HDL_SV_SOURCE)                     \
        -syslib ${QUESTA_MVC_HOME}/questa_mvc_core/linux_x86_64_gcc-6.2.0_vcs/libahb_IN_SystemVerilog_VCS_full.so
	env LD_LIBRARY_PATH=${QUESTA_MVC_HOME}/questa_mvc_core/linux_x86_64_gcc-6.2.0_vcs:${VCS_HOME}/gnu/linux/gcc-6.2.0/lib64:${LD_LIBRARY_PATH} \
        ./simv $(UVM_OPTIONS)

####################
# Cleanup.

clean:
	rm -rf work transcript vsim.wlf
	rm -rf csrc simv* ucli.key vc_hdrs.h
	rm -rf INCA_libs xrun.log xrun.history

.PHONY: all sv hvl_sv hdl_sv opt sim gui ius32 ius64 vcs32 vcs64
.PHONY: vis vis_opt vis_sim vis_int

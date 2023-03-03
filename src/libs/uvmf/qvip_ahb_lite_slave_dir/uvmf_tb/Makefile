####################
# Common Setup.

INCDIRS = +incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv \
          +incdir+${UVMF_HOME}/uvmf_base_pkg \
          +incdir+../config_policies

HVL_SV_SOURCE = ../uvmf/hvl_qvip_ahb_lite_slave.sv
HDL_SV_SOURCE = ../uvmf/hdl_qvip_ahb_lite_slave.sv

UVM_OPTIONS = +UVM_TESTNAME=qvip_ahb_lite_slave_test_base +SEQ=qvip_ahb_lite_slave_example_vseq

export QVIP_AHB_LITE_SLAVE_DIR_NAME ?= $(shell pwd)/../uvmf

####################
# Questa support.

all: work sv opt sim

sv: hvl_sv hdl_sv

work:
	vlib work

hvl_sv:
	vlog -f qvip_ahb_lite_slave_test_filelist.f $(INCDIRS) $(HVL_SV_SOURCE)

hdl_sv:
	vlog -f qvip_ahb_lite_slave_test_filelist.f $(INCDIRS) $(HDL_SV_SOURCE)

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
# Cleanup.

clean:
	rm -rf work transcript vsim.wlf

.PHONY: all sv hvl_sv hdl_sv opt sim gui
.PHONY: vis vis_opt vis_sim vis_int

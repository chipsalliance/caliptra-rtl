# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

TEST_CFLAGS = -g -O3
ABI = -mabi=ilp32 -march=rv32imac

VERILATOR = verilator
GCC_PREFIX = riscv64-unknown-elf
BUILD_DIR = $(CURDIR)

# Define test name
TESTNAME ?= iccm_lock
ifneq (,$(SIM_TOOLS_TOP_COMPILE_ROOT))
	TEST_DIR = $(SIM_TOOLS_TOP_COMPILE_ROOT)/test_suites/$(TESTNAME)
	HEX_DIR = $(SIM_TOOLS_TOP_COMPILE_ROOT)/test_suites/hex
	INCLUDES_DIR = $(SIM_TOOLS_TOP_COMPILE_ROOT)/test_suites/includes
	TBDIR = $(SIM_TOOLS_TOP_COMPILE_ROOT)/tb
	RISCV_HW_IF_DIR = $(SIM_TOOLS_TOP_COMPILE_ROOT)/test_suites/riscv_hw_if
else
	TEST_DIR = $(WORKSPACE)/Caliptra/src/integration/test_suites/$(TESTNAME)
	HEX_DIR = $(WORKSPACE)/Caliptra/src/integration/test_suites/hex
	INCLUDES_DIR = $(WORKSPACE)/Caliptra/src/integration/test_suites/includes
	TBDIR = $(WORKSPACE)/Caliptra/src/integration/tb
	RISCV_HW_IF_DIR = $(WORKSPACE)/Caliptra/src/integration/test_suites/riscv_hw_if
endif

# Determine test directory
#ifneq (,$(wildcard $(TBDIR)/tests/$(TEST)))
#  TEST_DIR = $(TBDIR)/tests/$(TEST)
#endif

HEADER_FILES := $(INCLUDES_DIR)/caliptra_defines.h \
		$(INCLUDES_DIR)/defines.h \
		$(WORKSPACE)/Caliptra/src/integration/rtl/caliptra_reg.h  \
		$(RISCV_HW_IF_DIR)/riscv_hw_if.h

ifeq (0,$(shell test -e $(TEST_DIR)/crt0.[sS] && echo $$?))
	OFILES += crt0.o
endif
OFILES += $(TESTNAME).o

ifdef debug
 DEBUG_PLUS = +dumpon
 IRUN_DEBUG = -access +rc
 IRUN_DEBUG_RUN = -input $(RV_ROOT)/testbench/input.tcl
 VCS_DEBUG = -debug_access
 VERILATOR_DEBUG = --trace
 RIVIERA_DEBUG = +access +r
endif

# RK
# provide specific link file
ifeq (,$(wildcard $(TEST_DIR)/$(TESTNAME).ld))
	LINK = $(RISCV_HW_IF_DIR)/link.ld
else
	LINK = $(TEST_DIR)/$(TESTNAME).ld
endif

VPATH = $(TEST_DIR) $(BUILD_DIR) $(TBDIR)

# Provides updates to OFILES, HEADER_FILES, VPATH
-include $(TEST_DIR)/$(TESTNAME).mki

# Use eval to expand env variables in the .vf file
$(eval TBFILES = $(shell cat $(TBDIR)/../config/caliptra_top_tb.vf | grep -v '+incdir+'))

#defines  = $(BUILD_DIR)/common_defines.vh
#defines += $(RV_ROOT)/design/include/el2_def.sv
#defines += $(BUILD_DIR)/el2_pdef.vh
includes = -I$(BUILD_DIR)
#
#         .--------------------------------------------------------------------------------.
#         | Verilator does not support unpacked structs/unions - waive this warning so     |
#         | that unpacked structs are treated as packed. This should only impact files     |
#         | generated from RDL register files, which use unpacked structs liberally.       |
#         '-----------------------------------------------------------------------------+--'
#                                                                                       |
#         .---------------------------------------------------------------------.       |
#         | This is flagged for every generated SystemVerilog file defining a   |       |
#         | register block. The field_storage signal is the target of the       |       |
#         | warning, indicating multiple drivers/different clocking.            |       |
#         '----------------------------------------------------------------+----'       |
#                                                                          |            |
#         .------------------------------------------------------.         |            |
#         | PeakRDL implements the default incrsaturate behavior |         |            |
#         | for counter registers by performing a > comparison   |         |            |
#         | with an all-ones value (i.e. cnt > 32'hFFFFFFFF)     |         |            |
#         | which, by definition, can never be true. Verilator   |         |            |
#         | warns that this will compile to a constant 0.        |         |            |
#         '------------------------------------------------+-----'         |            |
#                                                          |               |            |
#         .--------------------------------------------.   |               |            |
#         | Vectors that are little bit-endian are not |   |               |            |
#         | supported by Verilator, according to a     |   |               |            |
#         | warning that is thrown. This is supposedly |   |               |            |
#         | resolved as of version 3.720, according    |   |               |            |
#         | to the release notes.                      |   |               |            |
#         '-----------------------------------+--------'   |               |            |
#                                             |            |               |            |
#         .------------------------------.    |            |               |            |
#         | Inherited from ChipsAlliance |    |            |               |            |
#         | SweRV repository provided    |    |            |               |            |
#         | Makefile                     |    |            |               |            |
#         '-----+------------+-----------'    |            |               |            |
#               |            |                |            |               |            |
#               v            v                v            v               v            v
suppress = -Wno-WIDTH -Wno-UNOPTFLAT -Wno-LITENDIAN -Wno-CMPCONST -Wno-MULTIDRIVEN -Wno-UNPACKED

# CFLAGS for verilator generated Makefiles. Without -std=c++11 it
# complains for `auto` variables
CFLAGS += "-std=c++11"

# Optimization for better performance; alternative is nothing for
# slower runtime (faster compiles) -O2 for faster runtime (slower
# compiles), or -O for balance.
VERILATOR_MAKE_FLAGS = OPT_FAST="-Os"

# Targets
all: clean verilator

clean:
	rm -rf *.log *.s *.hex *.dis *.size *.tbl irun* vcs* simv* .map *.map snapshots \
	verilator* *.exe obj* *.o ucli.key vc_hdrs.h csrc *.csv work \
	dataset.asdb  library.cfg vsimsa.cfg  riviera-build wave.asdb sim.vcd \
	*.h

############ Model Builds ###############################

verilator-build: $(TBFILES) $(INCLUDES_DIR)/defines.h test_caliptra_top_tb.cpp
	$(VERILATOR)  --cc -CFLAGS $(CFLAGS) \
	  +libext+.v+.sv +define+RV_OPENSOURCE \
	  --timescale 1ns/1ps \
	  $(includes) \
	  $(suppress) \
	  -f $(TBDIR)/../config/caliptra_top_tb.vf --top-module caliptra_top_tb \
	  -exe test_caliptra_top_tb.cpp --autoflush $(VERILATOR_DEBUG)
	cp $(TBDIR)/test_caliptra_top_tb.cpp obj_dir/
	$(MAKE) -j -e -C obj_dir/ -f Vcaliptra_top_tb.mk $(VERILATOR_MAKE_FLAGS) VM_PARALLEL_BUILDS=1
	touch verilator-build

############ TEST Simulation ###############################

verilator: program.hex verilator-build
	./obj_dir/Vcaliptra_top_tb

############ TEST build ###############################

ifeq ($(shell which $(GCC_PREFIX)-gcc 2> /dev/null),)
program.hex: $(BUILD_DIR)/defines.h
	@echo " !!! No $(GCC_PREFIX)-gcc in path, using canned hex files !!"
	cp $(HEX_DIR)/$(TESTNAME).hex program.hex
else ifneq (,$(wildcard $(TEST_DIR)/$(TESTNAME).makefile))
program.hex:
	@echo Building $(TESTNAME) via $(TEST_DIR)/$(TESTNAME).makefile
	$(MAKE) -f $(TEST_DIR)/$(TESTNAME).makefile
else ifneq (,$(wildcard $(TEST_DIR)/$(TESTNAME)))
program.hex:
	@echo "Building program.hex from $(TESTNAME) using Crypto Test rules for pre-compiled RUST executables"
	-$(GCC_PREFIX)-objcopy -O verilog -R .data -R .rodata -R .bss -R .sbss -R .iccm -R .dccm -R .eh_frame --pad-to 0x8000 --no-change-warnings $(TEST_DIR)/$(TESTNAME) program.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .data -j .rodata -j .bss -j .sbss -j .dccm \
			      --change-section-lma       .data-0x50000000 \
			      --change-section-lma     .rodata-0x50000000 \
			      --change-section-lma        .bss-0x50000000 \
			      --change-section-lma       .sbss-0x50000000 \
			      --change-section-lma       .dccm-0x50000000 \
			      --pad-to 0x20000 \
			      --no-change-warnings \
			      $(TEST_DIR)/$(TESTNAME) dccm.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .iccm                       --change-section-address .iccm=0 --pad-to 0x20000 --no-change-warnings $(TEST_DIR)/$(TESTNAME) iccm.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .mailbox --gap-fill 0x0     --change-section-address .mailbox=0 --pad-to 0x20000 --no-change-warnings $(TEST_DIR)/$(TESTNAME) mailbox.hex
	$(GCC_PREFIX)-objdump -S  $(TEST_DIR)/$(TESTNAME) > $(TESTNAME).dis
	$(GCC_PREFIX)-size        $(TEST_DIR)/$(TESTNAME) | tee $(TESTNAME).size

else
program.hex: $(OFILES) $(LINK)
	@echo Building $(TESTNAME)
	$(GCC_PREFIX)-gcc $(ABI) -Wl,-Map=$(TEST).map -lgcc -T$(LINK) -o $(TESTNAME).exe $(OFILES) -nostartfiles  $(TEST_LIBS)
	-$(GCC_PREFIX)-objcopy -O verilog -R .data -R .rodata -R .sbss -R .bss -R .data_iccm0 -R .data_iccm1 -R .data_iccm2 -R .iccm -R .dccm -R .eh_frame --pad-to 0x8000 --no-change-warnings $(TESTNAME).exe program.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .data -j .rodata -j .sbss -j .bss -j .data_iccm0 -j .data_iccm1 -j .data_iccm2 -j .dccm \
			      --change-section-lma       .data-0x50000000 \
			      --change-section-lma     .rodata-0x50000000 \
			      --change-section-lma       .sbss-0x50000000 \
			      --change-section-lma        .bss-0x50000000 \
			      --change-section-lma .data_iccm0-0x50000000 \
			      --change-section-lma .data_iccm1-0x50000000 \
			      --change-section-lma .data_iccm2-0x50000000 \
			      --change-section-lma       .dccm-0x50000000 \
			      --pad-to 0x20000 \
			      --no-change-warnings \
			      $(TESTNAME).exe dccm.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .iccm                       --change-section-address .iccm=0 --pad-to 0x20000 --no-change-warnings $(TESTNAME).exe iccm.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .mailbox --gap-fill 0x0     --change-section-address .mailbox=0 --pad-to 0x20000 --no-change-warnings $(TESTNAME).exe mailbox.hex
	$(GCC_PREFIX)-objdump -S  $(TESTNAME).exe > $(TESTNAME).dis
	$(GCC_PREFIX)-size        $(TESTNAME).exe | tee $(TESTNAME).size
	@echo Completed building $(TESTNAME)

%.o : %.s $(HEADER_FILES)
	cp $(HEADER_FILES) $(BUILD_DIR)
	$(GCC_PREFIX)-cpp $(includes) -I$(TEST_DIR)  $<  > $*.cpp.s
	$(GCC_PREFIX)-as $(ABI) $*.cpp.s -o $@

%.o : %.c $(HEADER_FILES)
	cp $(HEADER_FILES) $(BUILD_DIR)
	$(GCC_PREFIX)-gcc $(includes) $(TEST_CFLAGS) -DCOMPILER_FLAGS="\"$(TEST_CFLAGS)\"" $(ABI) -nostdlib -c $< -o $@

endif

help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun vlog riviera help clean all verilator-build irun-build vcs-build riviera-build program.hex

.PHONY: help clean verilator vcs irun vlog riviera


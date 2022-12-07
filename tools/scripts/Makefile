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

GCC_PREFIX = riscv64-unknown-elf
BUILD_DIR = ${PWD}

# Define test name
#TESTNAME = hello_world
TEST_DIR = ${SIM_TOOLS_TOP_COMPILE_ROOT}/test_suites/${TESTNAME}
HEX_DIR = ${SIM_TOOLS_TOP_COMPILE_ROOT}/test_suites/hex
INCLUDES_DIR = ${SIM_TOOLS_TOP_COMPILE_ROOT}/test_suites/includes

# Determine test directory
#ifneq (,$(wildcard $(TBDIR)/tests/$(TEST)))
#  TEST_DIR = $(TBDIR)/tests/$(TEST)
#endif

HEADER_FILES := ${INCLUDES_DIR}/caliptra_defines.h \
		${INCLUDES_DIR}/defines.h \
		${SIM_TOOLS_TOP_COMPILE_ROOT}/rtl/caliptra_reg.h 

ifeq (0,$(shell test -e $(TEST_DIR)/crt0.[sS] && echo $$?))
	OFILES += crt0.o
endif
OFILES += $(TESTNAME).o

# RK
# provide specific link file
ifeq (,$(wildcard $(TEST_DIR)/$(TESTNAME).ld))
	LINK = $(BUILD_DIR)/link.ld
else
	LINK = $(TEST_DIR)/$(TESTNAME).ld
endif

VPATH = $(TEST_DIR) $(BUILD_DIR) $(TBDIR)

-include $(TEST_DIR)/$(TESTNAME).mki

includes = -I${BUILD_DIR}

# Targets
all: clean verilator

clean:
	rm -rf *.log *.s *.hex *.dis *.tbl irun* vcs* simv* *.map snapshots swerv* \
	verilator* *.exe obj* *.o ucli.key vc_hdrs.h csrc *.csv work\
	dataset.asdb  library.cfg vsimsa.cfg  riviera-build wave.asdb

############ TEST build ###############################

ifeq ($(shell which $(GCC_PREFIX)-gcc 2> /dev/null),)
program.hex: ${BUILD_DIR}/defines.h
	@echo " !!! No $(GCC_PREFIX)-gcc in path, using canned hex files !!"
	cp ${HEX_DIR}/$(TESTNAME).hex program.hex
else
ifneq (,$(wildcard $(TEST_DIR)/$(TESTNAME).makefile))
program.hex:
	@echo Building $(TESTNAME) via $(TEST_DIR)/$(TESTNAME).makefile
	$(MAKE) -f $(TEST_DIR)/$(TESTNAME).makefile
else
program.hex: $(OFILES) $(LINK)
	@echo Building $(TESTNAME)
	$(GCC_PREFIX)-gcc $(ABI) -Wl,-Map=$(TEST).map -lgcc -T$(LINK) -o $(TESTNAME).exe $(OFILES) -nostartfiles  $(TEST_LIBS)
	$(GCC_PREFIX)-objcopy -O verilog -R .data -R .bss -R .data_iccm0 -R .data_iccm1 -R .data_iccm2 -R .iccm -R .dccm -R .eh_frame $(TESTNAME).exe program.hex
	$(GCC_PREFIX)-objcopy -O verilog -j .data -j .bss -j .data_iccm0 -j .data_iccm1 -j .data_iccm2 -j .dccm \
			      --change-section-lma       .data-0x50000000 \
			      --change-section-lma        .bss-0x50000000 \
			      --change-section-lma .data_iccm0-0x50000000 \
			      --change-section-lma .data_iccm1-0x50000000 \
			      --change-section-lma .data_iccm2-0x50000000 \
			      --change-section-lma       .dccm-0x50000000 \
			      --pad-to 0x20000 \
			      $(TESTNAME).exe dccm.hex
	$(GCC_PREFIX)-objcopy -O verilog -j .iccm                       --change-section-address .iccm=0 --pad-to 0x20000 $(TESTNAME).exe iccm.hex
	$(GCC_PREFIX)-objcopy -O verilog -j .mailbox --gap-fill 0x0     --change-section-address .mailbox=0 --pad-to 0x20000 $(TESTNAME).exe mailbox.hex
	$(GCC_PREFIX)-objdump -S  $(TESTNAME).exe > $(TESTNAME).dis
	$(GCC_PREFIX)-size        $(TESTNAME).exe | tee $(TESTNAME).size
	@echo Completed building $(TESTNAME)

%.o : %.s ${HEADER_FILES}
	cp $(HEADER_FILES) $(BUILD_DIR)
	$(GCC_PREFIX)-cpp ${includes} -I${TEST_DIR}  $<  > $*.cpp.s
	$(GCC_PREFIX)-as ${ABI} $*.cpp.s -o $@

%.o : %.c ${HEADER_FILES}
	cp ${HEADER_FILES} ${BUILD_DIR}
	$(GCC_PREFIX)-gcc ${includes} ${TEST_CFLAGS} -DCOMPILER_FLAGS="\"${TEST_CFLAGS}\"" ${ABI} -nostdlib -c $< -o $@

endif
endif

help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun vlog riviera help clean all verilator-build irun-build vcs-build riviera-build program.hex

.PHONY: help clean verilator vcs irun vlog riviera


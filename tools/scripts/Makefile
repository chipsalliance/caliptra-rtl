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

TEST_CFLAGS = -g -O3 -funroll-all-loops
ABI = -mabi=ilp32 -march=rv32imac

GCC_PREFIX = riscv64-unknown-elf
BUILD_DIR = ${PWD}


# Define test name
#TESTNAME = hello_world
TEST_DIR = ${COMPILE_ROOT}/test_suites/${TESTNAME}
HEX_DIR = ${COMPILE_ROOT}/test_suites/hex
INCLUDES_DIR = ${COMPILE_ROOT}/test_suites/includes

# Determine test directory
#ifneq (,$(wildcard $(TBDIR)/tests/$(TEST)))
#  TEST_DIR = $(TBDIR)/tests/$(TEST)
#endif

OFILES = $(TESTNAME).o

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
	$(GCC_PREFIX)-objcopy -O verilog  $(TESTNAME).exe program.hex
	$(GCC_PREFIX)-objdump -S  $(TESTNAME).exe > $(TESTNAME).dis
	@echo Completed building $(TESTNAME)


%.o : %.s ${INCLUDES_DIR}/defines.h
	cp ${INCLUDES_DIR}/defines.h ${BUILD_DIR}
	$(GCC_PREFIX)-cpp -I${TEST_DIR}  $<  > $*.cpp.s
	$(GCC_PREFIX)-as ${ABI} $*.cpp.s -o $@


%.o : %.c ${INCLUDES_DIR}/defines.h
	cp ${INCLUDES_DIR}/defines.h ${BUILD_DIR}
	$(GCC_PREFIX)-gcc ${includes} ${TEST_CFLAGS} -DCOMPILER_FLAGS="\"${TEST_CFLAGS}\"" ${ABI} -nostdlib -c $< -o $@

endif
endif


help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun vlog riviera help clean all verilator-build irun-build vcs-build riviera-build program.hex

.PHONY: help clean verilator vcs irun vlog riviera


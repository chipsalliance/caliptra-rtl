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
GCC_PREFIX = riscv64-unknown-elf
BUILD_DIR = $(CURDIR)
today=$(shell date +%Y%m%d)

# Define test name
TESTNAME ?= fw_test_rom
TESTNAME_fw = $(TESTNAME)_fw
TEST_DIR = $(CALIPTRA_ROOT)/src/integration/test_suites/$(TESTNAME)

VPATH = $(TEST_DIR) $(BUILD_DIR)

# Targets
all: program.hex

clean:
	rm -rf *.log *.s *.hex *.dis *.size *.tbl .map *.map snapshots \
	*.exe obj* *.o csrc *.csv work \
	dataset.asdb  library.cfg vsimsa.cfg \
	*.h

############ TEST build ###############################

# Build program.hex from RUST executable
program.hex: fw_update.hex $(TEST_DIR)/$(TESTNAME)
	@-echo "Building program.hex from $(TESTNAME) using Crypto Test rules for pre-compiled RUST executables"
	$(GCC_PREFIX)-objcopy -I binary -O verilog --pad-to 0x8000 --gap-fill 0xFF --no-change-warnings $(TEST_DIR)/$(TESTNAME) program.hex
	#$(GCC_PREFIX)-objdump -S  $(TEST_DIR)/$(TESTNAME) > $(TESTNAME).dis
	#$(GCC_PREFIX)-size        $(TEST_DIR)/$(TESTNAME) | tee $(TESTNAME).size

fw_update.hex: $(TEST_DIR)/$(TESTNAME).extracted $(TEST_DIR)/$(TESTNAME_fw)
	@-echo "Building fw_update.hex from $(TESTNAME_fw) using binary objcopy pre-compiled RUST package"
	$(GCC_PREFIX)-objcopy -I binary -O verilog --pad-to 0x20000 --gap-fill 0xFF --no-change-warnings $(TEST_DIR)/$(TESTNAME_fw) fw_update.hex
	#@echo "Building fw_update.hex from $(TESTNAME_fw) using simple hexdump on pre-compiled RUST package"
	#-hexdump -v -e '16/1 "%02x " "\n"'  $(TEST_DIR)/$(TESTNAME_fw) > fw_update.hex

# Extract compiled FW from latest retrieved release
$(TEST_DIR)/$(TESTNAME).extracted: caliptra_release_v$(today)_0.zip
	@7z x -o"$(TEST_DIR)" $< caliptra-rom-with-log.bin
	 7z x -o"$(TEST_DIR)" $< image-bundle.bin
	 rm $<
	 mv $(TEST_DIR)/caliptra-rom-with-log.bin $(TEST_DIR)/$(TESTNAME)
	 mv $(TEST_DIR)/image-bundle.bin          $(TEST_DIR)/$(TESTNAME_fw)
	 touch $(TEST_DIR)/$(TESTNAME).extracted

# Retrieve latest build from caliptra-sw repo
# Fail if a build from within the last 30 days is not found
caliptra_release_v$(today)_0.zip: $(TEST_DIR)/$(TESTNAME)
	@base_url='https://github.com/chipsalliance/caliptra-sw/releases/download/'
	found=0
	full_path=""
	for days_ago in $$(seq 0 31); do
	  test_date=$$(date +%Y%m%d --date="$(today) -$${days_ago} days")
	  echo "Checking date $${test_date} for package"
	  super_base="release_v$${test_date}_0"
	  zipfile_base="caliptra_release_v$${test_date}_0"
	  full_path="$${base_url}/$${super_base}/$${zipfile_base}.zip"
	  if wget --spider --quiet $${full_path}; then
	    echo "Found $${full_path}";
	    found=1
	    break;
	  fi
	done
	if [[ $${found} -eq 1 ]]; then
	  wget --no-use-server-timestamps $${full_path}
	else
	  exit 1
	fi
	# Cheesy rename to satisfy makefile dependency
	if [[ ! -f "caliptra_release_v$(today)_0.zip" ]]; then
	  mv $${zipfile_base}.zip "caliptra_release_v$(today)_0.zip"
	fi

help:
	@echo Make sure the environment variable RV_ROOT is set.
	echo Possible targets: help clean all program.hex

.PHONY: help clean

.ONESHELL:

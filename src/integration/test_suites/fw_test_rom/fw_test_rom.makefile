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

# Offset calculations for fetching keys from ROM image
KEY_MANIFEST_ECC_PK_COUNT      = 4
KEY_MANIFEST_ECC_PK_SIZE       = 96
KEY_MANIFEST_ECC_PK_ROM_OFFSET = 8
KEY_MANIFEST_ECC_PK_LENGTH     = $(shell bc <<< "$(KEY_MANIFEST_ECC_PK_COUNT)*$(KEY_MANIFEST_ECC_PK_SIZE)")

KEY_MANIFEST_LMS_PK_COUNT      = 32
KEY_MANIFEST_LMS_PK_SIZE       = 48
KEY_MANIFEST_LMS_PK_ROM_OFFSET = $(shell bc <<< "$(KEY_MANIFEST_ECC_PK_ROM_OFFSET) + $(KEY_MANIFEST_ECC_PK_COUNT)*$(KEY_MANIFEST_ECC_PK_SIZE)")
KEY_MANIFEST_LMS_PK_LENGTH     = $(shell bc <<< "$(KEY_MANIFEST_LMS_PK_COUNT)*$(KEY_MANIFEST_LMS_PK_SIZE)")

KEY_MANIFEST_PK_LENGTH         = $(shell bc <<< "$(KEY_MANIFEST_LMS_PK_LENGTH) + $(KEY_MANIFEST_ECC_PK_LENGTH)")

OWNER_ECC_PK_SIZE              = 96
OWNER_ECC_PK_ROM_OFFSET        = 3652
OWNER_LMS_PK_SIZE              = 48
OWNER_LMS_PK_ROM_OFFSET        = $(shell bc <<< "$(OWNER_ECC_PK_ROM_OFFSET) + $(OWNER_ECC_PK_SIZE)")

OWNER_PK_LENGTH                = $(shell bc <<< "$(OWNER_LMS_PK_SIZE) + $(OWNER_ECC_PK_SIZE)")

# Targets
all: program.hex

clean:
	rm -rf *.log *.s *.hex *.dis *.size *.tbl .map *.map snapshots \
	*.exe obj* *.o csrc *.csv work \
	dataset.asdb  library.cfg vsimsa.cfg \
	*.h

############ TEST build ###############################

# Build program.hex from RUST executable
program.hex: key_manifest_pk_hash_val.hex owner_pk_hash_val.hex fw_update.hex $(TEST_DIR)/$(TESTNAME).extracted $(TEST_DIR)/$(TESTNAME)
	@-echo "Building program.hex from $(TESTNAME) using Crypto Test rules for pre-compiled RUST executables"
	$(GCC_PREFIX)-objcopy -I binary -O verilog --pad-to 0x8000 --gap-fill 0xFF --no-change-warnings $(TEST_DIR)/$(TESTNAME) program.hex
	du -b $(TEST_DIR)/$(TESTNAME) | cut -f1 > $(TESTNAME).size

fw_update.hex: $(TEST_DIR)/$(TESTNAME).extracted $(TEST_DIR)/$(TESTNAME_fw)
	@-echo "Building fw_update.hex from $(TESTNAME_fw) using binary objcopy pre-compiled RUST package"
	$(GCC_PREFIX)-objcopy -I binary -O verilog --pad-to 0x20000 --gap-fill 0xFF --no-change-warnings $(TEST_DIR)/$(TESTNAME_fw) fw_update.hex
	du -b $(TEST_DIR)/$(TESTNAME_fw) | cut -f1 > fw_update.size

# Extract public keys from ROM binary and dump as hex values
key_manifest_pk_hash_val.hex: key_manifest_pk_val.bin
	sha384sum key_manifest_pk_val.bin | sed 's,\s\+\S\+$$,,' > key_manifest_pk_hash_val.hex

key_manifest_pk_val.bin: $(TEST_DIR)/$(TESTNAME).extracted
	dd ibs=1 obs=1 if=$(TEST_DIR)/$(TESTNAME_fw) of=key_manifest_pk_val.bin skip=$(KEY_MANIFEST_ECC_PK_ROM_OFFSET) count=$(KEY_MANIFEST_PK_LENGTH)

owner_pk_hash_val.hex: owner_pk_val.bin
	sha384sum owner_pk_val.bin | sed 's,\s\+\S\+$$,,' > owner_pk_hash_val.hex

owner_pk_val.bin: $(TEST_DIR)/$(TESTNAME).extracted
	dd ibs=1 obs=1 if=$(TEST_DIR)/$(TESTNAME_fw) of=owner_pk_val.bin skip=$(OWNER_ECC_PK_ROM_OFFSET) count=$(OWNER_PK_LENGTH)

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

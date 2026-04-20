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

# Define test name
TESTNAME ?= fw_test_rom
TESTNAME_fw = $(TESTNAME)_fw
TEST_DIR = $(CALIPTRA_ROOT)/src/integration/test_suites/$(TESTNAME)

VPATH = $(TEST_DIR) $(BUILD_DIR)

# Offset calculations for fetching keys from ROM image
KEY_MANIFEST_ECC_PK_COUNT      = 1
KEY_MANIFEST_ECC_PK_SIZE       = 196
KEY_MANIFEST_ECC_PK_ROM_OFFSET = 12
KEY_MANIFEST_ECC_PK_LENGTH     = $(shell bc <<< "$(KEY_MANIFEST_ECC_PK_COUNT)*$(KEY_MANIFEST_ECC_PK_SIZE)")

KEY_MANIFEST_PQC_PK_COUNT      = 1
KEY_MANIFEST_PQC_PK_SIZE       = 1540
KEY_MANIFEST_PQC_PK_ROM_OFFSET = $(shell bc <<< "$(KEY_MANIFEST_ECC_PK_ROM_OFFSET) + $(KEY_MANIFEST_ECC_PK_COUNT)*$(KEY_MANIFEST_ECC_PK_SIZE)")
KEY_MANIFEST_PQC_PK_LENGTH     = $(shell bc <<< "$(KEY_MANIFEST_PQC_PK_COUNT)*$(KEY_MANIFEST_PQC_PK_SIZE)")

KEY_MANIFEST_PK_LENGTH         = $(shell bc <<< "$(KEY_MANIFEST_PQC_PK_LENGTH) + $(KEY_MANIFEST_ECC_PK_LENGTH)")

OWNER_ECC_PK_SIZE              = 96
OWNER_ECC_PK_ROM_OFFSET        = 9168
OWNER_PQC_PK_SIZE              = 2592
OWNER_PQC_PK_ROM_OFFSET        = $(shell bc <<< "$(OWNER_ECC_PK_ROM_OFFSET) + $(OWNER_ECC_PK_SIZE)")

OWNER_PK_LENGTH                = $(shell bc <<< "$(OWNER_PQC_PK_SIZE) + $(OWNER_ECC_PK_SIZE)")

# Targets
all: program.hex

clean:
	rm -rf *.log *.s *.hex *.dis *.size *.tbl .map *.map snapshots \
	*.exe obj* *.o csrc *.csv work \
	dataset.asdb  library.cfg vsimsa.cfg \
	*.h

############ TEST build ###############################

# Build program.hex from RUST executable
program.hex: vendor_pk_hash_val.hex owner_pk_hash_val.hex fw_update.hex $(TEST_DIR)/$(TESTNAME) $(TEST_DIR)/$(TESTNAME_fw)
	@-echo "Building program.hex from $(TESTNAME) using Crypto Test rules for pre-compiled RUST executables"
	$(GCC_PREFIX)-objcopy -I binary -O verilog --pad-to 0xC000 --gap-fill 0xFF --no-change-warnings $(TEST_DIR)/$(TESTNAME) program.hex
	du -b $(TEST_DIR)/$(TESTNAME) | cut -f1 > $(TESTNAME).size

fw_update.hex: $(TEST_DIR)/$(TESTNAME) $(TEST_DIR)/$(TESTNAME_fw)
	@-echo "Building fw_update.hex from $(TESTNAME_fw) using binary objcopy pre-compiled RUST package"
	$(GCC_PREFIX)-objcopy -I binary -O verilog --pad-to 0x20000 --gap-fill 0xFF --no-change-warnings $(TEST_DIR)/$(TESTNAME_fw) fw_update.hex
	du -b $(TEST_DIR)/$(TESTNAME_fw) | cut -f1 > fw_update.size

# Extract public keys from ROM binary and dump as hex values
vendor_pk_hash_val.hex: vendor_pk_val.bin
	sha384sum vendor_pk_val.bin | sed 's,\s\+\S\+$$,,' > vendor_pk_hash_val.hex

vendor_pk_val.bin: $(TEST_DIR)/$(TESTNAME_fw)
	dd ibs=1 obs=1 if=$(TEST_DIR)/$(TESTNAME_fw) of=vendor_pk_val.bin skip=$(KEY_MANIFEST_ECC_PK_ROM_OFFSET) count=$(KEY_MANIFEST_PK_LENGTH)

owner_pk_hash_val.hex: owner_pk_val.bin
	sha384sum owner_pk_val.bin | sed 's,\s\+\S\+$$,,' > owner_pk_hash_val.hex

owner_pk_val.bin: $(TEST_DIR)/$(TESTNAME_fw)
	dd ibs=1 obs=1 if=$(TEST_DIR)/$(TESTNAME_fw) of=owner_pk_val.bin skip=$(OWNER_ECC_PK_ROM_OFFSET) count=$(OWNER_PK_LENGTH)

# ROM and FW binaries must already be present. For pipeline regressions, these
# are pre-fetched by fetch_caliptra_sw_release.sh. For releases, they are
# included in the repository.
$(TEST_DIR)/$(TESTNAME):
	@echo "ERROR: ROM binary not found at $@"
	echo "For pipeline use, ensure fetch_caliptra_sw_release.sh runs before this step."
	echo "For local use, place caliptra-rom-with-log.bin at $@"
	exit 1

$(TEST_DIR)/$(TESTNAME_fw):
	@echo "ERROR: FW binary not found at $@"
	echo "For pipeline use, ensure fetch_caliptra_sw_release.sh runs before this step."
	echo "For local use, place image-bundle-mldsa.bin at $@"
	exit 1

help:
	@echo Make sure the environment variable RV_ROOT is set.
	echo Possible targets: help clean all program.hex

.PHONY: help clean

.ONESHELL:

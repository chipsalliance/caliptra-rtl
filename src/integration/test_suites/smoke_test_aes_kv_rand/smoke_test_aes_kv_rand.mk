# SPDX-License-Identifier: Apache-2.0
#
# Link aes library (not in global COMP_LIB_NAMES to save ROM space)
OFILES += aes.o
AUX_LIB_DIR += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/aes
AUX_HEADER_FILES += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/aes/aes.h

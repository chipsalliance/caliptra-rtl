# SPDX-License-Identifier: Apache-2.0
#
# aes is not in the global COMP_LIB_NAMES (keeps aes.o out of every test's image
# to save ROM). This test calls the aes.c API, so opt the object + header back in
# here only.
OFILES += aes.o
AUX_LIB_DIR += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/aes
AUX_HEADER_FILES += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/aes/aes.h

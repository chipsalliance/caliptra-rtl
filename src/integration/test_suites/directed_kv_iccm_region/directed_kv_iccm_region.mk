# Link kv_boot_flow library (not in global COMP_LIB_NAMES to save ROM space)
OFILES += kv_boot_flow.o
AUX_LIB_DIR += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/kv_boot_flow
AUX_HEADER_FILES += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/kv_boot_flow/kv_boot_flow.h

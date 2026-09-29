# smoke_test_ras exercises RISC-V exception capture (ICCM/DCCM uncorrectable ECC
# faults), so it opts into the shared trap handler's exception bookkeeping. This
# define reaches both smoke_test_ras.c and the shared caliptra_isr.c compile,
# enabling rv_exception_struct_s + the exc_flag recording path.
TEST_CFLAGS += -DRV_EXCEPTION_STRUCT

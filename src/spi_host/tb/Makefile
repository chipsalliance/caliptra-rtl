VERILATOR = verilator

IPNAME = spi_host
IPDIR = $(CALIPTRA_ROOT)/src/$(IPNAME)
TBFILES = $(IPDIR)/config/$(IPNAME).vf
VERILATOR_LINT_FILES = $(IPDIR)/config/$(IPNAME).vlt

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

verilator-build: $(TBFILES) $(VERILATOR_LINT_FILES) test_$(IPNAME)_tb.cpp
	$(VERILATOR) --cc \
		--timing \
		--timescale 1ns/1ps \
		-f $(TBFILES) --top-module $(IPNAME)_tb \
    -f $(VERILATOR_LINT_FILES) \
		-exe test_$(IPNAME)_tb.cpp \
		--trace-fst --trace-structs
	cp test_$(IPNAME)_tb.cpp obj_dir/
	$(MAKE) -j -e -C obj_dir/ -f V$(IPNAME)_tb.mk $(VERILATOR_MAKE_FLAGS) VM_PARALLEL_BUILDS=1
	touch verilator-build

############ TEST Simulation ###############################

verilator: verilator-build
	./obj_dir/V$(IPNAME)_tb

run: verilator

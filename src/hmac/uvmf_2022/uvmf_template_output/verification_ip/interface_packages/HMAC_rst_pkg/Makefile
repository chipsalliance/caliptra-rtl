# hmac_rst interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

hmac_rst_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/HMAC_rst_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/HMAC_rst_pkg/HMAC_rst_filelist_hvl.f 

hmac_rst_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/HMAC_rst_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/HMAC_rst_pkg/HMAC_rst_filelist_hdl.f 

hmac_rst_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/HMAC_rst_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/HMAC_rst_pkg/HMAC_rst_filelist_xrtl.f 

COMP_hmac_rst_PKG_TGT_0 = q_comp_hmac_rst_pkg
COMP_hmac_rst_PKG_TGT_1 = v_comp_hmac_rst_pkg
COMP_hmac_rst_PKG_TGT = $(COMP_hmac_rst_PKG_TGT_$(USE_VELOCE))

comp_hmac_rst_pkg: $(COMP_hmac_rst_PKG_TGT) 

# Backward-compatible aliases (top-level sim/Makefile uses the capitalized
# HMAC_rst target names because the interface package name is HMAC_rst).
comp_HMAC_rst_pkg:   comp_hmac_rst_pkg
q_comp_HMAC_rst_pkg: q_comp_hmac_rst_pkg
v_comp_HMAC_rst_pkg: v_comp_hmac_rst_pkg

q_comp_hmac_rst_pkg:
	$(HDL_COMP_CMD) $(hmac_rst_PKG_HDL)
	$(HVL_COMP_CMD) $(hmac_rst_PKG)
	$(HDL_COMP_CMD) $(hmac_rst_PKG_XRTL) 

v_comp_hmac_rst_pkg:
	$(HVL_COMP_CMD) $(hmac_rst_PKG_HDL)
	$(HVL_COMP_CMD) $(hmac_rst_PKG)
	$(VELANALYZE_CMD) $(hmac_rst_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(hmac_rst_PKG) 
	$(HDL_COMP_CMD) $(hmac_rst_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export hmac_rst_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/HMAC_rst_pkg/dpi

C_FILE_COMPILE_LIST_hmac_rst_pkg	= \

O_FILE_COMPILE_LIST_hmac_rst_pkg = $(notdir $(C_FILE_COMPILE_LIST_hmac_rst_pkg:.c=.o))

GCC_COMP_ARGS_hmac_rst_pkg	+= -I$(hmac_rst_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_hmac_rst_pkg	+= $(hmac_rst_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_hmac_rst_pkg	+= \
	 \
 	-o .so

comp_hmac_rst_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_hmac_rst_pkg) $(C_FILE_COMPILE_LIST_hmac_rst_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_hmac_rst_pkg) $(O_FILE_COMPILE_LIST_hmac_rst_pkg)
	@echo "--------------------------------"


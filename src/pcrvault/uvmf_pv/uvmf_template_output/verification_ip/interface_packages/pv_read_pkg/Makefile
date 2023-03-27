# pv_read interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

pv_read_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/pv_read_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/pv_read_pkg/pv_read_filelist_hvl.f 

pv_read_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/pv_read_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/pv_read_pkg/pv_read_filelist_hdl.f 

pv_read_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/pv_read_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/pv_read_pkg/pv_read_filelist_xrtl.f 

COMP_pv_read_PKG_TGT_0 = q_comp_pv_read_pkg
COMP_pv_read_PKG_TGT_1 = v_comp_pv_read_pkg
COMP_pv_read_PKG_TGT = $(COMP_pv_read_PKG_TGT_$(USE_VELOCE))

comp_pv_read_pkg: $(COMP_pv_read_PKG_TGT) 

q_comp_pv_read_pkg:
	$(HDL_COMP_CMD) $(pv_read_PKG_HDL)
	$(HVL_COMP_CMD) $(pv_read_PKG)
	$(HDL_COMP_CMD) $(pv_read_PKG_XRTL) 

v_comp_pv_read_pkg:
	$(HVL_COMP_CMD) $(pv_read_PKG_HDL)
	$(HVL_COMP_CMD) $(pv_read_PKG)
	$(VELANALYZE_CMD) $(pv_read_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(pv_read_PKG) 
	$(HDL_COMP_CMD) $(pv_read_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export pv_read_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/pv_read_pkg/dpi

C_FILE_COMPILE_LIST_pv_read_pkg	= \

O_FILE_COMPILE_LIST_pv_read_pkg = $(notdir $(C_FILE_COMPILE_LIST_pv_read_pkg:.c=.o))

GCC_COMP_ARGS_pv_read_pkg	+= -I$(pv_read_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_pv_read_pkg	+= $(pv_read_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_pv_read_pkg	+= \
	 \
 	-o .so

comp_pv_read_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_pv_read_pkg) $(C_FILE_COMPILE_LIST_pv_read_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_pv_read_pkg) $(O_FILE_COMPILE_LIST_pv_read_pkg)
	@echo "--------------------------------"


# core_axi_write_if interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

core_axi_write_if_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_if_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_if_pkg/core_axi_write_if_filelist_hvl.f 

core_axi_write_if_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_if_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_if_pkg/core_axi_write_if_filelist_hdl.f 

core_axi_write_if_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_if_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_if_pkg/core_axi_write_if_filelist_xrtl.f 

COMP_core_axi_write_if_PKG_TGT_0 = q_comp_core_axi_write_if_pkg
COMP_core_axi_write_if_PKG_TGT_1 = v_comp_core_axi_write_if_pkg
COMP_core_axi_write_if_PKG_TGT = $(COMP_core_axi_write_if_PKG_TGT_$(USE_VELOCE))

comp_core_axi_write_if_pkg: $(COMP_core_axi_write_if_PKG_TGT) 

q_comp_core_axi_write_if_pkg:
	$(HDL_COMP_CMD) $(core_axi_write_if_PKG_HDL)
	$(HVL_COMP_CMD) $(core_axi_write_if_PKG)
	$(HDL_COMP_CMD) $(core_axi_write_if_PKG_XRTL) 

v_comp_core_axi_write_if_pkg:
	$(HVL_COMP_CMD) $(core_axi_write_if_PKG_HDL)
	$(HVL_COMP_CMD) $(core_axi_write_if_PKG)
	$(VELANALYZE_CMD) $(core_axi_write_if_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(core_axi_write_if_PKG) 
	$(HDL_COMP_CMD) $(core_axi_write_if_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export core_axi_write_if_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/core_axi_write_if_pkg/dpi

C_FILE_COMPILE_LIST_core_axi_write_if_pkg	= \

O_FILE_COMPILE_LIST_core_axi_write_if_pkg = $(notdir $(C_FILE_COMPILE_LIST_core_axi_write_if_pkg:.c=.o))

GCC_COMP_ARGS_core_axi_write_if_pkg	+= -I$(core_axi_write_if_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_core_axi_write_if_pkg	+= $(core_axi_write_if_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_core_axi_write_if_pkg	+= \
	 \
 	-o .so

comp_core_axi_write_if_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_core_axi_write_if_pkg) $(C_FILE_COMPILE_LIST_core_axi_write_if_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_core_axi_write_if_pkg) $(O_FILE_COMPILE_LIST_core_axi_write_if_pkg)
	@echo "--------------------------------"


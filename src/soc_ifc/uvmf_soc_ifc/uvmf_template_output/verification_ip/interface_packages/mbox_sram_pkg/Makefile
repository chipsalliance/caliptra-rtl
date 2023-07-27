# mbox_sram interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

mbox_sram_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg/mbox_sram_filelist_hvl.f 

mbox_sram_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg/mbox_sram_filelist_hdl.f 

mbox_sram_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg/mbox_sram_filelist_xrtl.f 

COMP_mbox_sram_PKG_TGT_0 = q_comp_mbox_sram_pkg
COMP_mbox_sram_PKG_TGT_1 = v_comp_mbox_sram_pkg
COMP_mbox_sram_PKG_TGT = $(COMP_mbox_sram_PKG_TGT_$(USE_VELOCE))

comp_mbox_sram_pkg: $(COMP_mbox_sram_PKG_TGT) 

q_comp_mbox_sram_pkg:
	$(HDL_COMP_CMD) $(mbox_sram_PKG_HDL)
	$(HVL_COMP_CMD) $(mbox_sram_PKG)
	$(HDL_COMP_CMD) $(mbox_sram_PKG_XRTL) 

v_comp_mbox_sram_pkg:
	$(HVL_COMP_CMD) $(mbox_sram_PKG_HDL)
	$(HVL_COMP_CMD) $(mbox_sram_PKG)
	$(VELANALYZE_CMD) $(mbox_sram_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(mbox_sram_PKG) 
	$(HDL_COMP_CMD) $(mbox_sram_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export mbox_sram_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/mbox_sram_pkg/dpi

C_FILE_COMPILE_LIST_mbox_sram_pkg	= \

O_FILE_COMPILE_LIST_mbox_sram_pkg = $(notdir $(C_FILE_COMPILE_LIST_mbox_sram_pkg:.c=.o))

GCC_COMP_ARGS_mbox_sram_pkg	+= -I$(mbox_sram_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_mbox_sram_pkg	+= $(mbox_sram_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_mbox_sram_pkg	+= \
	 \
 	-o .so

comp_mbox_sram_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_mbox_sram_pkg) $(C_FILE_COMPILE_LIST_mbox_sram_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_mbox_sram_pkg) $(O_FILE_COMPILE_LIST_mbox_sram_pkg)
	@echo "--------------------------------"


# AES_out interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

AES_out_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/AES_out_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/AES_out_pkg/AES_out_filelist_hvl.f 

AES_out_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/AES_out_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/AES_out_pkg/AES_out_filelist_hdl.f 

AES_out_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/AES_out_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/AES_out_pkg/AES_out_filelist_xrtl.f 

COMP_AES_out_PKG_TGT_0 = q_comp_AES_out_pkg
COMP_AES_out_PKG_TGT_1 = v_comp_AES_out_pkg
COMP_AES_out_PKG_TGT = $(COMP_AES_out_PKG_TGT_$(USE_VELOCE))

comp_AES_out_pkg: $(COMP_AES_out_PKG_TGT) 

q_comp_AES_out_pkg:
	$(HDL_COMP_CMD) $(AES_out_PKG_HDL)
	$(HVL_COMP_CMD) $(AES_out_PKG)
	$(HDL_COMP_CMD) $(AES_out_PKG_XRTL) 

v_comp_AES_out_pkg:
	$(HVL_COMP_CMD) $(AES_out_PKG_HDL)
	$(HVL_COMP_CMD) $(AES_out_PKG)
	$(VELANALYZE_CMD) $(AES_out_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(AES_out_PKG) 
	$(HDL_COMP_CMD) $(AES_out_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export AES_out_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/AES_out_pkg/dpi

C_FILE_COMPILE_LIST_AES_out_pkg	= \

O_FILE_COMPILE_LIST_AES_out_pkg = $(notdir $(C_FILE_COMPILE_LIST_AES_out_pkg:.c=.o))

GCC_COMP_ARGS_AES_out_pkg	+= -I$(AES_out_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_AES_out_pkg	+= $(AES_out_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_AES_out_pkg	+= \
	 \
 	-o .so

comp_AES_out_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_AES_out_pkg) $(C_FILE_COMPILE_LIST_AES_out_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_AES_out_pkg) $(O_FILE_COMPILE_LIST_AES_out_pkg)
	@echo "--------------------------------"


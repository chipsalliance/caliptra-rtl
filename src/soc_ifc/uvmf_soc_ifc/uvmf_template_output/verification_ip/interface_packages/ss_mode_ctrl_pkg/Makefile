# ss_mode_ctrl interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

ss_mode_ctrl_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg/ss_mode_ctrl_filelist_hvl.f 

ss_mode_ctrl_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg/ss_mode_ctrl_filelist_hdl.f 

ss_mode_ctrl_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg/ss_mode_ctrl_filelist_xrtl.f 

COMP_ss_mode_ctrl_PKG_TGT_0 = q_comp_ss_mode_ctrl_pkg
COMP_ss_mode_ctrl_PKG_TGT_1 = v_comp_ss_mode_ctrl_pkg
COMP_ss_mode_ctrl_PKG_TGT = $(COMP_ss_mode_ctrl_PKG_TGT_$(USE_VELOCE))

comp_ss_mode_ctrl_pkg: $(COMP_ss_mode_ctrl_PKG_TGT) 

q_comp_ss_mode_ctrl_pkg:
	$(HDL_COMP_CMD) $(ss_mode_ctrl_PKG_HDL)
	$(HVL_COMP_CMD) $(ss_mode_ctrl_PKG)
	$(HDL_COMP_CMD) $(ss_mode_ctrl_PKG_XRTL) 

v_comp_ss_mode_ctrl_pkg:
	$(HVL_COMP_CMD) $(ss_mode_ctrl_PKG_HDL)
	$(HVL_COMP_CMD) $(ss_mode_ctrl_PKG)
	$(VELANALYZE_CMD) $(ss_mode_ctrl_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(ss_mode_ctrl_PKG) 
	$(HDL_COMP_CMD) $(ss_mode_ctrl_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export ss_mode_ctrl_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/ss_mode_ctrl_pkg/dpi

C_FILE_COMPILE_LIST_ss_mode_ctrl_pkg	= \

O_FILE_COMPILE_LIST_ss_mode_ctrl_pkg = $(notdir $(C_FILE_COMPILE_LIST_ss_mode_ctrl_pkg:.c=.o))

GCC_COMP_ARGS_ss_mode_ctrl_pkg	+= -I$(ss_mode_ctrl_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_ss_mode_ctrl_pkg	+= $(ss_mode_ctrl_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_ss_mode_ctrl_pkg	+= \
	 \
 	-o .so

comp_ss_mode_ctrl_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_ss_mode_ctrl_pkg) $(C_FILE_COMPILE_LIST_ss_mode_ctrl_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_ss_mode_ctrl_pkg) $(O_FILE_COMPILE_LIST_ss_mode_ctrl_pkg)
	@echo "--------------------------------"


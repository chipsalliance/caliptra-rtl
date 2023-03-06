# SHA512_in interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

SHA512_in_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/SHA512_in_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/SHA512_in_pkg/SHA512_in_filelist_hvl.f 

SHA512_in_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/SHA512_in_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/SHA512_in_pkg/SHA512_in_filelist_hdl.f 

SHA512_in_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/SHA512_in_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/SHA512_in_pkg/SHA512_in_filelist_xrtl.f 

COMP_SHA512_in_PKG_TGT_0 = q_comp_SHA512_in_pkg
COMP_SHA512_in_PKG_TGT_1 = v_comp_SHA512_in_pkg
COMP_SHA512_in_PKG_TGT = $(COMP_SHA512_in_PKG_TGT_$(USE_VELOCE))

comp_SHA512_in_pkg: $(COMP_SHA512_in_PKG_TGT) 

q_comp_SHA512_in_pkg:
	$(HDL_COMP_CMD) $(SHA512_in_PKG_HDL)
	$(HVL_COMP_CMD) $(SHA512_in_PKG)
	$(HDL_COMP_CMD) $(SHA512_in_PKG_XRTL) 

v_comp_SHA512_in_pkg:
	$(HVL_COMP_CMD) $(SHA512_in_PKG_HDL)
	$(HVL_COMP_CMD) $(SHA512_in_PKG)
	$(VELANALYZE_CMD) $(SHA512_in_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(SHA512_in_PKG) 
	$(HDL_COMP_CMD) $(SHA512_in_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export SHA512_in_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/SHA512_in_pkg/dpi

C_FILE_COMPILE_LIST_SHA512_in_pkg	= \

O_FILE_COMPILE_LIST_SHA512_in_pkg = $(notdir $(C_FILE_COMPILE_LIST_SHA512_in_pkg:.c=.o))

GCC_COMP_ARGS_SHA512_in_pkg	+= -I$(SHA512_in_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_SHA512_in_pkg	+= $(SHA512_in_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_SHA512_in_pkg	+= \
	 \
 	-o .so

comp_SHA512_in_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_SHA512_in_pkg) $(C_FILE_COMPILE_LIST_SHA512_in_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_SHA512_in_pkg) $(O_FILE_COMPILE_LIST_SHA512_in_pkg)
	@echo "--------------------------------"


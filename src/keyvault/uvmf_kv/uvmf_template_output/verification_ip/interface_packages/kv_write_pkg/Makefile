# kv_write interface packages source
# pragma uvmf custom additional begin
# pragma uvmf custom additional end

kv_write_PKG         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/kv_write_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/kv_write_pkg/kv_write_filelist_hvl.f 

kv_write_PKG_HDL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/kv_write_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/kv_write_pkg/kv_write_filelist_hdl.f 

kv_write_PKG_XRTL         = \
	+incdir+$(UVMF_VIP_LIBRARY_HOME)/interface_packages/kv_write_pkg \
	-F $(UVMF_VIP_LIBRARY_HOME)/interface_packages/kv_write_pkg/kv_write_filelist_xrtl.f 

COMP_kv_write_PKG_TGT_0 = q_comp_kv_write_pkg
COMP_kv_write_PKG_TGT_1 = v_comp_kv_write_pkg
COMP_kv_write_PKG_TGT = $(COMP_kv_write_PKG_TGT_$(USE_VELOCE))

comp_kv_write_pkg: $(COMP_kv_write_PKG_TGT) 

q_comp_kv_write_pkg:
	$(HDL_COMP_CMD) $(kv_write_PKG_HDL)
	$(HVL_COMP_CMD) $(kv_write_PKG)
	$(HDL_COMP_CMD) $(kv_write_PKG_XRTL) 

v_comp_kv_write_pkg:
	$(HVL_COMP_CMD) $(kv_write_PKG_HDL)
	$(HVL_COMP_CMD) $(kv_write_PKG)
	$(VELANALYZE_CMD) $(kv_write_PKG_HDL) 
	$(VELANALYZE_HVL_CMD) $(kv_write_PKG) 
	$(HDL_COMP_CMD) $(kv_write_PKG_XRTL)

ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export kv_write_IF_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/interface_packages/kv_write_pkg/dpi

C_FILE_COMPILE_LIST_kv_write_pkg	= \

O_FILE_COMPILE_LIST_kv_write_pkg = $(notdir $(C_FILE_COMPILE_LIST_kv_write_pkg:.c=.o))

GCC_COMP_ARGS_kv_write_pkg	+= -I$(kv_write_IF_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_kv_write_pkg	+= $(kv_write_IF_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_kv_write_pkg	+= \
	 \
 	-o .so

comp_kv_write_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Interface C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_kv_write_pkg) $(C_FILE_COMPILE_LIST_kv_write_pkg)
	@echo "--------------------------------"
	@echo "Linking Interface C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_kv_write_pkg) $(O_FILE_COMPILE_LIST_kv_write_pkg)
	@echo "--------------------------------"


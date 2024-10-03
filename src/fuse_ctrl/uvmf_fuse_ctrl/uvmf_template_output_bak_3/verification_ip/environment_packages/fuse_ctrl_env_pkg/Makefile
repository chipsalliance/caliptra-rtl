# fuse_ctrl environment packages source and make target

# pragma uvmf custom additional begin
# pragma uvmf custom additional end

# Include all requisite sub-environment package targets for this bench

fuse_ctrl_ENV_PKG =\
		 $(UVMF_VIP_LIBRARY_HOME)/environment_packages/fuse_ctrl_env_pkg/fuse_ctrl_env_pkg.sv

COMP_fuse_ctrl_PKG_TGT_0 = q_comp_fuse_ctrl_env_pkg
COMP_fuse_ctrl_PKG_TGT_1 = v_comp_fuse_ctrl_env_pkg
COMP_fuse_ctrl_PKG_TGT = $(COMP_fuse_ctrl_PKG_TGT_$(USE_VELOCE))

comp_fuse_ctrl_env_pkg: $(COMP_fuse_ctrl_PKG_TGT) 

q_comp_fuse_ctrl_env_pkg:   
		$(HVL_COMP_CMD) +incdir+$(UVMF_VIP_LIBRARY_HOME)/environment_packages/fuse_ctrl_env_pkg $(fuse_ctrl_ENV_PKG)

v_comp_fuse_ctrl_env_pkg: q_comp_fuse_ctrl_env_pkg
	$(VELANALYZE_HVL_CMD) +incdir+$(UVMF_VIP_LIBRARY_HOME)/environment_packages/fuse_ctrl_env_pkg $(fuse_ctrl_ENV_PKG)



ifeq ($(MTI_VCO_MODE),64)
  GCC_COMP_ARCH = -m64
else
  GCC_COMP_ARCH = -m32
endif

export fuse_ctrl_ENV_DPI_SRC ?= $(UVMF_VIP_LIBRARY_HOME)/environment_packages/fuse_ctrl_env_pkg/dpi

C_FILE_COMPILE_LIST_fuse_ctrl_env_pkg	= \

O_FILE_COMPILE_LIST_fuse_ctrl_env_pkg = $(notdir $(C_FILE_COMPILE_LIST_fuse_ctrl_env_pkg:.c=.o))

GCC_COMP_ARGS_fuse_ctrl_env_pkg	+= -I$(fuse_ctrl_ENV_DPI_SRC) \
	-fPIC 

GCC_COMP_ARGS_fuse_ctrl_env_pkg	+= $(fuse_ctrl_ENV_GCC_COMP_ARGUMENTS)

GCC_LINK_ARGS_fuse_ctrl_env_pkg	+= \
	 \
 	-o .so

comp_fuse_ctrl_env_pkg_c_files:
	@echo "--------------------------------"
	@echo "Compiling Environment C source"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_COMP_ARGS_fuse_ctrl_env_pkg) $(C_FILE_COMPILE_LIST_fuse_ctrl_env_pkg)
	@echo "--------------------------------"
	@echo "Linking Environment C objects into a shared object"
	@echo "--------------------------------"
	gcc $(GCC_COMP_ARCH) $(GCC_LINK_ARGS_fuse_ctrl_env_pkg) $(O_FILE_COMPILE_LIST_fuse_ctrl_env_pkg)
	@echo "--------------------------------"


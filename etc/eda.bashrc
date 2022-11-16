#################################################################
# Tool versions are controlled by an eda-profile.bashrc file in #
# Base_Tools/common_tools and Base_Verification/tools under the #
# ms-tsd organization in Azure DevOps.                          #
#                                                               #
# Listing these two repos as a dependency in your comodule file #
# gets you all the tools and their versions setup for free.     #
# You can override these versions below if necessary.           #
#################################################################

#############################
# Base_Tools/common_tools   #
#############################
# xcelium
# vcs-mx
# verdi
# vc_static
# realintent (RTL Lint)
# gnu
# UVM_ML
# questa
# questa_cdc
# and likely others.

#############################
# Base Verification/tools   #
#############################
# dvt (DV Lint)
# PLUSARGS_DEF_FILE
# REGRESS_PATCH_CONFIG

# Make gcc 8.2.0 take priority over 5.2.0 as it's needed by verification client.
module load tools/gnu/gcc/8.2.0

# VCS Timescale override Repo config
module prepend-path PB_CMD_CONFIGS "${WORKSPACE}/Caliptra/config/pb_cmd_config_local"

# RTL Lint
module load tools/realintent/license/2019.01
module load tools/realintent/versions/2019.A.p15.2020_12_18

# Synopsys
module load tools/synopsys/license/2018.12
module load tools/synopsys/vcs-mx/2020.12-SP2-2
module load tools/synopsys/verdi/2020.12-SP2-2
module load tools/synopsys/vc_static/2020.03-SP2-4
module load tools/synopsys/zebu/2020.03-SP1-1-B4_nfs_fix_08172021
module load tools/synopsys/zebu_ip_root/2021.06-1_1223
export SNPS_VCS_INTERNAL_SR_NO_EXIT=1
export VCS_LICENSE_WAIT=1

# Mentor Questa CDC
module load tools/mentor/questa/2021.2_1
module load tools/mentor/questa_cdc/2021.2_1

# Provides $QUESTA_MVC_HOME
module load tools/mentor/questa_vip/2022.2/x86_64_gcc-6.7.2_vcs

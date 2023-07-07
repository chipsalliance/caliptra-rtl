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

# VCS Timescale override Repo config
module prepend-path PB_CMD_CONFIGS "${WORKSPACE}/Caliptra/config/pb_cmd_config_local"

# Smart CLI Expansions
module prepend-path PB_CMD_SMART_ROOTS "${WORKSPACE}/Caliptra/config/smartexp_roots"

# Synopsys
module load tools/synopsys/zebu/2020.03-SP1-1-B4_nfs_fix_08172021
module load tools/synopsys/zebu_ip_root/2021.06-1_1223
export VCS_LICENSE_WAIT=1

# Provides $QUESTA_MVC_HOME
module load tools/mentor/questa_vip/2022.2/x86_64_gcc-6.7.2_vcs

# Verilator is loaded as EDA tool when launching sims through 'submit'
module load tools/verilator/5.012

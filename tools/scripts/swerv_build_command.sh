########################################################################
# How to run:
#   1. download the SweRV EL2 repo to some local directory:
#       mkdir my/local/dir
#       cd my/local/dir
#       git clone https://github.com/chipsalliance/Cores-SweRV-EL2
#       cd Cores-SweRV-EL2
#   2. in the shell, run:
#       export RV_ROOT=${PWD}
#   3. edit Cores-SweRV-EL2/configs/swerv.config, line 841
#       change
#          "reset_vec"             => "0x80000000",                        # Testbench, Overridable
#       to
#          "reset_vec"             => "0x00000000",                        # Testbench, Overridable
#   4. Run this script with 1 argument : name of snapshot to use
#        source <path/to/script>/swerv_build_command.sh <name_of_snapshot>
#   5. AFTER this script completes, you can merge contents into Caliptra repo
#      (Output files will be located in $RV_ROOT/snapshots/<name_of_snapshot>)
########################################################################
if [[ -z ${RV_ROOT+"empty"} ]]; then
    echo "Error! Must define environment variable RV_ROOT to point to swerv repo";
    exit 1;
fi
if [[ $# -ne 1 ]]; then
    echo "Error! Give 1 argument for snapshot name";
    exit 2;
fi
$RV_ROOT/configs/swerv.config    \
-target=default_ahb              \
--iccm_region=0x4                \
-set=ret_stack_size=8            \
-set=btb_enable=1                \
-set=btb_fullya=0                \
-set=btb_size=512                \
-set=bht_size=512                \
-set=div_bit=4                   \
-set=div_new=1                   \
-set=dccm_enable=1               \
-set=dccm_num_banks=4            \
-set=dccm_region=0x4             \
-set=dccm_offset=0x40000         \
-set=dccm_size=128               \
-set=dma_buf_depth=5             \
-set=fast_interrupt_redirect=1   \
-set=iccm_enable=1               \
-set=icache_enable=0             \
-set=icache_waypack=1            \
-set=icache_ecc=1                \
-set=icache_size=16              \
-set=icache_2banks=1             \
-set=icache_num_ways=2           \
-set=icache_bypass_enable=1      \
-set=icache_num_bypass=2         \
-set=icache_num_tag_bypass=2     \
-set=icache_tag_bypass_enable=1  \
-set=iccm_offset=0x0             \
-set=iccm_size=128               \
-set=iccm_num_banks=4            \
-set=lsu_stbuf_depth=4           \
-set=lsu_num_nbload=4            \
-set=load_to_use_plus1=0         \
-set=pic_2cycle=0                \
-set=pic_region=0x5              \
-set=pic_offset=0                \
-set=pic_size=32                 \
-set=pic_total_int=31            \
-set=dma_buf_depth=5             \
-set=timer_legal_en=1            \
-set=bitmanip_zba=1              \
-set=bitmanip_zbb=1              \
-set=bitmanip_zbc=1              \
-set=bitmanip_zbe=0              \
-set=bitmanip_zbf=0              \
-set=bitmanip_zbp=0              \
-set=bitmanip_zbr=0              \
-set=bitmanip_zbs=1              \
-fpga_optimize=0                 \
-snapshot=$1
#-text_in_iccm=0

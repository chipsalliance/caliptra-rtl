# SPDX-License-Identifier: Apache-2.0
# 
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
########################################################################
# How to run:
#   1. download the VeeR EL2 repo to some local directory:
#       mkdir my/local/dir
#       cd my/local/dir
#       git clone https://github.com/chipsalliance/Cores-VeeR-EL2
#       cd Cores-VeeR-EL2
#   2. in the shell, run:
#       export RV_ROOT=${PWD}
#   3. Run this script with 1 argument : name of snapshot to use
#        source <path/to/script>/veer_build_command.sh <name_of_snapshot>
#   4. AFTER this script completes, you can merge contents into Caliptra repo
#      (Output files will be located in $RV_ROOT/snapshots/<name_of_snapshot>)
########################################################################
if [[ -z ${RV_ROOT+"empty"} ]]; then
    echo "Error! Must define environment variable RV_ROOT to point to veer repo";
    exit 1;
fi
if [[ $# -ne 1 ]]; then
    echo "Error! Give 1 argument for snapshot name";
    exit 2;
fi
$RV_ROOT/configs/veer.config    \
-target=default_ahb              \
-set=ret_stack_size=8            \
-set=btb_enable=1                \
-set=btb_fullya=0                \
-set=btb_size=512                \
-set=bht_size=512                \
-set=div_bit=4                   \
-set=div_new=1                   \
-set=dccm_enable=1               \
-set=dccm_num_banks=4            \
-set=dccm_region=0x5             \
-set=dccm_offset=0x00000         \
-set=dccm_size=128               \
-set=dma_buf_depth=5             \
-set=fast_interrupt_redirect=1   \
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
-set=iccm_enable=1               \
-set=iccm_num_banks=4            \
-set=iccm_region=0x4             \
-set=iccm_offset=0x0             \
-set=iccm_size=128               \
-set=lsu_stbuf_depth=4           \
-set=lsu_num_nbload=4            \
-set=load_to_use_plus1=0         \
-set=pic_2cycle=0                \
-set=pic_region=0x6              \
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
-set=pmp_entries=64              \
-set=reset_vec=0x00000000        \
-fpga_optimize=0                 \
-snapshot=$1
#-text_in_iccm=0

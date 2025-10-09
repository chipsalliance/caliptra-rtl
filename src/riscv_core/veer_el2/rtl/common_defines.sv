//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//********************************************************************************


// NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
// This is an automatically generated file by cwhitehead on Wed Oct  8 18:26:01 PDT 2025
//
// cmd:    veer -target=default_ahb -set=ret_stack_size=8 -set=btb_enable=1 -set=btb_fullya=0 -set=btb_size=512 -set=bht_size=512 -set=div_bit=4 -set=div_new=1 -set=dccm_enable=1 -set=dccm_num_banks=4 -set=dccm_region=0x5 -set=dccm_offset=0x00000 -set=dccm_size=256 -set=dma_buf_depth=5 -set=fast_interrupt_redirect=1 -set=icache_enable=0 -set=icache_waypack=1 -set=icache_ecc=1 -set=icache_size=16 -set=icache_2banks=1 -set=icache_num_ways=2 -set=icache_bypass_enable=1 -set=icache_num_bypass=2 -set=icache_num_tag_bypass=2 -set=icache_tag_bypass_enable=1 -set=iccm_enable=1 -set=iccm_num_banks=4 -set=iccm_region=0x4 -set=iccm_offset=0x0 -set=iccm_size=256 -set=lsu_stbuf_depth=4 -set=lsu_num_nbload=4 -set=load_to_use_plus1=0 -set=pic_2cycle=0 -set=pic_region=0x6 -set=pic_offset=0 -set=pic_size=32 -set=pic_total_int=31 -set=dma_buf_depth=5 -set=timer_legal_en=1 -set=bitmanip_zba=1 -set=bitmanip_zbb=1 -set=bitmanip_zbc=1 -set=bitmanip_zbe=0 -set=bitmanip_zbf=0 -set=bitmanip_zbp=0 -set=bitmanip_zbr=0 -set=bitmanip_zbs=1 -set=pmp_entries=64 -set=reset_vec=0x00000000 -fpga_optimize=0 -snapshot=Cores-VeeR-EL2 
//
`ifndef RV_COMMON_DEFINES
`define RV_COMMON_DEFINES

`define RV_ROOT ""
`define RV_BHT_ADDR_HI 9
`define RV_BHT_ADDR_LO 2
`define RV_BHT_ARRAY_DEPTH 256
`define RV_BHT_GHR_HASH_1 
`define RV_BHT_GHR_RANGE 7:0
`define RV_BHT_GHR_SIZE 8
`define RV_BHT_HASH_STRING {hashin[8+1:2]^ghr[8-1:0]}// cf2
`define RV_BHT_SIZE 512
`define RV_BTB_ADDR_HI 9
`define RV_BTB_ADDR_LO 2
`define RV_BTB_ARRAY_DEPTH 256
`define RV_BTB_BTAG_FOLD 0
`define RV_BTB_BTAG_SIZE 5
`define RV_BTB_ENABLE 1
`define RV_BTB_FOLD2_INDEX_HASH 0
`define RV_BTB_INDEX1_HI 9
`define RV_BTB_INDEX1_LO 2
`define RV_BTB_INDEX2_HI 17
`define RV_BTB_INDEX2_LO 10
`define RV_BTB_INDEX3_HI 25
`define RV_BTB_INDEX3_LO 18
`define RV_BTB_SIZE 512
`define RV_BTB_TOFFSET_SIZE 12
`define RV_BUS_PRTY_DEFAULT 2'h3
`define RV_DMA_BUS_ID 1
`define RV_DMA_BUS_PRTY 2
`define RV_DMA_BUS_TAG 1
`define RV_IFU_BUS_ID 1
`define RV_IFU_BUS_PRTY 2
`define RV_IFU_BUS_TAG 3
`define RV_LSU_BUS_ID 1
`define RV_LSU_BUS_PRTY 2
`define RV_LSU_BUS_TAG 3
`define RV_SB_BUS_ID 1
`define RV_SB_BUS_PRTY 2
`define RV_SB_BUS_TAG 1
`define RV_CONFIG_KEY 32'hdeadbeef
`define RV_BITMANIP_ZBA 1
`define RV_BITMANIP_ZBB 1
`define RV_BITMANIP_ZBC 1
`define RV_BITMANIP_ZBE 0
`define RV_BITMANIP_ZBF 0
`define RV_BITMANIP_ZBP 0
`define RV_BITMANIP_ZBR 0
`define RV_BITMANIP_ZBS 1
`define RV_DIV_BIT 4
`define RV_DIV_NEW 1
`define RV_DMA_BUF_DEPTH 5
`define RV_FAST_INTERRUPT_REDIRECT 1
`define RV_ICCM_ONLY 1
`define RV_LSU2DMA 0
`define RV_LSU_NUM_NBLOAD 4
`define RV_LSU_NUM_NBLOAD_WIDTH 2
`define RV_LSU_STBUF_DEPTH 4
`define RV_TIMER_LEGAL_EN 1
`define RV_DCCM_BANK_BITS 2
`define RV_DCCM_BITS 18
`define RV_DCCM_BYTE_WIDTH 4
`define RV_DCCM_DATA_CELL ram_16384x39
`define RV_DCCM_DATA_WIDTH 32
`define RV_DCCM_EADR 32'h5003ffff
`define RV_DCCM_ECC_WIDTH 7
`define RV_DCCM_ENABLE 1
`define RV_DCCM_FDATA_WIDTH 39
`define RV_DCCM_INDEX_BITS 14
`define RV_DCCM_NUM_BANKS 4
`define RV_DCCM_NUM_BANKS_4 
`define RV_DCCM_OFFSET 28'h00000
`define RV_DCCM_REGION 4'h5
`define RV_DCCM_RESERVED 'h1400
`define RV_DCCM_ROWS 16384
`define RV_DCCM_SADR 32'h50000000
`define RV_DCCM_SIZE 256
`define RV_DCCM_SIZE_256 
`define RV_DCCM_WIDTH_BITS 2
`define RV_LSU_SB_BITS 18
`define RV_ICACHE_2BANKS 1
`define RV_ICACHE_BANK_BITS 1
`define RV_ICACHE_BANK_HI 3
`define RV_ICACHE_BANK_LO 3
`define RV_ICACHE_BANK_WIDTH 8
`define RV_ICACHE_BANKS_WAY 2
`define RV_ICACHE_BEAT_ADDR_HI 5
`define RV_ICACHE_BEAT_BITS 3
`define RV_ICACHE_BYPASS_ENABLE 1
`define RV_ICACHE_DATA_CELL ram_512x71
`define RV_ICACHE_DATA_DEPTH 512
`define RV_ICACHE_DATA_INDEX_LO 4
`define RV_ICACHE_DATA_WIDTH 64
`define RV_ICACHE_ECC 1
`define RV_ICACHE_FDATA_WIDTH 71
`define RV_ICACHE_INDEX_HI 12
`define RV_ICACHE_LN_SZ 64
`define RV_ICACHE_NUM_BEATS 8
`define RV_ICACHE_NUM_BYPASS 2
`define RV_ICACHE_NUM_BYPASS_WIDTH 2
`define RV_ICACHE_NUM_LINES 256
`define RV_ICACHE_NUM_LINES_BANK 64
`define RV_ICACHE_NUM_LINES_WAY 128
`define RV_ICACHE_NUM_WAYS 2
`define RV_ICACHE_SCND_LAST 6
`define RV_ICACHE_SIZE 16
`define RV_ICACHE_STATUS_BITS 1
`define RV_ICACHE_TAG_BYPASS_ENABLE 1
`define RV_ICACHE_TAG_CELL ram_128x25
`define RV_ICACHE_TAG_DEPTH 128
`define RV_ICACHE_TAG_INDEX_LO 6
`define RV_ICACHE_TAG_LO 13
`define RV_ICACHE_TAG_NUM_BYPASS 2
`define RV_ICACHE_TAG_NUM_BYPASS_WIDTH 2
`define RV_ICACHE_WAYPACK 1
`define RV_ICCM_BANK_BITS 2
`define RV_ICCM_BANK_HI 3
`define RV_ICCM_BANK_INDEX_LO 4
`define RV_ICCM_BITS 18
`define RV_ICCM_DATA_CELL ram_16384x39
`define RV_ICCM_EADR 32'h4003ffff
`define RV_ICCM_ECC_WIDTH 7
`define RV_ICCM_ENABLE 1
`define RV_ICCM_INDEX_BITS 14
`define RV_ICCM_NUM_BANKS 4
`define RV_ICCM_NUM_BANKS_4 
`define RV_ICCM_OFFSET 10'h0
`define RV_ICCM_REGION 4'h4
`define RV_ICCM_RESERVED 'h1000
`define RV_ICCM_ROWS 16384
`define RV_ICCM_SADR 32'h40000000
`define RV_ICCM_SIZE 256
`define RV_ICCM_SIZE_256 
`define RV_DEBUG_SB_MEM 'hc0580000
`define RV_EXTERNAL_DATA 'he0580000
`define RV_EXTERNAL_DATA_1 'hd0000000
`define RV_SERIALIO 'hf0580000
`define RV_UNUSED_REGION0 'hb0000000
`define RV_UNUSED_REGION1 'ha0000000
`define RV_UNUSED_REGION2 'h90000000
`define RV_UNUSED_REGION3 'h80000000
`define RV_UNUSED_REGION4 'h70000000
`define RV_UNUSED_REGION5 'h30000000
`define RV_UNUSED_REGION6 'h20000000
`define RV_UNUSED_REGION7 'h10000000
`define RV_NMI_VEC 'h11110000
`define RV_NUMIREGS 32
`define RV_PIC_BASE_ADDR 32'h60000000
`define RV_PIC_BITS 15
`define RV_PIC_INT_WORDS 1
`define RV_PIC_MEIE_COUNT 31
`define RV_PIC_MEIE_MASK 'h1
`define RV_PIC_MEIE_OFFSET 'h2000
`define RV_PIC_MEIGWCLR_COUNT 31
`define RV_PIC_MEIGWCLR_MASK 'h0
`define RV_PIC_MEIGWCLR_OFFSET 'h5000
`define RV_PIC_MEIGWCTRL_COUNT 31
`define RV_PIC_MEIGWCTRL_MASK 'h3
`define RV_PIC_MEIGWCTRL_OFFSET 'h4000
`define RV_PIC_MEIP_COUNT 1
`define RV_PIC_MEIP_MASK 'h0
`define RV_PIC_MEIP_OFFSET 'h1000
`define RV_PIC_MEIPL_COUNT 31
`define RV_PIC_MEIPL_MASK 'hf
`define RV_PIC_MEIPL_OFFSET 'h0000
`define RV_PIC_MEIPT_COUNT 31
`define RV_PIC_MEIPT_MASK 'h0
`define RV_PIC_MEIPT_OFFSET 'h3004
`define RV_PIC_MPICCFG_COUNT 1
`define RV_PIC_MPICCFG_MASK 'h1
`define RV_PIC_MPICCFG_OFFSET 'h3000
`define RV_PIC_OFFSET 10'h0
`define RV_PIC_REGION 4'h6
`define RV_PIC_SIZE 32
`define RV_PIC_TOTAL_INT 31
`define RV_PIC_TOTAL_INT_PLUS1 32
`define RV_DATA_ACCESS_ADDR0 'h00000000
`define RV_DATA_ACCESS_ADDR1 'h00000000
`define RV_DATA_ACCESS_ADDR2 'h00000000
`define RV_DATA_ACCESS_ADDR3 'h00000000
`define RV_DATA_ACCESS_ADDR4 'h00000000
`define RV_DATA_ACCESS_ADDR5 'h00000000
`define RV_DATA_ACCESS_ADDR6 'h00000000
`define RV_DATA_ACCESS_ADDR7 'h00000000
`define RV_DATA_ACCESS_ENABLE0 1'h0
`define RV_DATA_ACCESS_ENABLE1 1'h0
`define RV_DATA_ACCESS_ENABLE2 1'h0
`define RV_DATA_ACCESS_ENABLE3 1'h0
`define RV_DATA_ACCESS_ENABLE4 1'h0
`define RV_DATA_ACCESS_ENABLE5 1'h0
`define RV_DATA_ACCESS_ENABLE6 1'h0
`define RV_DATA_ACCESS_ENABLE7 1'h0
`define RV_DATA_ACCESS_MASK0 'hffffffff
`define RV_DATA_ACCESS_MASK1 'hffffffff
`define RV_DATA_ACCESS_MASK2 'hffffffff
`define RV_DATA_ACCESS_MASK3 'hffffffff
`define RV_DATA_ACCESS_MASK4 'hffffffff
`define RV_DATA_ACCESS_MASK5 'hffffffff
`define RV_DATA_ACCESS_MASK6 'hffffffff
`define RV_DATA_ACCESS_MASK7 'hffffffff
`define RV_INST_ACCESS_ADDR0 'h00000000
`define RV_INST_ACCESS_ADDR1 'h00000000
`define RV_INST_ACCESS_ADDR2 'h00000000
`define RV_INST_ACCESS_ADDR3 'h00000000
`define RV_INST_ACCESS_ADDR4 'h00000000
`define RV_INST_ACCESS_ADDR5 'h00000000
`define RV_INST_ACCESS_ADDR6 'h00000000
`define RV_INST_ACCESS_ADDR7 'h00000000
`define RV_INST_ACCESS_ENABLE0 1'h0
`define RV_INST_ACCESS_ENABLE1 1'h0
`define RV_INST_ACCESS_ENABLE2 1'h0
`define RV_INST_ACCESS_ENABLE3 1'h0
`define RV_INST_ACCESS_ENABLE4 1'h0
`define RV_INST_ACCESS_ENABLE5 1'h0
`define RV_INST_ACCESS_ENABLE6 1'h0
`define RV_INST_ACCESS_ENABLE7 1'h0
`define RV_INST_ACCESS_MASK0 'hffffffff
`define RV_INST_ACCESS_MASK1 'hffffffff
`define RV_INST_ACCESS_MASK2 'hffffffff
`define RV_INST_ACCESS_MASK3 'hffffffff
`define RV_INST_ACCESS_MASK4 'hffffffff
`define RV_INST_ACCESS_MASK5 'hffffffff
`define RV_INST_ACCESS_MASK6 'hffffffff
`define RV_INST_ACCESS_MASK7 'hffffffff
`define RV_PMP_ENTRIES 64
`define REGWIDTH 32
`define RV_RESET_VEC 'h00000000
`define RV_RET_STACK_SIZE 8
`define RV_TARGET default_ahb
`define TEC_RV_ICG clockhdr
`define CPU_TOP `RV_TOP.veer
//`define RV_TOP `TOP.rvtop
`define SDVT_AHB 1
//`define TOP tb_top
`define RV_BUILD_AHB_LITE 1
`define CLOCK_PERIOD 100
`define RV_EXT_ADDRWIDTH 32
`define RV_EXT_DATAWIDTH 64
`define RV_LDERR_ROLLBACK 1
`define RV_STERR_ROLLBACK 0
`define RV_XLEN 32
`ifndef SYNTHESIS
`ifndef VERILATOR
    `define RV_ASSERT_ON 
`endif
`endif

`endif // RV_COMMON_DEFINES

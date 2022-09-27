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
//

import el2_pkg::*;
module caliptra_swerv_sram_export #(
    `include "el2_param.vh"
) (
    el2_mem_if.top el2_mem_export
);


if ( pt.ICACHE_ENABLE ) begin: icache
    //////////////////////////////////////////////////////
    // IC DATA
    //
    if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_DATA_0
        `define EL2_IC_DATA_SRAM(depth,width)                                \
            ram_``depth``x``width ic_bank_sb_way_data (                       \
                .CLK     (el2_mem_export.clk                                    ), \
                .ME      (el2_mem_export.ic_data_bank_way_clken[k][i]           ), \
                .WE      (el2_mem_export.ic_data_wren[k][i]                     ), \
                .D       (el2_mem_export.ic_data_sb_wr_data[k][``width-1:0]     ), \
                .ADR     (el2_mem_export.ic_data_addr_bank_q[k]                   ), \
                .Q       (el2_mem_export.ic_data_dout_pre[k][``width*i+:``width]     ), \
                .ROP     (                                                      ), \
                .TEST1   (1'b0    ), \
                .RME     (1'b0    ), \
                .RM      (4'b0000 ), \
                                                                              \
                .LS      (1'b0    ), \
                .DS      (1'b0    ), \
                .SD      (1'b0    ), \
                                                                              \
                .TEST_RNM(1'b0    ), \
                .BC1     (1'b0    ), \
                .BC2     (1'b0    )  \
            );

        for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
            for (genvar k=0; k<pt.ICACHE_BANKS_WAY; k++) begin: BANKS_WAY   // 16B subbank
                if (pt.ICACHE_ECC) begin : ECC1
                    if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
                        `EL2_IC_DATA_SRAM(8192,71)
                    end
                    else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
                        `EL2_IC_DATA_SRAM(4096,71)
                    end
                    else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
                        `EL2_IC_DATA_SRAM(2048,71)
                    end
                    else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
                        `EL2_IC_DATA_SRAM(1024,71)
                    end
                    else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
                        `EL2_IC_DATA_SRAM(512,71)
                    end
                    else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
                        `EL2_IC_DATA_SRAM(256,71)
                    end
                    else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
                        `EL2_IC_DATA_SRAM(128,71)
                    end
                    else  begin : size_64
                        `EL2_IC_DATA_SRAM(64,71)
                    end
                end // if (pt.ICACHE_ECC)

                else  begin  : ECC0
                    if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
                        `EL2_IC_DATA_SRAM(8192,68)
                    end
                    else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
                        `EL2_IC_DATA_SRAM(4096,68)
                    end
                    else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
                        `EL2_IC_DATA_SRAM(2048,68)
                    end
                    else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
                        `EL2_IC_DATA_SRAM(1024,68)
                    end
                    else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
                        `EL2_IC_DATA_SRAM(512,68)
                    end
                    else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
                        `EL2_IC_DATA_SRAM(256,68)
                    end
                    else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
                        `EL2_IC_DATA_SRAM(128,68)
                    end
                    else  begin : size_64
                        `EL2_IC_DATA_SRAM(64,68)
                    end
                end // else: !if(pt.ICACHE_ECC)
            end // block: BANKS_WAY
        end // block: WAYS
    end // block: PACKED_DATA_0

    // WAY PACKED
    else begin : PACKED_DATA_1
        `define EL2_PACKED_IC_DATA_SRAM(depth,width,waywidth)                                                                       \
            ram_be_``depth``x``width  ic_bank_sb_way_data (                                                                          \
                .CLK      (el2_mem_export.clk                                                        ),                                   \
                .WE       (|el2_mem_export.ic_data_wren[k]                                           ), // OR of all the ways in the bank \
                .WEM      (el2_mem_export.ic_data_bit_en_vec[k]                                      ), // 284 bits of bit enables        \
                .D        ({pt.ICACHE_NUM_WAYS{el2_mem_export.ic_data_sb_wr_data[k][``waywidth-1:0]}}),                                   \
                .ADR      (el2_mem_export.ic_data_addr_bank_q[k]                                       ),                                   \
                .Q        (el2_mem_export.ic_data_dout_pre[k]                                             ),                                   \
                .ME       (|el2_mem_export.ic_data_bank_way_clken[k]                                 ),                                   \
                .ROP      (                                                                          ),                                   \
                .TEST1    (1'b0    ),                                   \
                .RME      (1'b0    ),                                   \
                .RM       (4'b0000 ),                                   \
                                                                        \
                .LS       (1'b0    ),                                   \
                .DS       (1'b0    ),                                   \
                .SD       (1'b0    ),                                   \
                                                                        \
                .TEST_RNM (1'b0    ),                                   \
                .BC1      (1'b0    ),                                   \
                .BC2      (1'b0    )                                    \
            );

        // generate IC DATA PACKED SRAMS for 2/4 ways
        for (genvar k=0; k<pt.ICACHE_BANKS_WAY; k++) begin: BANKS_WAY   // 16B subbank
            if (pt.ICACHE_ECC) begin : ECC1
                // SRAMS with ECC (single/double detect; no correct)
                if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(8192,284,71)    // 64b data + 7b ecc
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(8192,142,71)
                   end // block: WAYS
                end // block: size_8192

                else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(4096,284,71)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(4096,142,71)
                   end // block: WAYS
                end // block: size_4096

                else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(2048,284,71)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(2048,142,71)
                   end // block: WAYS
                end // block: size_2048

                else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(1024,284,71)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(1024,142,71)
                   end // block: WAYS
                end // block: size_1024

                else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(512,284,71)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(512,142,71)
                   end // block: WAYS
                end // block: size_512

                else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(256,284,71)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(256,142,71)
                   end // block: WAYS
                end // block: size_256

                else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(128,284,71)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(128,142,71)
                   end // block: WAYS
                end // block: size_128

                else  begin : size_64
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(64,284,71)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(64,142,71)
                   end // block: WAYS
                end // block: size_64

            end // if (pt.ICACHE_ECC)


            else  begin  : ECC0
                // SRAMs with parity
                if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(8192,272,68)    // 64b data + 4b parity
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(8192,136,68)
                   end // block: WAYS
                end // block: size_8192

                else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(4096,272,68)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(4096,136,68)
                   end // block: WAYS
                end // block: size_4096

                else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(2048,272,68)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(2048,136,68)
                   end // block: WAYS
                end // block: size_2048

                else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(1024,272,68)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(1024,136,68)
                   end // block: WAYS
                end // block: size_1024

                else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(512,272,68)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(512,136,68)
                   end // block: WAYS
                end // block: size_512

                else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(256,272,68)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(256,136,68)
                   end // block: WAYS
                end // block: size_256

                else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(128,272,68)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(128,136,68)
                   end // block: WAYS
                end // block: size_128

                else  begin : size_64
                   if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(64,272,68)
                   end // block: WAYS
                   else   begin : WAYS
                      `EL2_PACKED_IC_DATA_SRAM(64,136,68)
                   end // block: WAYS
                end // block: size_64

            end // block: ECC0
        end // block: BANKS_WAY
    end // block: PACKED_DATA_1


    //////////////////////////////////////////////////////
    // IC TAG
    //
    if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_TAG_0
        `define EL2_IC_TAG_SRAM(depth,width)                                                      \
            ram_``depth``x``width  ic_way_tag (                                                    \
                .CLK     (el2_mem_export.clk                                                     ), \
                .ME      (el2_mem_export.ic_tag_clken_final[i]                                   ), \
                .WE      (el2_mem_export.ic_tag_wren_q[i]                                        ), \
                .D       (el2_mem_export.ic_tag_wr_data[``width-1:0]                             ), \
                .ADR     (el2_mem_export.ic_tag_addr_q[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]), \
                .Q       (el2_mem_export.ic_tag_data_raw_pre[``width * i+:``width]               ), \
                .ROP     (                                                                       ), \
                                                                                                   \
                .TEST1   (1'b0    ), \
                .RME     (1'b0    ), \
                .RM      (4'b0000 ), \
                                     \
                .LS      (1'b0    ), \
                .DS      (1'b0    ), \
                .SD      (1'b0    ), \
                                     \
                .TEST_RNM(1'b0    ), \
                .BC1     (1'b0    ), \
                .BC2     (1'b0    )  \
            );

        for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS

            if (pt.ICACHE_ECC) begin  : ECC1
                if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
                           `EL2_IC_TAG_SRAM(32,26)
                end // if (pt.ICACHE_TAG_DEPTH == 32)
                if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
                           `EL2_IC_TAG_SRAM(64,26)
                end // if (pt.ICACHE_TAG_DEPTH == 64)
                if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
                           `EL2_IC_TAG_SRAM(128,26)
                end // if (pt.ICACHE_TAG_DEPTH == 128)
                if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
                          `EL2_IC_TAG_SRAM(256,26)
                end // if (pt.ICACHE_TAG_DEPTH == 256)
                if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
                          `EL2_IC_TAG_SRAM(512,26)
                end // if (pt.ICACHE_TAG_DEPTH == 512)
                if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
                          `EL2_IC_TAG_SRAM(1024,26)
                end // if (pt.ICACHE_TAG_DEPTH == 1024)
                if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
                          `EL2_IC_TAG_SRAM(2048,26)
                end // if (pt.ICACHE_TAG_DEPTH == 2048)
                if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
                          `EL2_IC_TAG_SRAM(4096,26)
                end // if (pt.ICACHE_TAG_DEPTH == 4096)
            end
            else  begin : ECC0
                if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
                           `EL2_IC_TAG_SRAM(32,22)
                end // if (pt.ICACHE_TAG_DEPTH == 32)
                if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
                           `EL2_IC_TAG_SRAM(64,22)
                end // if (pt.ICACHE_TAG_DEPTH == 64)
                if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
                           `EL2_IC_TAG_SRAM(128,22)
                end // if (pt.ICACHE_TAG_DEPTH == 128)
                if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
                          `EL2_IC_TAG_SRAM(256,22)
                end // if (pt.ICACHE_TAG_DEPTH == 256)
                if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
                          `EL2_IC_TAG_SRAM(512,22)
                end // if (pt.ICACHE_TAG_DEPTH == 512)
                if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
                          `EL2_IC_TAG_SRAM(1024,22)
                end // if (pt.ICACHE_TAG_DEPTH == 1024)
                if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
                          `EL2_IC_TAG_SRAM(2048,22)
                end // if (pt.ICACHE_TAG_DEPTH == 2048)
                if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
                          `EL2_IC_TAG_SRAM(4096,22)
                end // if (pt.ICACHE_TAG_DEPTH == 4096)
            end // else: !if(pt.ICACHE_ECC)

        end // block: WAYS
    end // block: PACKED_TAG_0

    else begin : PACKED_TAG_1
        `define EL2_IC_TAG_PACKED_SRAM(depth,width)                                                             \
            ram_be_``depth``x``width  ic_way_tag (                                                              \
                .CLK      (el2_mem_export.clk                                                                 ), \
                .ME       ( el2_mem_export.ic_tag_clken_final[0]                                              ), \
                .WE       (|el2_mem_export.ic_tag_wren_q[pt.ICACHE_NUM_WAYS-1:0]                              ), \
                .WEM      (el2_mem_export.ic_tag_wren_biten_vec[``width-1:0]                                  ), \
                                                                                                                 \
                .D        ({pt.ICACHE_NUM_WAYS{el2_mem_export.ic_tag_wr_data[``width/pt.ICACHE_NUM_WAYS-1:0]}}), \
                .ADR      (el2_mem_export.ic_tag_addr_q[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]            ), \
                .Q        (el2_mem_export.ic_tag_data_raw_pre[``width-1:0]                                    ), \
                .ROP      (                                                                                   ), \
                                                                                                                 \
                .TEST1    (1'b0    ), \
                .RME      (1'b0    ), \
                .RM       (4'b0000 ), \
                                      \
                .LS       (1'b0    ), \
                .DS       (1'b0    ), \
                .SD       (1'b0    ), \
                                      \
                .TEST_RNM (1'b0    ), \
                .BC1      (1'b0    ), \
                .BC2      (1'b0    )  \
            );

        if (pt.ICACHE_ECC) begin  : ECC1
             if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
                 if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                          `EL2_IC_TAG_PACKED_SRAM(32,104)
                 end // block: WAYS
                 else begin : WAYS
                          `EL2_IC_TAG_PACKED_SRAM(32,52)
                 end // block: WAYS
             end // if (pt.ICACHE_TAG_DEPTH == 32

             if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
                 if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                          `EL2_IC_TAG_PACKED_SRAM(64,104)
                 end // block: WAYS
                 else begin : WAYS
                          `EL2_IC_TAG_PACKED_SRAM(64,52)
                 end // block: WAYS
             end // block: size_64

             if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
                 if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                        `EL2_IC_TAG_PACKED_SRAM(128,104)
                 end // block: WAYS
                 else begin : WAYS
                        `EL2_IC_TAG_PACKED_SRAM(128,52)
                 end // block: WAYS

             end // block: size_128

             if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
                 if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                           `EL2_IC_TAG_PACKED_SRAM(256,104)
                 end // block: WAYS
                 else begin : WAYS
                           `EL2_IC_TAG_PACKED_SRAM(256,52)
                 end // block: WAYS
             end // block: size_256

             if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
                 if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                           `EL2_IC_TAG_PACKED_SRAM(512,104)
                  end // block: WAYS
                 else begin : WAYS
                           `EL2_IC_TAG_PACKED_SRAM(512,52)
                  end // block: WAYS
             end // block: size_512

             if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
                  if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                          `EL2_IC_TAG_PACKED_SRAM(1024,104)
                 end // block: WAYS
                else begin : WAYS
                          `EL2_IC_TAG_PACKED_SRAM(1024,52)
                 end // block: WAYS
             end // block: size_1024

             if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
                if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                          `EL2_IC_TAG_PACKED_SRAM(2048,104)
                 end // block: WAYS
                else begin : WAYS
                          `EL2_IC_TAG_PACKED_SRAM(2048,52)
                 end // block: WAYS
             end // block: size_2048

             if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
                 if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                           `EL2_IC_TAG_PACKED_SRAM(4096,104)
                  end // block: WAYS
                 else begin : WAYS
                           `EL2_IC_TAG_PACKED_SRAM(4096,52)
                  end // block: WAYS
             end // block: size_4096
        end // block: ECC1
        else  begin : ECC0
            if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
              if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(32,88)
              end // block: WAYS
            else begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(32,44)
              end // block: WAYS
            end // if (pt.ICACHE_TAG_DEPTH == 32

            if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
              if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(64,88)
              end // block: WAYS
            else begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(64,44)
              end // block: WAYS
            end // block: size_64

            if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
             if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(128,88)
            end // block: WAYS
            else begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(128,44)
            end // block: WAYS

            end // block: size_128

            if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
             if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(256,88)
              end // block: WAYS
             else begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(256,44)
              end // block: WAYS
            end // block: size_256

            if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
             if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(512,88)
              end // block: WAYS
             else begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(512,44)
              end // block: WAYS
            end // block: size_512

            if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
               if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(1024,88)
              end // block: WAYS
             else begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(1024,44)
              end // block: WAYS
            end // block: size_1024

            if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
             if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(2048,88)
              end // block: WAYS
             else begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(2048,44)
              end // block: WAYS
            end // block: size_2048

            if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
             if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(4096,88)
              end // block: WAYS
             else begin : WAYS
                       `EL2_IC_TAG_PACKED_SRAM(4096,44)
              end // block: WAYS
            end // block: size_4096
        end // block: ECC0
    end // block: PACKED_TAG_1
end // block: icache


//////////////////////////////////////////////////////
// DCCM
//
if (pt.DCCM_ENABLE == 1) begin: Gen_dccm_enable
`define EL2_LOCAL_DCCM_RAM_TEST_PORTS    .TEST1   (1'b0   ), \
                                         .RME     (1'b0   ), \
                                         .RM      (4'b0000), \
                                         .LS      (1'b0   ), \
                                         .DS      (1'b0   ), \
                                         .SD      (1'b0   ), \
                                         .TEST_RNM(1'b0   ), \
                                         .BC1     (1'b0   ), \
                                         .BC2     (1'b0   ), \

localparam DCCM_INDEX_DEPTH = ((pt.DCCM_SIZE)*1024)/((pt.DCCM_BYTE_WIDTH)*(pt.DCCM_NUM_BANKS));  // Depth of memory bank
// 8 Banks, 16KB each (2048 x 72)
for (genvar i=0; i<pt.DCCM_NUM_BANKS; i++) begin: dccm_loop
`ifdef VERILATOR

        el2_ram #(DCCM_INDEX_DEPTH,39)  ram (
                                  // Primary ports
                                  .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                  .CLK (el2_mem_export.clk                                            ),
                                  .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                  .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                  .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                  .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                  .ROP (                                                              ),
                                  // These are used by SoC
                                  `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                  .*
                                  );
`else

      if (DCCM_INDEX_DEPTH == 32768) begin : dccm
         ram_32768x39  dccm_bank (
                                  // Primary ports
                                  .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                  .CLK (el2_mem_export.clk                                            ),
                                  .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                  .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                  .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                  .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                  .ROP (                                                              ),
                                  // These are used by SoC
                                  `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                  .*
                                  );
      end
      else if (DCCM_INDEX_DEPTH == 16384) begin : dccm
         ram_16384x39  dccm_bank (
                                  // Primary ports
                                  .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                  .CLK (el2_mem_export.clk                                            ),
                                  .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                  .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                  .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                  .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                  .ROP (                                                              ),
                                  // These are used by SoC
                                  `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                  .*
                                  );
      end
      else if (DCCM_INDEX_DEPTH == 8192) begin : dccm
         ram_8192x39  dccm_bank (
                                 // Primary ports
                                 .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                 .CLK (el2_mem_export.clk                                            ),
                                 .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                 .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                 .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                 .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                 .ROP (                                                              ),
                                 // These are used by SoC
                                 `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                 .*
                                 );
      end
      else if (DCCM_INDEX_DEPTH == 4096) begin : dccm
         ram_4096x39  dccm_bank (
                                 // Primary ports
                                 .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                 .CLK (el2_mem_export.clk                                            ),
                                 .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                 .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                 .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                 .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                 .ROP (                                                              ),
                                 // These are used by SoC
                                 `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                 .*
                                 );
      end
      else if (DCCM_INDEX_DEPTH == 3072) begin : dccm
         ram_3072x39  dccm_bank (
                                 // Primary ports
                                 .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                 .CLK (el2_mem_export.clk                                            ),
                                 .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                 .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                 .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                 .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                 .ROP (                                                              ),
                                 // These are used by SoC
                                 `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                 .*
                                 );
      end
      else if (DCCM_INDEX_DEPTH == 2048) begin : dccm
         ram_2048x39  dccm_bank (
                                 // Primary ports
                                 .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                 .CLK (el2_mem_export.clk                                            ),
                                 .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                 .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                 .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                 .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                 .ROP (                                                              ),
                                 // These are used by SoC
                                 `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                 .*
                                 );
      end
      else if (DCCM_INDEX_DEPTH == 1024) begin : dccm
         ram_1024x39  dccm_bank (
                                 // Primary ports
                                 .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                 .CLK (el2_mem_export.clk                                            ),
                                 .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                 .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                 .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                 .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                 .ROP (                                                              ),
                                 // These are used by SoC
                                 `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                 .*
                                 );
      end
      else if (DCCM_INDEX_DEPTH == 512) begin : dccm
         ram_512x39  dccm_bank (
                                // Primary ports
                                .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                .CLK (el2_mem_export.clk                                            ),
                                .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                .ROP (                                                              ),
                                // These are used by SoC
                                `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                .*
                                );
      end
      else if (DCCM_INDEX_DEPTH == 256) begin : dccm
         ram_256x39  dccm_bank (
                                // Primary ports
                                .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                .CLK (el2_mem_export.clk                                            ),
                                .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                .ROP (                                                              ),
                                // These are used by SoC
                                `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                .*
                                );
      end
      else if (DCCM_INDEX_DEPTH == 128) begin : dccm
         ram_128x39  dccm_bank (
                                // Primary ports
                                .ME  (el2_mem_export.dccm_clken[i]                                  ),
                                .CLK (el2_mem_export.clk                                            ),
                                .WE  (el2_mem_export.dccm_wren_bank[i]                              ),
                                .ADR (el2_mem_export.dccm_addr_bank[i]                              ),
                                .D   (el2_mem_export.dccm_wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:0]  ),
                                .Q   (el2_mem_export.dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:0]     ),
                                .ROP (                                                              ),
                                // These are used by SoC
                                `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                .*
                                );
      end
`endif
end : dccm_loop
end :Gen_dccm_enable


//////////////////////////////////////////////////////
// ICCM
//
if (pt.ICCM_ENABLE) begin : Gen_iccm_enable
for (genvar i=0; i<pt.ICCM_NUM_BANKS; i++) begin: iccm_loop
 `ifdef VERILATOR

    el2_ram #(.depth(1<<pt.ICCM_INDEX_BITS), .width(39)) iccm_bank (
                                     // Primary ports
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .CLK (el2_mem_export.clk                       ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
 `else

     if (pt.ICCM_INDEX_BITS == 6 ) begin : iccm
               ram_64x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm

   else if (pt.ICCM_INDEX_BITS == 7 ) begin : iccm
               ram_128x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm

     else if (pt.ICCM_INDEX_BITS == 8 ) begin : iccm
               ram_256x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 9 ) begin : iccm
               ram_512x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 10 ) begin : iccm
               ram_1024x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 11 ) begin : iccm
               ram_2048x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 12 ) begin : iccm
               ram_4096x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 13 ) begin : iccm
               ram_8192x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 14 ) begin : iccm
               ram_16384x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm
     else begin : iccm
               ram_32768x39 iccm_bank (
                                     // Primary ports
                                     .CLK (el2_mem_export.clk                       ),
                                     .ME  (el2_mem_export.iccm_clken[i]             ),
                                     .WE  (el2_mem_export.iccm_wren_bank[i]         ),
                                     .ADR (el2_mem_export.iccm_addr_bank[i]         ),
                                     .D   (el2_mem_export.iccm_bank_wr_data[i][38:0]),
                                     .Q   (el2_mem_export.iccm_bank_dout[i][38:0]   ),
                                     .ROP (                                         ),
                                     // These are used by SoC
                                     .TEST1   (1'b0   ),
                                     .RME     (1'b0   ),
                                     .RM      (4'b0000),
                                     .LS      (1'b0   ),
                                     .DS      (1'b0   ),
                                     .SD      (1'b0   ) ,
                                     .TEST_RNM(1'b0   ),
                                     .BC1     (1'b0   ),
                                     .BC2     (1'b0   )

                                      );
     end // block: iccm
`endif
end : iccm_loop
end : Gen_iccm_enable


endmodule

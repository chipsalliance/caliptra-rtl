/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
.section .dccm
hw_data:
// start of input message
.word 0x61626380
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000018
// expected value
.word 0xDDAF35A1
.word 0x93617ABA
.word 0xCC417349
.word 0xAE204131
.word 0x12E6FA4E
.word 0x89A97EA2
.word 0x0A9EEEE6
.word 0x4B55D39A
.word 0x2192992A
.word 0x274FC1A8
.word 0x36BA3C23
.word 0xA3FEEBBD
.word 0x454D4423
.word 0x643CE80E
.word 0x2A9AC94F
.word 0xA54CA49F
SHA512ShortMsg:
// SHA512ShortMsgvector_2
// vector length
.word 0x00000008
// input message
.word 0x21000000
// expected output
.word 0x3831a6a6
.word 0x155e509d
.word 0xee59a7f4
.word 0x51eb3532
.word 0x4d8f8f2d
.word 0xf6e37088
.word 0x94740f98
.word 0xfdee2388
.word 0x9f4de5ad
.word 0xb0c5010d
.word 0xfb555cda
.word 0x77c8ab5d
.word 0xc902094c
.word 0x52de3278
.word 0xf35a75eb
.word 0xc25f093a
SHA512LongMsg:
// vector length
.word 0x00000A30
// input message
.word 0xd5e378ae
.word 0x9fc2648f
.word 0x4a13bbec
.word 0x4b0935af
.word 0xb4f822f5
.word 0xfe0d5063
.word 0x053d2fbd
.word 0x547b33b4
.word 0xa32e7a00
.word 0x9ee2afaf
.word 0xe83d2ebd
.word 0x603568e4
.word 0xa38189b5
.word 0xd24d59e8
.word 0x953260f1
.word 0x5f654ed4
.word 0xf42f9a39
.word 0x299d68c3
.word 0xeb78b09e
.word 0x83779d57
.word 0x18b433f1
.word 0x765d3535
.word 0x0eac4649
.word 0x3d194e84
.word 0xd1ce1f81
.word 0xc95b5972
.word 0x5cab8ab7
.word 0x3d369ab0
.word 0x1e7967cf
.word 0x73a3acf1
.word 0x789227ee
.word 0x75fdfb6e
.word 0x40f353ff
.word 0x04844865
.word 0x42be0531
.word 0x15db2896
.word 0xbab86c77
.word 0x4f8985c4
.word 0xdbcc4c07
.word 0x8f7b1c3a
.word 0x4c867cdc
.word 0x6580fe44
.word 0xa5986734
.word 0x94cc0fb1
.word 0xf6598b12
.word 0x95768a58
.word 0x4041fdbd
.word 0x14fa7b90
.word 0xfa6fe33f
.word 0x71b743b6
.word 0x8e23f8e7
.word 0x407217aa
.word 0xd9440cc8
.word 0xcad28152
.word 0xaedb8238
.word 0x8be2de16
.word 0x5496d051
.word 0xb292de63
.word 0x03460273
.word 0xa4350829
.word 0x6b6237c0
.word 0x7804335d
.word 0x2e81229f
.word 0x7c9a0e77
.word 0x61e38a3a
.word 0xaf7799f4
.word 0x0fe9cb00
.word 0x457ea9d5
.word 0xb5995323
.word 0x2676681f
.word 0xc71b261a
.word 0x6f8cd359
.word 0x293f5b21
.word 0xf0cf3a11
.word 0xb7f49cb5
.word 0xadb3c357
.word 0xbed2aa18
.word 0x5d8fe840
.word 0x8192d6d3
.word 0xed1ff465
.word 0xb590892e
.word 0xfe030000
// expected output
.word 0xa70c75b9
.word 0xb1f0ac2e
.word 0xd2c27977
.word 0x63ac9a66
.word 0x01d95f46
.word 0x889b00fc
.word 0x3ddae4d0
.word 0xac692375
.word 0x0a108d79
.word 0xeb764e77
.word 0xac07b7cb
.word 0x5c01cb4b
.word 0x3747dcf6
.word 0x9ba3b35c
.word 0x51fb995d
.word 0xa2632e70
SHA384LongMsg:
// vector length
.word 0x00000718
// input message
.word 0x62c6a169
.word 0xb9be02b3
.word 0xd7b471a9
.word 0x64fc0bcc
.word 0x72b480d2
.word 0x6aecb2ed
.word 0x460b7f50
.word 0x016ddaf0
.word 0x4c512187
.word 0x83f3aadf
.word 0xdff5a04d
.word 0xed030d7b
.word 0x3fb7376b
.word 0x61ba30b9
.word 0x0e2da921
.word 0xa4470740
.word 0xd63fb99f
.word 0xa16cc8ed
.word 0x81abaf8c
.word 0xe4016e50
.word 0xdf81da83
.word 0x2070372c
.word 0x24a80890
.word 0xaa3a26fa
.word 0x675710b8
.word 0xfb718266
.word 0x249d496f
.word 0x313c55d0
.word 0xbada101f
.word 0x8f56eecc
.word 0xee4345a8
.word 0xf98f60a3
.word 0x6662cfda
.word 0x794900d1
.word 0x2f9414fc
.word 0xbdfdeb85
.word 0x388a8149
.word 0x96b47e24
.word 0xd5c8086e
.word 0x7a8edcc5
.word 0x3d299d0d
.word 0x033e6bb6
.word 0x0c58b83d
.word 0x6e8b57f6
.word 0xc258d608
.word 0x1dd10eb9
.word 0x42fdf8ec
.word 0x157ec3e7
.word 0x5371235a
.word 0x8196eb9d
.word 0x22b1de3a
.word 0x2d30c2ab
.word 0xbe0db765
.word 0x0cf6c715
.word 0x9bacbe29
.word 0xb3a93c92
.word 0x10050800
// expected output
.word 0x0730e184
.word 0xe7795575
.word 0x569f8703
.word 0x0260bb8e
.word 0x54498e0e
.word 0x5d096b18
.word 0x285e988d
.word 0x245b6f34
.word 0x86d1f244
.word 0x7d5f85bc
.word 0xbe59d568
.word 0x9fc49425

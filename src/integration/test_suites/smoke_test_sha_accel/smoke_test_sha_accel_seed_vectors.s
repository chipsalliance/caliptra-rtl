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
.word 0x00000d48
// input message
.word 0x4f7a5618
.word 0x870945b8
.word 0x9f194e31
.word 0xb1aa802c
.word 0x5350326d
.word 0xc691df58
.word 0x708e34b4
.word 0x8ce666b0
.word 0x21d7c923
.word 0x30a69f18
.word 0x32412d8a
.word 0xc224156c
.word 0x9679dfed
.word 0xb383d9f9
.word 0xe13c2103
.word 0x5d3d0002
.word 0xcfdf79b9
.word 0x7ba0223c
.word 0xbbc833b0
.word 0xad4cdd52
.word 0x29f2ddbb
.word 0xf6b65062
.word 0x3d6cc962
.word 0x3da8a17d
.word 0x41db8e61
.word 0xcfbe772b
.word 0x23f4872a
.word 0xdceb81e5
.word 0xf403535f
.word 0xf5f2ed99
.word 0x6a675359
.word 0x94edf12a
.word 0x5f1230a4
.word 0x94c946ed
.word 0x500e5280
.word 0xb5c8a82d
.word 0xdff36961
.word 0x1afe58a8
.word 0x5272e870
.word 0xcbd59a10
.word 0x12ce8509
.word 0x338a368b
.word 0x2c5dbb3b
.word 0xa2adfb33
.word 0xd30c494a
.word 0xcca43896
.word 0xdbd8b030
.word 0x48284137
.word 0x4055b818
.word 0x12c6f00c
.word 0x9e2bebe2
.word 0x096021fe
.word 0xb69418a2
.word 0x72aa356c
.word 0xefdfd220
.word 0x74ae91a8
.word 0xd2f1ef59
.word 0x9a481c78
.word 0x8dbe0afd
.word 0x54aac396
.word 0x72d401ef
.word 0x76d9f831
.word 0x75d177c9
.word 0xb72e2f6a
.word 0xb1e75255
.word 0x33d761d8
.word 0xe3603f14
.word 0xea538904
.word 0xed142abb
.word 0x3ff929ed
.word 0x55f4c6b1
.word 0x7a72c685
.word 0xc3820b93
.word 0x463a6733
.word 0x8756b2b0
.word 0x33231a4f
.word 0x119cbb8d
.word 0x35d270a9
.word 0x7791e862
.word 0x2340fc02
.word 0xf2093f9b
.word 0x393ad791
.word 0x61eb8c58
.word 0x97e21f7f
.word 0xc4b3ddee
.word 0xc02b736c
.word 0xc3ef0464
.word 0x1c6179e8
.word 0x25c319f6
.word 0x769f59fa
.word 0x5966f595
.word 0x7e573f9d
.word 0xf0a2b765
.word 0x48cedd3e
.word 0x2158433d
.word 0xcb9de63f
.word 0x44f9be2b
.word 0x63319477
.word 0x570e14ee
.word 0x504b23b0
.word 0x7cb2737a
.word 0x35815427
.word 0x7912cd77
.word 0x9abbeb10
.word 0x36f459c2
.word 0x6ab7310f
.word 0x43000000
// expected output
.word 0x713d5c26
.word 0xde17e144
.word 0x0a36aab9
.word 0x3f7cd811
.word 0x1cd62fd8
.word 0xbea5099b
.word 0x2b6bf93e
.word 0x470e1eae
.word 0xab8b925c
.word 0x646e9e67
.word 0xce01b03b
.word 0x33d2b500
.word 0xb9400e59
.word 0xf0ecdfb0
.word 0x0dd7ddcd
.word 0x230cc837
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

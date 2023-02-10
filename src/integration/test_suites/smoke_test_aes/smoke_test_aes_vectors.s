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
// start of 128bit key
.word 0x56e47a38  
.word 0xc5598974
.word 0xbc46903d
.word 0xba290349
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
// start of IV input
.word 0x8ce82eef   
.word 0xbea0da3c
.word 0x44699ed7
.word 0xdb51b7d9 
// start of 1st text
.word 0xa0a1a2a3   
.word 0xa4a5a6a7
.word 0xa8a9aaab
.word 0xacadaeaf
// start of 2nd text
.word 0xb0b1b2b3  
.word 0xb4b5b6b7
.word 0xb8b9babb
.word 0xbcbdbebf 
// start of 3rd text
.word 0xc0c1c2c3
.word 0xc4c5c6c7  
.word 0xc8c9cacb
.word 0xcccdcecf 
// start of 4th text
.word 0xd0d1d2d3
.word 0xd4d5d6d7 
.word 0xd8d9dadb
.word 0xdcdddedf 
// start of 1st expected
.word 0xc30e32ff
.word 0xedc0774e
.word 0x6aff6af0
.word 0x869f71aa
// start of 2nd expected
.word 0x0f3af07a
.word 0x9a31a9c6
.word 0x84db207e
.word 0xb0ef8e4e
// start of 3rd expected
.word 0x35907aa6
.word 0x32c3ffdf
.word 0x868bb7b2
.word 0x9d3d46ad
// start of 4th expected
.word 0x83ce9f9a
.word 0x102ee99d
.word 0x49a53e87
.word 0xf4c3da55
// .ascii "----------------------------------\n"
// .ascii "AES CBC mode Quadratic Blocks Test !!\n"
// .ascii "----------------------------------\n"
// .byte 0
// string1: 
// .ascii "1st block successful"
// string2: 
// .ascii "2nd block successful"
// string3: 
// .ascii "3rd block successful"
// string4: 
// .ascii "4th block successful"
CBCMMT256:
// CBCMMT256_vector1
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000001
// start of key
.word 0x6ed76d2d
.word 0x97c69fd1
.word 0x33958952
.word 0x3931f2a6
.word 0xcff554b1
.word 0x5f738f21
.word 0xec72dd97
.word 0xa7330907
// start of IV
.word 0x851e8764
.word 0x776e6796
.word 0xaab722db
.word 0xb644ace8
// input message
.word 0x6282b8c0
.word 0x5c5c1530
.word 0xb97d4816
.word 0xca434762
// expected output
.word 0x6acc0414
.word 0x2e100a65
.word 0xf51b97ad
.word 0xf5172c41
// CBCMMT256_vector2
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000002
// start of key
.word 0xdce26c6b
.word 0x4cfb2865
.word 0x10da4eec
.word 0xd2cffe6c
.word 0xdf430f33
.word 0xdb9b5f77
.word 0xb460679b
.word 0xd49d13ae
// start of IV
.word 0xfdeaa134
.word 0xc8d7379d
.word 0x457175fd
.word 0x1a57d3fc
// input message
.word 0x50e9eee1
.word 0xac528009
.word 0xe8cbcd35
.word 0x6975881f
.word 0x957254b1
.word 0x3f91d7c6
.word 0x662d1031
.word 0x2052eb00
// expected output
.word 0x2fa0df72
.word 0x2a9fd3b6
.word 0x4cb18fb2
.word 0xb3db55ff
.word 0x22674227
.word 0x57289413
.word 0xf8f65750
.word 0x7412a64c
// CBCMMT256_vector3
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000003
// start of key
.word 0xfe8901fe
.word 0xcd3ccd2e
.word 0xc5fdc7c7
.word 0xa0b50519
.word 0xc245b42d
.word 0x611a5ef9
.word 0xe90268d5
.word 0x9f3edf33
// start of IV
.word 0xbd416cb3
.word 0xb9892228
.word 0xd8f1df57
.word 0x5692e4d0
// input message
.word 0x8d3aa196
.word 0xec3d7c9b
.word 0x5bb122e7
.word 0xfe77fb12
.word 0x95a6da75
.word 0xabe5d3a5
.word 0x10194d3a
.word 0x8a4157d5
.word 0xc89d4061
.word 0x97166198
.word 0x59da3ec9
.word 0xb247ced9
// expected output
.word 0x608e82c7
.word 0xab04007a
.word 0xdb22e389
.word 0xa44797fe
.word 0xd7de090c
.word 0x8c03ca8a
.word 0x2c5acd9e
.word 0x84df37fb
.word 0xc58ce8ed
.word 0xb293e98f
.word 0x02b640d6
.word 0xd1d72464
// CBCMMT256_vector4
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000004
// start of key
.word 0x0493ff63
.word 0x7108af6a
.word 0x5b8e90ac
.word 0x1fdf035a
.word 0x3d4bafd1
.word 0xafb573be
.word 0x7ade9e86
.word 0x82e663e5
// start of IV
.word 0xc0cd2beb
.word 0xccbb6c49
.word 0x920bd548
.word 0x2ac756e8
// input message
.word 0x8b37f914
.word 0x8df4bb25
.word 0x956be631
.word 0x0c73c8dc
.word 0x58ea9714
.word 0xff49b643
.word 0x107b34c9
.word 0xbff096a9
.word 0x4fedd682
.word 0x3526abc2
.word 0x7a8e0b16
.word 0x616eee25
.word 0x4ab4567d
.word 0xd68e8ccd
.word 0x4c38ac56
.word 0x3b13639c
// expected output
.word 0x05d5c777
.word 0x29421b08
.word 0xb737e411
.word 0x19fa4438
.word 0xd1f570cc
.word 0x772a4d6c
.word 0x3df7ffed
.word 0xa0384ef8
.word 0x4288ce37
.word 0xfc4c4c7d
.word 0x1125a499
.word 0xb051364c
.word 0x389fd639
.word 0xbdda647d
.word 0xaa3bdada
.word 0xb2eb5594
// CBCMMT256_vector5
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000005
// start of key
.word 0x9adc8fbd
.word 0x506e032a
.word 0xf7fa20cf
.word 0x5343719d
.word 0xe6d1288c
.word 0x158c63d6
.word 0x878aaf64
.word 0xce26ca85
// start of IV
.word 0x11958dc6
.word 0xab81e1c7
.word 0xf01631e9
.word 0x944e620f
// input message
.word 0xc7917f84
.word 0xf747cd8c
.word 0x4b4fedc2
.word 0x219bdbc5
.word 0xf4d07588
.word 0x389d8248
.word 0x854cf2c2
.word 0xf89667a2
.word 0xd7bcf53e
.word 0x73d32684
.word 0x535f4231
.word 0x8e24cd45
.word 0x793950b3
.word 0x825e5d5c
.word 0x5c8fcd3e
.word 0x5dda4ce9
.word 0x246d1833
.word 0x7ef3052d
.word 0x8b21c556
.word 0x1c8b660e
// expected output
.word 0x9c99e682
.word 0x36bb2e92
.word 0x9db1089c
.word 0x7750f1b3
.word 0x56d39ab9
.word 0xd0c40c3e
.word 0x2f05108a
.word 0xe9d0c30b
.word 0x04832ccd
.word 0xbdc08ebf
.word 0xa426b7f5
.word 0xefde986e
.word 0xd05784ce
.word 0x368193bb
.word 0x3699bc69
.word 0x1065ac62
.word 0xe258b9aa
.word 0x4cc557e2
.word 0xb45b49ce
.word 0x05511e65
// CBCMMT256_vector6
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000006
// start of key
.word 0x73b8faf0
.word 0x0b3302ac
.word 0x99855cf6
.word 0xf9e9e485
.word 0x18690a59
.word 0x06a4869d
.word 0x4dcf48d2
.word 0x82faae2a
// start of IV
.word 0xb3cb97a8
.word 0x0a539912
.word 0xb8c21f45
.word 0x0d3b9395
// input message
.word 0x3adea6e0
.word 0x6e42c4f0
.word 0x41021491
.word 0xf2775ef6
.word 0x378cb088
.word 0x24165edc
.word 0x4f6448e2
.word 0x32175b60
.word 0xd0345b9f
.word 0x9c78df65
.word 0x96ec9d22
.word 0xb7b9e76e
.word 0x8f3c76b3
.word 0x2d5d6727
.word 0x3f1d83fe
.word 0x7a6fc3dd
.word 0x3c491391
.word 0x70fa5701
.word 0xb3beac61
.word 0xb490f0a9
.word 0xe13f8446
.word 0x40c4500f
.word 0x9ad3087a
.word 0xdfb0ae10
// expected output
.word 0xac3d6dba
.word 0xfe2e0f74
.word 0x0632fd9e
.word 0x820bf604
.word 0x4cd5b155
.word 0x1cbb9cc0
.word 0x3c0b25c3
.word 0x9ccb7f33
.word 0xb83aacfc
.word 0xa40a3265
.word 0xf2bbff87
.word 0x9153448a
.word 0xcacb88fc
.word 0xfb3bb7b1
.word 0x0fe463a6
.word 0x8c0109f0
.word 0x28382e3e
.word 0x557b1adf
.word 0x02ed648a
.word 0xb6bb895d
.word 0xf0205d26
.word 0xebbfa9a5
.word 0xfd8cebd8
.word 0xe4bee3dc
// CBCMMT256_vector7
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000007
// start of key
.word 0x9ddf3745
.word 0x896504ff
.word 0x360a51a3
.word 0xeb49c01b
.word 0x79fccebc
.word 0x71c3abcb
.word 0x94a94940
.word 0x8b05b2c9
// start of IV
.word 0xe7902663
.word 0x9d4aa230
.word 0xb5ccffb0
.word 0xb29d79bc
// input message
.word 0xcf52e5c3
.word 0x954c51b9
.word 0x4c9e38ac
.word 0xb8c9a7c7
.word 0x6aebdaa9
.word 0x943eae0a
.word 0x1ce155a2
.word 0xefdb4d46
.word 0x985d9355
.word 0x11471452
.word 0xd9ee64d2
.word 0x461cb299
.word 0x1d59fc00
.word 0x60697f9a
.word 0x67167216
.word 0x3230f367
.word 0xfed14223
.word 0x16e52d29
.word 0xeceacb87
.word 0x68f56d9b
.word 0x80f6d278
.word 0x093c9a8a
.word 0xcd3cfd7e
.word 0xdd8ebd5c
.word 0x293859f6
.word 0x4d2f8486
.word 0xae1bd593
.word 0xc65bc014
// expected output
.word 0x34df561b
.word 0xd2cfebbc
.word 0xb7af3b4b
.word 0x8d21ca52
.word 0x58312e7e
.word 0x2e4e538e
.word 0x35ad2490
.word 0xb6112f0d
.word 0x7f148f6a
.word 0xa8d522a7
.word 0xf3c61d78
.word 0x5bd667db
.word 0x0e1dc460
.word 0x6c318ea4
.word 0xf26af4fe
.word 0x7d11d4dc
.word 0xff045651
.word 0x1b4aed1a
.word 0x0d91ba4a
.word 0x1fd6cd90
.word 0x29187bc5
.word 0x881a5a07
.word 0xfe02049d
.word 0x39368e83
.word 0x139b1282
.word 0x5bae2c7b
.word 0xe81e6f12
.word 0xc61bb5c5
// CBCMMT256_vector8
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000008
// start of key
.word 0x458b67bf
.word 0x212d20f3
.word 0xa57fce39
.word 0x2065582d
.word 0xcefbf381
.word 0xaa22949f
.word 0x8338ab90
.word 0x52260e1d
// start of IV
.word 0x4c12effc
.word 0x5963d404
.word 0x59602675
.word 0x153e9649
// input message
.word 0x256fd73c
.word 0xe35ae3ea
.word 0x9c25dd2a
.word 0x9454493e
.word 0x96d8633f
.word 0xe633b561
.word 0x76dce878
.word 0x5ce5dbbb
.word 0x84dbf2c8
.word 0xa2eeb1e9
.word 0x6b518996
.word 0x05e4f13b
.word 0xbc11b93b
.word 0xf6f39b34
.word 0x69be1485
.word 0x8b5b720d
.word 0x4a522d36
.word 0xfeed7a32
.word 0x9c9b1e85
.word 0x2c9280c4
.word 0x7db8039c
.word 0x17c49215
.word 0x71a07d18
.word 0x64128330
.word 0xe09c308d
.word 0xdea1694e
.word 0x95c84500
.word 0xf1a61e61
.word 0x4197e86a
.word 0x30ecc28d
.word 0xf64ccb3c
.word 0xcf5437aa
// expected output
.word 0x90b7b963
.word 0x0a2378f5
.word 0x3f501ab7
.word 0xbeff0391
.word 0x55008071
.word 0xbc8438e7
.word 0x89932cfd
.word 0x3eb12991
.word 0x95465e66
.word 0x33849463
.word 0xfdb44375
.word 0x278e2fdb
.word 0x1310821e
.word 0x6492cf80
.word 0xff15cb77
.word 0x2509fb42
.word 0x6f3aeee2
.word 0x7bd49388
.word 0x82fd2ae6
.word 0xb5bd9d91
.word 0xfa4a43b1
.word 0x7bb439eb
.word 0xbe59c042
.word 0x310163a8
.word 0x2a5fe538
.word 0x8796eee3
.word 0x5a181a12
.word 0x71f00be2
.word 0x9b852d8f
.word 0xa759bad0
.word 0x1ff4678f
.word 0x010594cd
// CBCMMT256_vector9
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x00000009
// start of key
.word 0xd2412db0
.word 0x845d84e5
.word 0x732b8bbd
.word 0x64295747
.word 0x3b81fb99
.word 0xca8bff70
.word 0xe7920d16
.word 0xc1dbec89
// start of IV
.word 0x51c619fc
.word 0xf0b23f0c
.word 0x7925f400
.word 0xa6cacb6d
// input message
.word 0x026006c4
.word 0xa71a180c
.word 0x9929824d
.word 0x9d095b8f
.word 0xaaa86fc4
.word 0xfa25ecac
.word 0x61d85ff6
.word 0xde92dfa8
.word 0x702688c0
.word 0x2a282c1b
.word 0x8af44497
.word 0x07f22d75
.word 0xe9199101
.word 0x5db22374
.word 0xc95f8f19
.word 0x5d5bb0af
.word 0xeb03040f
.word 0xf8965e0e
.word 0x1339dba5
.word 0x653e174f
.word 0x8aa5a1b3
.word 0x9fe3ac83
.word 0x9ce307a4
.word 0xe44b4f8f
.word 0x1b0063f7
.word 0x38ec18ac
.word 0xdbff2ebf
.word 0xe07383e7
.word 0x34558723
.word 0xe741f0a1
.word 0x836dafdf
.word 0x9de82210
.word 0xa9248bc1
.word 0x13b3c1bc
.word 0x8b4e252c
.word 0xa01bd803
// expected output
.word 0x0254b234
.word 0x63bcabec
.word 0x5a395eb7
.word 0x4c8fb0eb
.word 0x137a07bc
.word 0x6f5e9f61
.word 0xec0b057d
.word 0xe305714f
.word 0x8fa29422
.word 0x1c91a159
.word 0xc315939b
.word 0x81e300ee
.word 0x902192ec
.word 0x5f152544
.word 0x28d8772f
.word 0x79324ec4
.word 0x3298ca21
.word 0xc00b3702
.word 0x73ee5e5e
.word 0xd90e43ef
.word 0xa1e05a5d
.word 0x171209fe
.word 0x34f9f292
.word 0x37dba2a6
.word 0x726650fd
.word 0x3b132174
.word 0x7d120886
.word 0x3c6c3c6b
.word 0x3e2d879a
.word 0xb5f25782
.word 0xf08ba8f2
.word 0xabbe63e0
.word 0xbedb4a22
.word 0x7e81afb3
.word 0x6bb66455
.word 0x08356d34
// CBCMMT256_vector10
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000003
// indicates message length, multiply of 128
.word 0x0000000A
// start of key
.word 0x48be597e
.word 0x632c1677
.word 0x2324c8d3
.word 0xfa1d9c5a
.word 0x9ecd010f
.word 0x14ec5d11
.word 0x0d3bfec3
.word 0x76c5532b
// start of IV
.word 0xd6d581b8
.word 0xcf04ebd3
.word 0xb6eaa1b5
.word 0x3f047ee1
// input message
.word 0x0c63d413
.word 0xd3864570
.word 0xe70bb661
.word 0x8bf8a4b9
.word 0x58558668
.word 0x8c32bba0
.word 0xa5ecc136
.word 0x2fada74a
.word 0xda32c52a
.word 0xcfd1aa74
.word 0x44ba567b
.word 0x4e7daaec
.word 0xf7cc1cb2
.word 0x9182af16
.word 0x4ae5232b
.word 0x00286869
.word 0x56355998
.word 0x07a9a7f0
.word 0x7a1f137e
.word 0x97b1e1c9
.word 0xdabc89b6
.word 0xa5e4afa9
.word 0xdb5855ed
.word 0xaa575056
.word 0xa8f4f824
.word 0x2216242b
.word 0xb0c25631
.word 0x0d9d3298
.word 0x26ac353d
.word 0x715fa39f
.word 0x80cec144
.word 0xd6424558
.word 0xf9f70b98
.word 0xc920096e
.word 0x0f2c855d
.word 0x594885a0
.word 0x0625880e
.word 0x9dfb7341
.word 0x63cecef7
.word 0x2cf030b8
// expected output
.word 0xfc5873e5
.word 0x0de8faf4
.word 0xc6b84ba7
.word 0x07b0854e
.word 0x9db9ab2e
.word 0x9f7d707f
.word 0xbba338c6
.word 0x843a18fc
.word 0x6facebaf
.word 0x663d2629
.word 0x6fb329b4
.word 0xd26f1849
.word 0x4c79e09e
.word 0x779647f9
.word 0xbafa8748
.word 0x9630d79f
.word 0x4301610c
.word 0x2300c19d
.word 0xbf3148b7
.word 0xcac8c4f4
.word 0x94410275
.word 0x4f332e92
.word 0xb6f7c5e7
.word 0x5bc6179e
.word 0xb877a078
.word 0xd4719009
.word 0x021744c1
.word 0x4f13fd2a
.word 0x55a2b9c4
.word 0x4d180006
.word 0x85a845a4
.word 0xf632c7c5
.word 0x6a77306e
.word 0xfa66a24d
.word 0x05d088dc
.word 0xd7c13fe2
.word 0x4fc44727
.word 0x5965db9e
.word 0x4d37fbc9
.word 0x304448cd
// CBCMMT256_vector11
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x0000000A
// start of key
.word 0x43e953b2
.word 0xaea08a3a
.word 0xd52d182f
.word 0x58c72b9c
.word 0x60fbe4a9
.word 0xca46a3cb
.word 0x89e38638
.word 0x45e22c9e
// start of IV
.word 0xddbbb017
.word 0x3f1e2deb
.word 0x2394a62a
.word 0xa2a0240e
// input message
.word 0x0c63d413
.word 0xd3864570
.word 0xe70bb661
.word 0x8bf8a4b9
.word 0x58558668
.word 0x8c32bba0
.word 0xa5ecc136
.word 0x2fada74a
.word 0xda32c52a
.word 0xcfd1aa74
.word 0x44ba567b
.word 0x4e7daaec
.word 0xf7cc1cb2
.word 0x9182af16
.word 0x4ae5232b
.word 0x00286869
.word 0x56355998
.word 0x07a9a7f0
.word 0x7a1f137e
.word 0x97b1e1c9
.word 0xdabc89b6
.word 0xa5e4afa9
.word 0xdb5855ed
.word 0xaa575056
.word 0xa8f4f824
.word 0x2216242b
.word 0xb0c25631
.word 0x0d9d3298
.word 0x26ac353d
.word 0x715fa39f
.word 0x80cec144
.word 0xd6424558
.word 0xf9f70b98
.word 0xc920096e
.word 0x0f2c855d
.word 0x594885a0
.word 0x0625880e
.word 0x9dfb7341
.word 0x63cecef7
.word 0x2cf030b8
// expected output
.word 0xd51d19de
.word 0xd5ca4ae1
.word 0x4b2b20b0
.word 0x27ffb020
// CBCMMT256_vector12
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000001
// start of key
.word 0xaddf88c1
.word 0xab997eb5
.word 0x8c045528
.word 0x8c3a4fa3
.word 0x20ada8c1
.word 0x8a69cc90
.word 0xaa99c73b
.word 0x174dfde6
// start of IV
.word 0x60cc50e0
.word 0x887532e0
.word 0xd4f3d2f2
.word 0x0c3c5d58
// input message
.word 0x07270d0e
.word 0x63aa36da
.word 0xed8c6ade
.word 0x13ac1af1
// expected output
.word 0x6cb4e2f4
.word 0xddf79a8e
.word 0x08c96c7f
.word 0x4040e8a8
.word 0x3266c07f
.word 0xc88dd007
.word 0x4ee25b00
.word 0xd445985a
// CBCMMT256_vector13
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000002
// start of key
.word 0x54682728
.word 0xdb5035eb
.word 0x04b79645
.word 0xc64a9560
.word 0x6abb6ba3
.word 0x92b6633d
.word 0x79173c02
.word 0x7c5acf77
// start of IV
.word 0x2eb94297
.word 0x77285196
.word 0x3dd39a1e
.word 0xb95d438f
// input message
.word 0x98a8a9d8
.word 0x4356bf40
.word 0x3a9ccc38
.word 0x4a06fe04
.word 0x3dfeecb8
.word 0x9e59ce0c
.word 0xb8bd0a49
.word 0x5ef76cf0
// expected output
.word 0xe4046d05
.word 0x385ab789
.word 0xc6a72866
.word 0xe08350f9
.word 0x3f583e2a
.word 0x005ca0fa
.word 0xecc32b5c
.word 0xfc323d46
.word 0x1c76c107
.word 0x307654db
.word 0x5566a5bd
.word 0x693e227c
// CBCMMT256_vector14
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000003
// start of key
.word 0x7482c470
.word 0x04aef406
.word 0x115ca5fd
.word 0x499788d5
.word 0x82efc0b2
.word 0x9dc9e951
.word 0xb1f95940
.word 0x6693a54f
// start of IV
.word 0x485ebf22
.word 0x15d20b81
.word 0x6ea53944
.word 0x829717ce
// input message
.word 0x0faa5d01
.word 0xb9afad3b
.word 0xb519575d
.word 0xaaf4c60a
.word 0x5ed4ca2b
.word 0xa20c625b
.word 0xc4f08799
.word 0xaddcf89d
.word 0x19796d1e
.word 0xff0bd790
.word 0xc622dc22
.word 0xc1094ec7
// expected output
.word 0x6c24f19b
.word 0x9c0b18d7
.word 0x126bf680
.word 0x90cb8ae7
.word 0x2db3ca7e
.word 0xabb594f5
.word 0x06aae7a2
.word 0x493e5326
.word 0xa5afae4e
.word 0xc4d10937
.word 0x5b56e2b6
.word 0xff4c9cf6
.word 0x39e72c63
.word 0xdc8114c7
.word 0x96df95b3
.word 0xc6b62021
// CBCMMT256_vector15
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000004
// start of key
.word 0x3ae38d4e
.word 0xbf7e7f6d
.word 0xc0a1e31e
.word 0x5efa7ca1
.word 0x23fdc321
.word 0xe533e79f
.word 0xedd5132c
.word 0x5999ef5b
// start of IV
.word 0x36d55dc9
.word 0xedf8669b
.word 0xeecd9a2a
.word 0x029092b9
// input message
.word 0x82fec664
.word 0x466d5850
.word 0x23821c2e
.word 0x39a0c433
.word 0x45669a41
.word 0x244d0501
.word 0x8a23d715
.word 0x9515f8ff
.word 0x4d88b01c
.word 0xd0eb8307
.word 0x0d0077e0
.word 0x65d74d73
.word 0x73816b61
.word 0x505718f8
.word 0xd4f27028
.word 0x6a59d45e
// expected output
.word 0xd50ea48c
.word 0x8962962f
.word 0x7c3d301f
.word 0xa9f87724
.word 0x5026c204
.word 0xa7771292
.word 0xcddca1e7
.word 0xffebbef0
.word 0x0e86d729
.word 0x10b7d8a7
.word 0x56dfb45c
.word 0x9f104097
.word 0x8bb748ca
.word 0x537edd90
.word 0xb670ecee
.word 0x375e15d9
.word 0x8582b9f9
.word 0x3b6355ad
.word 0xc9f80f4f
.word 0xb2108fb9
// CBCMMT256_vector16
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000005
// start of key
.word 0xd30bfc0b
.word 0x2a19d5b8
.word 0xb6f8f46a
.word 0xb7f444ee
.word 0x136a7fa3
.word 0xfbdaf530
.word 0xcc3e8976
.word 0x339afcc4
// start of IV
.word 0x80be76a7
.word 0xf885d2c0
.word 0x6b37d6a5
.word 0x28fae0cd
// input message
.word 0x8d22db30
.word 0xc4253c3e
.word 0x3add9685
.word 0xc14d55b0
.word 0x5f7cf762
.word 0x6c52cccf
.word 0xcbe9b99f
.word 0xd8913663
.word 0xb8b1f22e
.word 0x277a4cc3
.word 0xd0e7e978
.word 0xa34782eb
.word 0x87686755
.word 0x6ad47284
.word 0x86d5e890
.word 0xea738243
.word 0xe3700a69
.word 0x6d6eb58c
.word 0xd81c0e60
.word 0xeb121c50
// expected output
.word 0x31e4677a
.word 0x17aed120
.word 0xbd3af69f
.word 0xbb0e4b64
.word 0x5b9e8c10
.word 0x4e280b79
.word 0x9ddd49f1
.word 0xe241c3cc
.word 0xb7d40e1c
.word 0x6ff226bf
.word 0x04f8049c
.word 0x51a86e29
.word 0x81cf1331
.word 0xc824d7d4
.word 0x51746ccf
.word 0x77fc22fd
.word 0x3717001e
.word 0xe51913d8
.word 0x1f7a06fb
.word 0x0037f309
.word 0x957579f6
.word 0x95670f2c
.word 0x4c7397d2
.word 0xd990374e
// CBCMMT256_vector17
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000006
// start of key
.word 0x64a256a6
.word 0x63527ebe
.word 0xa71f8d77
.word 0x0990b4ce
.word 0xe4a2d3af
.word 0xbfd33fb1
.word 0x2c7ac300
.word 0xef59e49a
// start of IV
.word 0x18cce914
.word 0x7f295c5c
.word 0x00dbe042
.word 0x4089d3b4
// input message
.word 0x0b6e2a82
.word 0x13169b3b
.word 0x78db6de3
.word 0x24e286f0
.word 0x366044e0
.word 0x35c6970a
.word 0xfbf0a1a5
.word 0xc32a05b2
.word 0x4ba706cd
.word 0x9c660973
.word 0x7651a81b
.word 0x2bcf4c68
.word 0x1dc08619
.word 0x83a5aec7
.word 0x6e6c8b24
.word 0x4112d64d
.word 0x489e8432
.word 0x89747373
.word 0x94b83a39
.word 0x45901172
.word 0x7162652b
.word 0x7aa793bf
.word 0xb1b71488
.word 0xb7dec96b
// expected output
.word 0xd9977196
.word 0x3b7ae520
.word 0x2e382ff8
.word 0xc06e0353
.word 0x67909cd2
.word 0x4fe5ada7
.word 0xf3d39bfa
.word 0xeb5de98b
.word 0x04eaf498
.word 0x9648e001
.word 0x12f0d2aa
.word 0xdb8c5f21
.word 0x57b64581
.word 0x45035996
.word 0x5140c141
.word 0xe5fb631e
.word 0x43469d65
.word 0xd1b7370e
.word 0xb3b39639
.word 0x9fec32cc
.word 0xed294a5e
.word 0xee46d654
.word 0x7f7bbd49
.word 0xdee148b4
.word 0xbc31d6c4
.word 0x93cfd28f
.word 0x3908e36c
.word 0xb698629d
// CBCMMT256_vector18
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000007
// start of key
.word 0x31358e8a
.word 0xf34d6ac3
.word 0x1c958bbd
.word 0x5c8fb33c
.word 0x334714bf
.word 0xfb41700d
.word 0x28b07f11
.word 0xcfe891e7
// start of IV
.word 0x14451624
.word 0x6a752c32
.word 0x9056d884
.word 0xdaf3c89d
// input message
.word 0xf7e0f79c
.word 0xfddd15ed
.word 0x3600ab2d
.word 0x29c56ba3
.word 0xc8e96d1a
.word 0x896aff6d
.word 0xec773e6e
.word 0xa4710a77
.word 0xf2f4ec64
.word 0x6b76efda
.word 0x6428c175
.word 0xd007c84a
.word 0xa9f4b18c
.word 0x5e1bac5f
.word 0x27f7307b
.word 0x737655ee
.word 0xe813f7e1
.word 0xf5880a37
.word 0xac63ad16
.word 0x66e78830
.word 0x83b64845
.word 0x4d45786f
.word 0x53ea3db1
.word 0xb5129291
.word 0x138abe40
.word 0xc79fcb7a
.word 0xb7c6f6b9
.word 0xea133b5f
// expected output
.word 0xb32e2b17
.word 0x1b638270
.word 0x34ebb0d1
.word 0x909f7ef1
.word 0xd51c5f82
.word 0xc1bb9bc2
.word 0x6bc4ac4d
.word 0xccdee835
.word 0x7dca6154
.word 0xc2510ae1
.word 0xc87b1b42
.word 0x2b02b621
.word 0xbb06cac2
.word 0x80023894
.word 0xfcff3406
.word 0xaf08ee9b
.word 0xe1dd7241
.word 0x9beccddf
.word 0xf77c722d
.word 0x992cdcc8
.word 0x7e9c7486
.word 0xf56ab406
.word 0xea608d8c
.word 0x6aeb060c
.word 0x64cf2785
.word 0xad1a1591
.word 0x47567e39
.word 0xe303370d
.word 0xa4452475
.word 0x26d95942
.word 0xbf4d7e88
.word 0x057178b0
// CBCMMT256_vector19
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000008
// start of key
.word 0x5b4b6933
.word 0x9891db4e
.word 0x3337c348
.word 0x6f439dfb
.word 0xd0fb2a78
.word 0x2ca71ef0
.word 0x059819d5
.word 0x1669d93c
// start of IV
.word 0x2b28a2d1
.word 0x9ba9ecd1
.word 0x49dae966
.word 0x22c21769
// input message
.word 0xcfc155a3
.word 0x967de347
.word 0xf58fa2e8
.word 0xbbeb4183
.word 0xd6d32f74
.word 0x27155e6a
.word 0xb39cddf2
.word 0xe627c572
.word 0xacae02f1
.word 0xf243f3b7
.word 0x84e73e21
.word 0xe7e520ea
.word 0xcd3befaf
.word 0xbee81486
.word 0x7334c6ee
.word 0x8c2f0ee7
.word 0x376d3c72
.word 0x728cde78
.word 0x13173dbd
.word 0xfe3357de
.word 0xac41d3ae
.word 0x2a04229c
.word 0x0262f2d1
.word 0x09d01f5d
.word 0x03e7f848
.word 0xfb50c288
.word 0x49146c02
.word 0xa2f4ebf7
.word 0xd7ffe3c9
.word 0xd40e3197
.word 0x0bf15187
.word 0x3672ef2b
// expected output
.word 0xba21db8e
.word 0xc170fa4d
.word 0x73cfc381
.word 0x687f3fa1
.word 0x88dd2d01
.word 0x2bef4800
.word 0x7f3dc883
.word 0x29e22ba3
.word 0x2fe235a3
.word 0x15be3625
.word 0x46468b9d
.word 0xb6af6705
.word 0xc6e5d4d3
.word 0x6822f428
.word 0x83c08d4a
.word 0x994cc454
.word 0xa7db292c
.word 0x4ca1f4b6
.word 0x2ebf8e47
.word 0x9a5d545d
.word 0x6af9978d
.word 0x2cfee7bc
.word 0x80999192
.word 0xc2c8662c
.word 0xe9b4be11
.word 0xaf40bd68
.word 0xf3e2d568
.word 0x5bb28c0f
.word 0x3dc08017
.word 0xc0aba826
.word 0x3e6fdc45
.word 0xed7f9893
.word 0xbf14fd3a
.word 0x86c418a3
.word 0x5c5667e6
.word 0x42d59985
// CBCMMT256_vector20
// indicates op mode and key length, write to AES_ADDR_CONFIG
.word 0x00000002
// indicates message length, multiply of 128
.word 0x00000009
// start of key
.word 0x87725bd4
.word 0x3a456088
.word 0x14180773
.word 0xf0e7ab95
.word 0xa3c859d8
.word 0x3a2130e8
.word 0x84190e44
.word 0xd14c6996
// start of IV
.word 0xe4965198
.word 0x8ebbb72e
.word 0xb8bb80bb
.word 0x9abbca34
// input message
.word 0xa0bb1d2f
.word 0xdeb7e6bf
.word 0x34c690fe
.word 0x7b72a5e9
.word 0xd65796aa
.word 0x57982fe3
.word 0x40c286d6
.word 0x923dbddb
.word 0x426566ff
.word 0x58e9c0b3
.word 0xaf52e4db
.word 0x446f6cc5
.word 0xdaa5bfcf
.word 0x4e3c85db
.word 0x5a5638e6
.word 0x70c370cc
.word 0xe128db22
.word 0xc97542a6
.word 0x4a63846f
.word 0x18a228d3
.word 0x462a1137
.word 0x6dcb71f6
.word 0x6ec52ebd
.word 0xa474f7b6
.word 0x752915b0
.word 0x80179797
.word 0x4bc51eb1
.word 0x218127fe
.word 0xd60f1009
.word 0x430eb508
.word 0x9fb3ba5f
.word 0x28fad24c
.word 0x518ccddc
.word 0x2501393c
.word 0xeb6dffc4
.word 0x6a159421
// expected output
.word 0x5b97a9d4
.word 0x23f4b974
.word 0x13f388d9
.word 0xa341e727
.word 0xbb339f8e
.word 0x18a3fac2
.word 0xf2fb85ab
.word 0xdc8f135d
.word 0xeb30054a
.word 0x1afdc9b6
.word 0xed7da16c
.word 0x55eba6b0
.word 0xd4d10c74
.word 0xe1d9a7cf
.word 0x8edfaeaa
.word 0x684ac0bd
.word 0x9f9d24ba
.word 0x674955c7
.word 0x9dc6be32
.word 0xaee1c260
.word 0xb558ff07
.word 0xe3a4d49d
.word 0x24162011
.word 0xff254db8
.word 0xbe078e8a
.word 0xd07e648e
.word 0x6bf56793
.word 0x76cb4321
.word 0xa5ef01af
.word 0xe6ad8816
.word 0xfcc76346
.word 0x69c8c438
.word 0x9295c924
.word 0x1e45fff3
.word 0x9f3225f7
.word 0x745032da
.word 0xeebe99d4
.word 0xb19bcb21
.word 0x5d1bfdb3
.word 0x6eda2c24

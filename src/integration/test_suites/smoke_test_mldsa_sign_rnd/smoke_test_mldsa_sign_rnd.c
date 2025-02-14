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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "mldsa.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// ALL TEST VECTORS IN BIG-ENDIAN PRESENTATION

const uint32_t mldsa_msg[] = {
0xe188167d, 0x57d2657d, 0x20df4f23, 0x39a0d967, 0xd458b199, 0x5e79f3ea, 0x26d4c2c8, 0x87738f2b, 
0xee512acd, 0xd39ee02d, 0xb38783d7, 0x3ea94ec3, 0x213fdc05, 0x7a4d5378, 0x952b4683, 0x1f9de5bc
};

   
const uint32_t mldsa_privkey[] = {
0xc7c4546f, 0x937fc1da, 0x061086c6, 0x1603bbe9, 0x5ea902a5, 0x8212a345, 0xe9e46295, 0x363a26cf, 
0xf8572ab0, 0xd7d3c099, 0x28f32a04, 0x2be75021, 0x8f835018, 0x1df5806c, 0x880b0134, 0xbe19114b, 
0x6288cf3e, 0xda533e0d, 0x213913ee, 0x0afc9e09, 0x4a912e2f, 0x14e28748, 0x95f807aa, 0xc2218778, 
0xdec66326, 0x76e0c7b4, 0x2b6cb83d, 0xd4e313e9, 0x01bc0651, 0x0fef7d1b, 0x22c8562a, 0x81bd35a9, 
0xf6be72f9, 0x151474f0, 0x524d2bfc, 0x2685db69, 0x43123fd2, 0xede4bb9d, 0x6f8247f6, 0xd72a5626, 
0x68a00725, 0x9facd44c, 0xb81077ad, 0x34d4bc71, 0xca32e72f, 0x9217be9a, 0x9ff5ff4e, 0x4d3f0251, 
0x5a0a575f, 0xc5b4c0d1, 0xf2ae0fdb, 0xab048d45, 0x6c1c53ea, 0x5e25e344, 0xb3e444a8, 0x93bd628c, 
0x1ca9dd77, 0x6d87b230, 0x620099b2, 0x2af4e060, 0xd8fcbfd5, 0xc3041413, 0x619bf0c1, 0x5908620b, 
0xae708cd2, 0x08cf3e40, 0xbd48cbe9, 0xe7b2b310, 0xe8832591, 0xc861aad8, 0xe4b6cc9b, 0xce6674b4, 
0x3d2e6040, 0x8922e3ac, 0x7cb0530b, 0xe850a618, 0x2648955d, 0x7d3823b4, 0x8988c81e, 0xaf8615c8, 
0x0f4a6f62, 0x1999ecca, 0x01555eb2, 0x709c687d, 0x04b747e8, 0xe3927c70, 0x1c5c68af, 0x14f3f52b, 
0xa8964a30, 0x1d356692, 0x4f0bb2b2, 0xbca5c6cd, 0x0087fcf0, 0x235f7c47, 0x76ca2757, 0x5f3aedfe, 
0x82a82cf2, 0xc1af6333, 0x79a6f9f1, 0x58e15a44, 0x0a819561, 0x3ebf6741, 0x15d952d6, 0x3a59fecf, 
0x8fe4c845, 0x4d5e08ae, 0x98f1d7b9, 0x3cd662cf, 0xec5c0552, 0x98ce922f, 0x6d3298cd, 0x77faa3ea, 
0xf4d55a46, 0x792ae6f1, 0xd41995a8, 0x97858ce3, 0x2741312d, 0x55cabf41, 0x02432a66, 0xe792d087, 
0xd27e988e, 0x20e724b3, 0xa2dd38fb, 0x02397717, 0x05e3828d, 0xc67c5ea6, 0x65131d10, 0x23d74941, 
0x35c41219, 0xa3b69ab9, 0x9a2db412, 0x5f43c811, 0x603680b3, 0xdf5b57e4, 0x9cf4be8b, 0x07fa89da, 
0xcf652869, 0x922924cf, 0x408996de, 0x79c4f763, 0x95ea7706, 0x8f56a0fe, 0x0da983f9, 0xb890d90c, 
0x2f2eeb7a, 0xba31d51c, 0xa3745e94, 0xe375c629, 0xfebb0706, 0x05e4c3fb, 0x32918699, 0x38a5f8c7, 
0xa3d4bb8f, 0x7ca5ccdc, 0x93e5b37f, 0x7b52e06e, 0x5031aaaa, 0x8d3cb793, 0x23b472d3, 0x96fffcd3, 
0xea8533ca, 0x6bdf379c, 0x53541561, 0x48eac610, 0x3cad3c2f, 0xb359a99b, 0x2df89c8e, 0x66b309aa, 
0x6e29faaa, 0x7d3f2f4b, 0x5363736c, 0xd0a65ea9, 0xa1dc9fd6, 0xef302dfa, 0x139032ba, 0xd7c6d228, 
0x133d42fb, 0x67dbbc13, 0xf04c064b, 0x9456293a, 0xc90f39a9, 0x595dcde2, 0xcaa59360, 0x81a588ea, 
0x26741f22, 0xb2a16232, 0x18c328ea, 0xb231a2bf, 0x572590f9, 0x84591e90, 0x48db3475, 0xacd0dcd3, 
0x81918ed6, 0x2bc5c1ba, 0x734bb239, 0x2dd98ba3, 0x81006ffc, 0xe61cde92, 0x620779d5, 0x2446df05, 
0x76e7d6bc, 0x078ce366, 0x3ff598e6, 0x32e4b64f, 0x1c0b30a5, 0x21b9ddf3, 0x4fe73482, 0xa141e2e3, 
0x5a165064, 0x5d983f17, 0x4ced230e, 0x97f2fa11, 0x73ef4371, 0x8a59843e, 0xd0a77a78, 0xf9b47685, 
0x82fb9a1b, 0xf1bcfa64, 0xbecf5248, 0x6f97b636, 0x9794e15e, 0xd3c14413, 0x08360c38, 0x2b2f6999, 
0x4ceb5417, 0xd0cc67d7, 0x86d60e28, 0xd29f6a3c, 0xa213d5f3, 0xf2561513, 0x46329b7b, 0x6a247a0c, 
0x62cb2de6, 0xb159c3e2, 0x03209ce9, 0xb5b3d6d2, 0xff592b61, 0x0ca792b4, 0x220c694b, 0xfaa1e743, 
0x71888ab4, 0x4e71d048, 0x99bc84a3, 0xba58f614, 0x96f3b24d, 0x85e43e10, 0xcd51e4ff, 0x392673ab, 
0xe3ec957d, 0xc1599838, 0xbda57321, 0x366ddd3d, 0xb4556fd6, 0x0e3858df, 0x4b62125c, 0x6887808f, 
0x1c05a8e1, 0x7ce8f0a6, 0xe9ea7bc7, 0x48c9cd1f, 0x1e879312, 0xd55259b8, 0x615b32da, 0x2d8c37bd, 
0x3fd1623d, 0x0dd14cc1, 0x77c64a70, 0x57b6f6a6, 0x3f398a3a, 0x1003579a, 0x5886aea8, 0x30ecbcef, 
0x19f2a016, 0xeafb5b28, 0x87382595, 0x9df1efa1, 0x2ea00482, 0xfce3e33f, 0xe1402467, 0x1b835625, 
0x48701aef, 0x7b882897, 0xf8fd9da7, 0xe159121c, 0x7b174421, 0xc221866a, 0xead369fe, 0xe8e15ff0, 
0xf9b80657, 0xefbf4bec, 0xa9d82c94, 0x8473d631, 0x38decb72, 0x68cdcc6d, 0x71d55e82, 0xfbb419cf, 
0xdcf9ca79, 0x8584fc64, 0xdc4ff360, 0x89491358, 0xbbe8f7b3, 0x1424b1f6, 0x5988ce6a, 0x85e2bffd, 
0x795b2df1, 0xcaad8304, 0x36461c77, 0x4073e021, 0x23ec290d, 0x788d9d5a, 0x4ce3f0be, 0x04b36270, 
0x274401fd, 0xbce65d45, 0xd7307dc7, 0x99392368, 0xfd98e147, 0x6388ca03, 0xd68226ef, 0x8b263ca8, 
0xf8088795, 0xecbd9e05, 0x14e7309d, 0xbf32358a, 0x249f95f2, 0x1e8959e9, 0xadc514f5, 0xa5dd5b62, 
0x28298fef, 0x60774283, 0x83092226, 0x8568d5b1, 0xa4071109, 0x082f300a, 0x2919aa3b, 0xf265c0b5, 
0xfac09302, 0xa7bb0511, 0xc11fcf7b, 0x275f9187, 0xc309e173, 0xeaa6d261, 0xcc6cf081, 0xdf2e6259, 
0xeb313c24, 0x813bb9be, 0x2a46db46, 0x4e8f773f, 0x24da6819, 0x5f05b685, 0x55c39b95, 0x8c03a766, 
0x555042bc, 0x3bdb4e12, 0xad439321, 0x4a5b0c83, 0x6bdc68e7, 0x8292cb46, 0xd7eda854, 0x7705ee32, 
0x40f595e5, 0xcf09950f, 0x45b47e35, 0x3173cc87, 0x303569ac, 0x10e24102, 0x0aae8b35, 0x784dbfc8, 
0xf83c3da6, 0x7a8b7b36, 0xce74ab5f, 0xf8e35102, 0x8fd992ee, 0x33e8513f, 0x18d260f2, 0xf24a0429, 
0x62a893dd, 0xf22d6212, 0xc02bc1cb, 0xa9f0ee88, 0xece3ea86, 0x96b54148, 0xf6beade6, 0xd1dcabda, 
0xb9f6421a, 0xf2d09f2a, 0x64bec65e, 0x7833269a, 0x3e888fa6, 0x3a21b6d5, 0xf9f2737d, 0x52dfddae, 
0xf3731136, 0xe7b51c15, 0xfb7d73da, 0x4c3b6350, 0x43a0f19e, 0x1ccf3e7c, 0xea298d55, 0x161950eb, 
0xbb8cab69, 0x299ed8f2, 0x884cee0f, 0x6eec851a, 0x1fbe8199, 0x2435494c, 0x0a691be3, 0xb3835d0b, 
0xd90fad6d, 0x90313cc5, 0xa946e1ae, 0xd4d86429, 0xf56086b3, 0xf2a3048c, 0xe4a01941, 0xdd62af04, 
0xf2ffe1a5, 0x6acba25d, 0x51853da3, 0x96beecc7, 0xc79e97d3, 0x8dc957b2, 0x06d47d06, 0xc2af5f4a, 
0x963e9cb6, 0xcb8f838a, 0xa28ea66b, 0x3c890e80, 0xaec95346, 0x830f7cd4, 0x720a470c, 0xc1eb3f39, 
0x6ebc24df, 0x88be8c19, 0x5eedf577, 0xbe88fd86, 0x238a0071, 0xb36b36b6, 0xc21edb73, 0x33170daf, 
0x099f06ab, 0x9bc2da5d, 0x571d335b, 0xa0f41505, 0x03e432e5, 0xd4dc3255, 0x995acc33, 0xd924d258, 
0xfd0ce078, 0x3b8567e9, 0x9719017a, 0xeb101f7b, 0x917e0c27, 0x39fced81, 0x91b1666b, 0xe17f813e, 
0x38c67986, 0x60da7049, 0x1baa1c72, 0xd01debb4, 0x80cf7a2f, 0x61759645, 0x3fb82014, 0xf5639ec9, 
0x76a8581f, 0x7a83186d, 0xec2b13db, 0x6258c6af, 0xaa245418, 0x1b78bed8, 0xfadb2d22, 0x8efcc700, 
0x6287fa21, 0xc0451786, 0x90b138e9, 0x346fa2b1, 0x76fb45df, 0x021cb69e, 0xdf9b1684, 0x634c6bd6, 
0x00a92236, 0xe052fbb5, 0x9aed1bf7, 0xda55b759, 0x1d698f81, 0x64ad48d2, 0xc7d1301c, 0xa16d2ba7, 
0xdfdfec46, 0x72f32bfa, 0xb2b2bf6e, 0x1627f518, 0xd24d1a2c, 0x00322927, 0x3795cef1, 0xb580b848, 
0xc93a22fc, 0xde7c82e7, 0xeed0b98a, 0x7c67f9b3, 0x4c53672e, 0x8467bf43, 0x3c6856fb, 0x66157ca2, 
0x4ecb2a79, 0xd45e701a, 0xaa7dc7d8, 0xe46ee2d1, 0x008c1d43, 0x4894f0fe, 0x5d2486c3, 0xa40b8c1d, 
0x02900cc6, 0xf8ed165e, 0xf3823af3, 0x7b5e8a4a, 0x2a03c135, 0x9e1cafe6, 0xd33d504a, 0x5944988b, 
0x2f31f042, 0x33274050, 0xbff6c998, 0x5bfca280, 0x80843ece, 0xc81cedaf, 0x5e069e8b, 0xc97d1cf0, 
0xa239adca, 0xdace6d27, 0x91b2ef7b, 0x0bdc9d72, 0x59bb117e, 0xcf1b5f40, 0x03cb14e7, 0xc8b4e523, 
0xec1bab49, 0x4a0853cc, 0x492db0d2, 0x82fbab95, 0xfdbefc9e, 0xfbe2a502, 0xa6dd93b8, 0xace92848, 
0x16be628b, 0x781425ca, 0x4de191f9, 0x32568adf, 0x23548d2c, 0x27a9def1, 0x7af32e6f, 0x2b29c1e5, 
0x9a199b9e, 0xf3ff2ece, 0xab26f369, 0xc16d4266, 0xb5c0d8a3, 0x289a0b83, 0x3bc255c4, 0x850b8714, 
0x9322733c, 0x7cd1a48d, 0xe7566e97, 0x4a684b16, 0x1784774c, 0x2941d983, 0x36e1e004, 0x01c82f15, 
0xd1b51c34, 0x86d12e7e, 0x7c825fe0, 0x5f308f2d, 0x4bebdd79, 0x0a20a94e, 0xe3d39bed, 0xf5c42729, 
0x4b79e062, 0xefee413e, 0xc94508dd, 0x513d95e5, 0x9b9cf99b, 0xca0f5588, 0x5cf0f4f5, 0x87d09087, 
0xbe8150a2, 0x6391f4e4, 0x09151ad5, 0x7140a53f, 0xd0f10b61, 0xeeebd74a, 0xc0414d0a, 0x9486743f, 
0xd81ee595, 0x72f40a4d, 0x05fc46f9, 0xac834d89, 0xea7af712, 0x7416348e, 0x9bb923b5, 0x8b53349e, 
0xa0eb7989, 0xf87fe604, 0x0c72c363, 0x878cb78e, 0xa317b43c, 0x420e8bfe, 0x22352552, 0x18a73fcf, 
0xd6e22de7, 0x855d4acc, 0x0850e7f2, 0x9cd47018, 0x009f1690, 0x4861f076, 0x0a99a662, 0x599ca584, 
0xdfa6c994, 0x48af8c35, 0x4276d946, 0x6a39b9bb, 0x5d6f937a, 0x9a9671ee, 0x72344a8d, 0xae131ac5, 
0x1e657b97, 0x25cf3f65, 0x6df16119, 0xefd4b0c1, 0x455dc679, 0xec2362cb, 0xc3b0ebf6, 0xd24d8931, 
0x6d6817d0, 0xf794b42a, 0x3d4603c1, 0x1dfa9a2a, 0x271ec2a0, 0x42cf035e, 0x99420289, 0x8600a824, 
0xb17b29bd, 0xa3811a7f, 0x078c1087, 0x6f898812, 0xd8d4fb1a, 0x51b9cd3b, 0xbc6bd595, 0x1a207905, 
0xea388879, 0xeb56f6b6, 0xa93b0156, 0xf5e38627, 0xbfebd0f5, 0x8215b8b1, 0xd7995d7f, 0x6e866f2c, 
0xaced6081, 0x53e18345, 0x980c210a, 0x50e0de00, 0x31c94e8c, 0x6b529c6e, 0xbbd892df, 0x7778b56d, 
0x0a915bcf, 0x5582197d, 0x83ed530c, 0x629df31c, 0x76d0a8a6, 0xd6493af8, 0x254cbf89, 0xdf7b53e3, 
0x2bae75b3, 0x2fdeccdb, 0xbf25c7bb, 0xdddedebd, 0x33794bc6, 0x5a9ed7bc, 0x76679d5c, 0x2becb247, 
0x172c4f90, 0xc165cee3, 0x6c6165d6, 0xdaf04fb1, 0x6e15727c, 0x886f38fe, 0xca65a1cb, 0x8ba9a2c4, 
0xb910d165, 0xe31dd3ea, 0x3369f06e, 0xe554afd4, 0x3a656b58, 0xb2f0d15f, 0xc7706cd6, 0xc8d8caac, 
0x337b763a, 0x1416c342, 0xe0f138ea, 0xfc609eca, 0x0e4a5375, 0xf25c8f76, 0xa99f8df6, 0xa33d7e8f, 
0x0fbee035, 0x0dbc4619, 0xdccb8a84, 0x3a9cd2f8, 0x00aaa31b, 0x6428e34e, 0xd109b8fc, 0xda2a1902, 
0xc698791c, 0x0bd846c4, 0xaaa500da, 0x4dd58a39, 0xd20b7635, 0x13cf4703, 0x6cd17b48, 0xfea95af0, 
0x8720b5e5, 0x7e8b96df, 0x41cbb443, 0x72039ffb, 0x8ed77869, 0x9526a1a6, 0x437b4170, 0x7fc54181, 
0x857dc94d, 0x7f5e13fb, 0x1e154b4f, 0x5e910dce, 0x92f7d8d2, 0x806cbeed, 0x198174b3, 0x4e39859c, 
0x95cb062f, 0xc50a3cec, 0x52384147, 0x091beb09, 0x4eaa85e0, 0xe972de3b, 0xebd10277, 0x80fe0d4f, 
0xecace02c, 0xcdaf368a, 0xb38c5a95, 0x77575147, 0xd60dd23e, 0x689bf475, 0x4a792884, 0x360f7104, 
0x2b15230d, 0x2175e69f, 0x265d5e59, 0xcec3ac4a, 0xbd7754ba, 0xacd2cd38, 0x893be48d, 0xd1a4aed5, 
0x4842178b, 0xebddad70, 0x8d8bcfb0, 0x4a06795b, 0xd2b3ed9d, 0xb2f85905, 0xe3ba7690, 0x0b16aa24, 
0xfa37b66e, 0x9bce1bd0, 0x9edf1a4c, 0xef96435b, 0xa3a130a8, 0x7c59fc5a, 0x34b11de7, 0x48a2e6ae, 
0xfadcdc8b, 0x6da5f55d, 0x0b3dee4c, 0x676c26bb, 0x7db0525e, 0x3825ff83, 0x821db7f2, 0x479f8489, 
0xbf6f5e1d, 0x13fd6109, 0x78116d2e, 0x9e26d309, 0xcb44ade5, 0x5eb85ac5, 0x1585cbf4, 0xac6c84d1, 
0x5f9382e9, 0xfb2c736f, 0xaa917534, 0x92c62d18, 0xd056d13d, 0xe8b528d3, 0xf6473a43, 0xb1dee3c1, 
0xf45cfd4c, 0xf9e92829, 0xf8fcee6f, 0x930040eb, 0xd539fe33, 0xb749e0af, 0xcdee9161, 0x4daffe9d, 
0x7a321a4c, 0x7817ecc8, 0xe997470c, 0xbd5676c2, 0x1aaad1ca, 0x68acc717, 0x9853139d, 0x3ce998f7, 
0x591bd113, 0x58993bf2, 0x40f42a91, 0x92efe50c, 0xcb493c3b, 0xe575e483, 0x4480d98a, 0x19f2799b, 
0xe50b4a1a, 0x6bc60ee3, 0xb7b19bf6, 0xf264a60e, 0x24861701, 0xe1d0200e, 0x054a7920, 0x865f8c86, 
0x12131260, 0x34220d44, 0xd371a250, 0x92320048, 0x84d225c8, 0xc92da8d3, 0x3040242d, 0x88ca2536, 
0xc081c463, 0x60004c45, 0x92c22898, 0xa48c090b, 0x12366112, 0x149029a8, 0x54402888, 0x45821402, 
0x37190830, 0x942410c8, 0x29846368, 0xb6143146, 0x930d3602, 0x51b2644d, 0x22db64c1, 0x0a420111, 
0x40861065, 0x10014cb6, 0x034880d9, 0x8da05a88, 0x35108a15, 0x112e329c, 0x6d831c64, 0xc0522107, 
0x03409012, 0x05460030, 0x17084c16, 0x59042458, 0x2a200a25, 0x08647212, 0xc80e3700, 0x21244292, 
0x491c2e22, 0xd9680482, 0x4c092360, 0x16cb65c2, 0x5164c8a1, 0x4080e268, 0xc24a28c3, 0x082418d4, 
0x4e32ca0e, 0x32db2d06, 0xe44022d2, 0x2a026050, 0x82980e40, 0xdc31c660, 0x4c931030, 0xc6634533, 
0x0c120800, 0x5212222e, 0x10144d18, 0x9a80c519, 0x2886418a, 0x490c90a8, 0x09720682, 0x2094d348, 
0x92c881a8, 0x62212218, 0x0c891010, 0x021924a6, 0xcb000018, 0x04c85041, 0x94c20044, 0x22261459, 
0x48c2da45, 0xc8900db0, 0xd1704288, 0x0d181b28, 0x464b2c21, 0x1331a811, 0x24009c65, 0x80c13144, 
0x4270b0e1, 0x49068b4d, 0x46092219, 0x006c4283, 0x46306231, 0x964489a6, 0x4171c262, 0x69b49372, 
0x048a3248, 0x126100d4, 0x6a332409, 0x05186246, 0x194d1442, 0x4020948a, 0x412400b8, 0x4281c09c, 
0x09a6cb61, 0x48590c80, 0xd02c1212, 0x68051c50, 0x90cb3148, 0x0200c882, 0x2a446449, 0x050a6e23, 
0x0c7008e4, 0x02348a28, 0x42c82d29, 0x0160a909, 0x6d249909, 0x20946904, 0xe4448009, 0x69984b4e, 
0x34c23240, 0x990c82c0, 0x21890825, 0x91038a20, 0x63490003, 0x2990d86c, 0x33147096, 0x226e48e3, 
0x72449b70, 0x230a2c38, 0x626908d1, 0x05481281, 0x10d34805, 0x2231008c, 0x86390c50, 0x02d950a1, 
0x1c860113, 0x51c2d105, 0xa29c0426, 0x980c42c0, 0x8444ca48, 0x14400542, 0x244a4302, 0x84065441, 
0x24214990, 0x0185084c, 0x0c26db48, 0x24d42486, 0x5b663058, 0x4216002d, 0xa2dc2825, 0x02621641, 
0x44a44069, 0x021b4c12, 0xc225a009, 0x8649002c, 0x10942c30, 0xcb30025a, 0x49145251, 0xa2017018, 
0x0304b813, 0x91a6112c, 0x82144519, 0x0921964c, 0x86270410, 0x904a2d92, 0xca2820c0, 0x24c21b49, 
0x305a6c84, 0x614d4281, 0x8142d310, 0xc2a02c05, 0x04849704, 0x71b91b28, 0xc4990126, 0x51800853, 
0x21969a21, 0x38e35022, 0x13621000, 0x4da01848, 0x34190240, 0x24411058, 0x8828a160, 0x02099012, 
0x832d329b, 0x0106848a, 0x38c405a8, 0x0c80a654, 0x09445881, 0x14cc6938, 0x4a1112a1, 0x65b0cc0d, 
0x346369b6, 0x128db2c0, 0x8c420324, 0xa2104234, 0x0924a25a, 0x0c160985, 0x991221c8, 0x122224d3, 
0x00b8218d, 0x864c6192, 0xc36d241b, 0x2d40d841, 0x30110e36, 0x0270390a, 0x10409270, 0x02a44cc9, 
0x0c70b243, 0x8e272221, 0x905a0923, 0x10498850, 0x71429960, 0xa05b5026, 0x1b9180da, 0x21071429, 
0x80d95128, 0xa4692241, 0x66368928, 0x40cb8543, 0x00492240, 0x71a31829, 0x46d06936, 0x0410869b, 
0x85b4e071, 0xa6546530, 0xc04086d3, 0x28a8194d, 0x10195098, 0x0311c662, 0x2d94092c, 0xa5010c40, 
0x0c66408c, 0x3044142d, 0xb0639104, 0xc4512904, 0x51b2a364, 0xa6521216, 0x8a6ca2c1, 0x40210329, 
0x340a3121, 0x0b29a8cc, 0x2008a444, 0x28d91238, 0x0a61b404, 0x21322084, 0x31082dc6, 0x44292462, 
0x22272462, 0x22e44614, 0x60250698, 0x46481c61, 0x40cc6902, 0x1985c010, 0x70b7134c, 0xb4218a16, 
0x9a2942d0, 0x4124db64, 0xb50c8510, 0x50448720, 0x24165410, 0x12492114, 0x8c88c063, 0x90069b44, 
0x20a28440, 0x1228240c, 0x00004249, 0xb5040124, 0x4b213841, 0x0014a08c, 0x20c30248, 0xa20548d0, 
0x24485028, 0x465004b9, 0x0b8d1004, 0x6929042a, 0x309b6226, 0xd070c080, 0x60a85808, 0x348490c9, 
0x0c01865a, 0x7238c166, 0x32e38cc6, 0xa1458292, 0x11c00404, 0x27114448, 0x48920658, 0x62225472, 
0x220041c2, 0x84841521, 0x2e328111, 0xc89c0e40, 0x9361310a, 0x08a68a20, 0x02520801, 0x1c4d2698, 
0x6944232c, 0x22924640, 0x80514894, 0x6c940368, 0xb0602198, 0xa4001018, 0x6a185164, 0x46cc8428, 
0xca00024b, 0x21960111, 0x811c6d94, 0x64248243, 0x6931008c, 0x34c15242, 0xda0c4120, 0x6d150804, 
0x00a34925, 0x13854819, 0x4e151c32, 0x06490e20, 0x520c2319, 0x51190900, 0x44ca3098, 0x48904484, 
0x4808c08c, 0x17084425, 0x24503318, 0x71302180, 0x301c6428, 0x9b800421, 0x1098cc22, 0x31140d00, 
0x5b71350c, 0x70c9218c, 0xa4930804, 0x6422309b, 0x70b8100d, 0x98913108, 0x1886320c, 0x4532634c, 
0x30e16882, 0xd98cc400, 0x30c50031, 0x882109b6, 0x4829b11a, 0x2d29232a, 0x16432008, 0x2028a904, 
0x44c0638c, 0x94847018, 0x1360a460, 0x2886d340, 0xc3048d46, 0x622ca51a, 0x51a89a68, 0x168a2190, 
0x444ca444, 0x6a320809, 0x200a6897, 0x18290681, 0x61284422, 0x301a4a24, 0x900d4423, 0x85c30252, 
0x18226599, 0x19311243, 0x2c350a91, 0xb4d34c12, 0x622930c1, 0x88c01300, 0xb50444a0, 0x89088019, 
0x9b61c530, 0xcedba664, 0xe0a0b742, 0x32110eee, 0x48557e6e, 0x0c2e288f, 0xab71c9d2, 0x2976adb3, 
0x06c59ab7, 0x27fe15b8, 0x2885f264, 0x4095ca5d, 0xde474c75, 0x07b8b929, 0xaa4b31d1, 0xdc8087c9, 
0x4931ea72, 0xb3ce25ad, 0xac06d594, 0xe87d3c9a, 0x72323f4d, 0x46d7dd02, 0xe81a2a42, 0xc1c29a3b, 
0x00ce86a7, 0x74e1784e, 0xaa39800f, 0x12638219, 0xe46a5cb3, 0x0bc395f0, 0xafb9a757, 0x42bb2469
};


const uint32_t mldsa_seed[] = {
0x9d29499b, 0xf0b43a43, 0xbb92ba18, 0xadcbdba8, 0xe8efe27e, 0x139e60fe, 0xcf8295d7, 0xbc9f3538
};

const uint32_t mldsa_sign_rnd[] = {  //deterministic signature
0x6742d2f8, 0x55d7decb, 0xa20a5e96, 0xf1ef77ed, 0x8d2e6575, 0x5b7cc393, 0xc6504726, 0x4b9c2fa1
};


const uint32_t mldsa_sign[] = {
0x00352f28, 0x211b170f, 0x09000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x000000ab, 
0x95502416, 0x0ed9c79a, 0x68635103, 0xf8dfdb9e, 0x8b862ade, 0xcdb09932, 0x2de8451a, 0x03daa199, 
0x80635f5b, 0x10d9d289, 0x56230eff, 0xe9ccc6c4, 0xa3720a05, 0xf777af68, 0xea8f65d3, 0x89d49854, 
0xd8827841, 0x7df59e05, 0x423973a9, 0x31fe8bb3, 0x45ea87e9, 0x018eecc4, 0x075eaa9c, 0x5f295449, 
0xc9c9a31d, 0xc4e42167, 0xf6ec3373, 0x4f5a0ff3, 0x15639251, 0xc9e1b852, 0x1ec2bfed, 0x515fe460, 
0x989eecbc, 0x27010b0d, 0x2af8391d, 0x5dab9d41, 0x2cfa504a, 0x20927f80, 0x11ca006b, 0x6ac1d945, 
0x1ddb602a, 0xcaaebe4a, 0x4188d101, 0xbf20c633, 0x70e4bd15, 0x3c7e38fb, 0xb712097a, 0x5ba111c8, 
0x9e98d935, 0x2348d1e1, 0x31c3d5d8, 0xe4885823, 0x765db3ea, 0xf505d2c3, 0xd9e441f6, 0x7c82b1fe, 
0x81a46cf4, 0x3eca7353, 0xe8c4b175, 0x685817bd, 0x569ab011, 0x56a9bf86, 0xb2546325, 0x0cffa8d7, 
0x34d25297, 0xd42fc5b7, 0x4a8b4c5e, 0x8a372c6a, 0x7c6bb1a6, 0x02c55d1b, 0x53a9ae7b, 0xa799ca9e, 
0xaa5a533f, 0xf7750639, 0x38c3e337, 0xb1d0a97b, 0x9a8a3dad, 0x6a31f821, 0x7cbae7bc, 0x2d83933c, 
0x94b276a4, 0x7e2a6dca, 0xd0130e06, 0xb5ce6e62, 0x89aedce6, 0x256a6907, 0x3e37177f, 0x23678420, 
0x23acd8e8, 0x013bdcbd, 0xab76b045, 0x759a839c, 0x54710852, 0xc5a958fa, 0xe82c6207, 0xa8d0138b, 
0x0458729a, 0xb6074c60, 0xc0e00c52, 0xe49c45a9, 0xffc8b64e, 0x668b709c, 0xa3ab6a42, 0xb5492827, 
0x65d7062b, 0x27abfe5a, 0x29dc9014, 0x81c9db0f, 0x0307ed25, 0x8563957c, 0xa8c06ec1, 0xe16b8306, 
0xe253b71f, 0xdc5e0699, 0x5c2470d5, 0x30eda829, 0x16d725ee, 0x1b72e08e, 0xe79230ea, 0x2c53c2c0, 
0x7c1bf0ac, 0x9c4c00a7, 0x6b443d98, 0x3a9a0b5c, 0x5985f02f, 0xea20ea09, 0x5a488a21, 0xbd824fb9, 
0xb219c4bc, 0x33444892, 0x2924a47c, 0x004c52b1, 0xd983eff6, 0x72497449, 0x937d0249, 0x2e975ece, 
0xcec20f3f, 0x8b569713, 0xcc4d0af9, 0x9e9845c2, 0x93f0af98, 0x0bedb7a4, 0xcb61a877, 0x0afae7ad, 
0x78b800f8, 0x07a6f86c, 0xfbed60a4, 0x3881200e, 0xde05f134, 0x2847998f, 0xacbb9579, 0xcc468a90, 
0xd0668d68, 0xab94cb1c, 0x23d46d72, 0xc5d85475, 0x12f1ad66, 0x7325f315, 0x0c91dfbb, 0xc96f541e, 
0x29e48326, 0x6733c932, 0xb7f59097, 0x9e56a867, 0xd445cf11, 0x94693aad, 0x13f0b8ac, 0xec0df170, 
0xb5d433f2, 0x97e95670, 0x5cdb3445, 0xfdeaf660, 0x0dbc74d2, 0xb1b6ca59, 0x4a07c454, 0x83a6db5d, 
0x6db8fca4, 0xda58e796, 0x3063347c, 0xa4692e4e, 0x62687882, 0x503a808d, 0x7f03218a, 0xf580f2aa, 
0x5ab560a1, 0x57a97238, 0xea5e18e5, 0xf9489419, 0xf42ee73b, 0x2e191424, 0x0440a2fa, 0xe2a5e0e4, 
0xab2f2be8, 0x7b1f8f9c, 0x6227e586, 0x2792ff3d, 0x5f249d70, 0x0de90611, 0x852f66ef, 0x395930ec, 
0xe44cb914, 0x59f132e8, 0xdb2025d9, 0xa09eb2f0, 0x03a8b4ba, 0x5fff23a8, 0xad05ee0a, 0x283e1dab, 
0x2f85cce1, 0xd1271476, 0xf278bb4b, 0xc98bf2da, 0x7e0e6c01, 0x15b7b631, 0x0c89c11d, 0x49ebdb00, 
0x89f44473, 0xe6ddbec9, 0xf61d1aa7, 0x8f4892d2, 0x662952d7, 0xeeb57b38, 0x18d90b50, 0x34cf1600, 
0x2867e347, 0xa335b432, 0xf76d1a51, 0xbda63353, 0xc0bcaa44, 0x54d26e5a, 0xea838528, 0x4e22d624, 
0x43873f09, 0x7574c644, 0x438cacfa, 0x04385313, 0x8618a7c8, 0xd0798e4b, 0x117df732, 0xfb1bdcd7, 
0x4a9007cd, 0x3dbdaf8f, 0x72795f58, 0x2f8f6367, 0x22dedab2, 0xbf59a98b, 0x622087c3, 0xb0a90232, 
0xec6085a2, 0x7f95b3ad, 0xfe540b0e, 0x6478b0c4, 0x9da6c4b7, 0x4d7733a5, 0xc39882d1, 0x10af47cd, 
0x0219fa0f, 0x0ee60d0c, 0x640bf8a4, 0xeafa04e5, 0xfd35a48f, 0x9e058bf3, 0xcff27a86, 0xbb28977f, 
0xaf8a2312, 0xfd6a5fca, 0x08c85da7, 0x47becb3e, 0x74dc5368, 0x9c0a1a9c, 0x8bc596d0, 0xe920b353, 
0x7b29bc75, 0xf296a58b, 0xf31c0d50, 0x06b61bf0, 0x387451e6, 0xc9b4fc7d, 0xe96bea8d, 0x222844f1, 
0x78020c1b, 0x1cfe0260, 0xf0d45959, 0xfada8256, 0xb2e048f8, 0x9f654ea2, 0x960590af, 0xfa42f6a4, 
0x0a72249a, 0x1df0b119, 0x4ddeafca, 0x7390982b, 0x5a1ab89d, 0x7f93c5aa, 0x6d9bedb6, 0x4466f780, 
0x9b35724c, 0xc6e723bc, 0xb4fd337b, 0x90ff60fb, 0x0c9ed071, 0x14f7a39e, 0x3448138c, 0x7dc7d153, 
0x4e19396b, 0xc798c050, 0x48698097, 0x60c9a245, 0x9bc159d7, 0xa565d1c5, 0x360cac97, 0xc014773b, 
0xf852ee05, 0x7e6024e8, 0x854875f1, 0xb662b0f8, 0x9c948b91, 0x74d7bb48, 0x804d3942, 0x64a00f6f, 
0x37040a65, 0x3aa25131, 0x439976d6, 0x297dc90f, 0x5e3ead9d, 0xdcd099e3, 0xcda169b3, 0xe61a34c8, 
0x68d0f1b6, 0x6fc1d312, 0xd6d72e42, 0x1476ce1c, 0x3530a984, 0x01013747, 0xde349d4a, 0xbcf08ac8, 
0xddc541b0, 0x645c6e04, 0x369f83f5, 0x30b12bf8, 0xf75f348b, 0xeb38cb01, 0x2c72b48d, 0xf88dd8b8, 
0xa2762a8a, 0xe6ee4d3d, 0xf7deb65b, 0xa6b568a4, 0x110b4e7f, 0x6a06f156, 0xe00e0dad, 0xc859ddf1, 
0x53145445, 0xccc8a7fe, 0x64bfd49d, 0x4a5e1a31, 0x6bbabed0, 0x3d3edee2, 0x6e4965f8, 0xba633c14, 
0x006c8e66, 0xf2672d86, 0x4f1d93c6, 0x7c388280, 0x07bea354, 0x1099dd85, 0xef4d42db, 0x9da4c6e0, 
0x9d5d69b2, 0x73a9cc24, 0x7d547702, 0xa75be3e6, 0xe39cb9e7, 0xdc1e2030, 0xabf9b55c, 0x06cab594, 
0x0cdfff64, 0x56444c4e, 0x11f992e5, 0xc7153e6f, 0xd90982e8, 0xe75e9f7b, 0xd7ae54ec, 0x2ce6860c, 
0x5f455805, 0x74a33408, 0x9559eee0, 0xbdb3fdab, 0xb9f374cb, 0x7b0e6aa5, 0x568ea1d8, 0xb6c480f4, 
0x37902e0d, 0x011c5a55, 0xffab928a, 0xd638f43c, 0x95ed78b0, 0xff527529, 0x9e06ea44, 0xd055b27e, 
0x0dc041f2, 0xda737d63, 0xe2cccc90, 0x7aad03ca, 0x01fadeb6, 0xd1e6b5f3, 0x48eeefee, 0x0a5edc3e, 
0x0fdb40a8, 0x6e6ed1a5, 0xbb0b48a9, 0x9734861f, 0xb998b39e, 0x0bcf5e20, 0x0755eee9, 0x5fd67ec8, 
0xc97efd15, 0x4d4dc023, 0x0a586f95, 0x5539971a, 0xb3b33a26, 0x79cbf2fd, 0xf2060e88, 0x8b2aed93, 
0xac6d141a, 0x2cd35bca, 0xe5e7ed3e, 0xb0e40f9c, 0xfa4b8568, 0x45ea9c2a, 0xdbc0fd2e, 0xc836f6c0, 
0x300101a5, 0x9974b891, 0xf8e7feea, 0x5a3fbf25, 0x6ccb7460, 0x5db5f0a5, 0x5a04f45d, 0x53f92746, 
0x020a52fe, 0xd2cd5605, 0x6833da70, 0x1cffe9e9, 0x1ecdc660, 0x23b7949e, 0x8b982afe, 0x10943dc4, 
0x4b7ee049, 0x0403a654, 0xdcbf5eaa, 0x243cf9c0, 0x0136a928, 0x56b02dea, 0x16ad1604, 0x4af8985d, 
0x00502fa7, 0x54880d1f, 0x507b9136, 0x357cefdd, 0xc3dea9e2, 0x02e1389d, 0xb96aac9b, 0xfb9a9e77, 
0x41e2a551, 0x20c9f7d0, 0xbecb7061, 0x0573cb35, 0x32e6cdf0, 0xf8272660, 0xe98710e2, 0x78a9ae00, 
0x72531054, 0xdadcf3a6, 0x6ea3a21c, 0xec289493, 0xeaeb3ea3, 0x8f5b1239, 0x9c881a70, 0x1fcdab68, 
0xa5db24e8, 0x2c7e91c5, 0x7964e298, 0xf6b51eab, 0x9c1371b9, 0x40c923c6, 0xf0ad7e38, 0x7905d2d0, 
0x7c741e95, 0x9028b877, 0x7c81b57e, 0x40aef11c, 0x612e2644, 0x5f66dc3e, 0x8be2c63a, 0xfa83a151, 
0x29b61ab0, 0xc2efa7ec, 0x84e2edb1, 0x040d5045, 0xa5a6d201, 0x008d7e30, 0x41280155, 0x760b7346, 
0x9108e878, 0x3234a33c, 0xe70988a5, 0xb4383080, 0xf2d400ee, 0x904b0073, 0x5b5b2700, 0x8a623235, 
0x410205bd, 0xedd498c3, 0x56eb3af4, 0x3fe92ac7, 0x5ccc6e1c, 0x2cc2529f, 0x34faf182, 0x23d9dbc4, 
0x17505bbd, 0xefe5717b, 0x39e38918, 0x8794cae2, 0xd0e430bc, 0x1e268e4a, 0xab2b5ff3, 0x04e6c03f, 
0xe5405fbb, 0x5dc8dd6a, 0xf009674c, 0x0dd286b8, 0x3001816c, 0x24add5e2, 0xdeff20c0, 0xf3aa32a4, 
0xa41bb525, 0xc3a49111, 0x68102bda, 0x66bdeadd, 0x0c3ab1e5, 0x6f907640, 0xfab11879, 0xebe0b134, 
0xa57fa976, 0x8a194551, 0x955451f1, 0x419307a7, 0xaaaab600, 0xeff4453e, 0xec2d4810, 0x164d7376, 
0xa31010c9, 0xf40e545c, 0x786443a4, 0xdba0b6ff, 0x96fd2362, 0x3560d8e2, 0xa1768e61, 0x5710b778, 
0x6519b4a5, 0x227ce79c, 0x1e1e5a15, 0x7b6abbf7, 0x735ba73b, 0x43e1d3a6, 0xbde340dd, 0xa2b9b080, 
0x3f33df40, 0xe3cec4cc, 0x522e410c, 0x6efa6371, 0x8474359c, 0xa0d10c13, 0xf16f04b6, 0x7ccfab32, 
0xcce6a804, 0xb031d677, 0x02d7b327, 0x23c5de15, 0x41701342, 0xaae75c37, 0xbfd7f740, 0x996f6b97, 
0x5a86adec, 0xc610b8e7, 0x32e54374, 0x82e9c6a2, 0x8b2af874, 0xd070d3ef, 0x068c21a2, 0xaaffd04e, 
0x60515042, 0x29f902b4, 0xe89f6278, 0x54c2a289, 0x19c801e5, 0xc68e2d76, 0x6e158587, 0x3ea59f5b, 
0x89867178, 0xb49e4167, 0xa91b6446, 0xc42adfaf, 0xc11c59a0, 0xffa16de6, 0xed47686f, 0x3c4a9028, 
0xc5313ffa, 0x729f573b, 0xabc2c58e, 0xe24c465e, 0xdf4a5f30, 0x05e8b314, 0xfe167699, 0x6b3d8682, 
0xa397efd6, 0x8cc71afd, 0x5e951c4d, 0x384bf5b8, 0x86f011cb, 0xec094dbd, 0x44e364cb, 0x1e14cdba, 
0x28bd5446, 0x26105653, 0x10bb6ea3, 0xa4098ef2, 0x010fe321, 0xfca0c3d9, 0x61992bb8, 0x63f3cea9, 
0x3cee4915, 0x561ae994, 0xc4caed13, 0xe8fe8154, 0xde540829, 0x08b77373, 0x786da232, 0x7f3a5111, 
0xed68e054, 0xbd2206dd, 0x156688d4, 0x945bc644, 0x5992cd06, 0x4a951a36, 0x00302fb4, 0xfc4af777, 
0xc45adbb6, 0x2f7cd75d, 0x0b2042b9, 0xc22838ea, 0x9f318dd9, 0x15241474, 0x84513770, 0x1a7ee462, 
0x9eab40b8, 0x3e69e7ef, 0x4d96efeb, 0xcd0b4729, 0x19c8db8b, 0x3e13c656, 0x7c18cc1b, 0xf1ab218d, 
0xfa91b265, 0xb3ffc865, 0xec9eeaf3, 0x5c9f6a46, 0x4f9cfe0c, 0x29eb9ea4, 0x45e3e673, 0x3ef6ac24, 
0x1a632738, 0xcbd9549c, 0x77837277, 0xba5ff8fe, 0x97867fb5, 0x39d6bb03, 0x867f552a, 0x29fc12a3, 
0xcc548c03, 0x27849a36, 0xe435107e, 0x5d54f206, 0x1b84f4f4, 0x5954de5d, 0x97da4404, 0xd7377a6f, 
0x8b956dd2, 0x6b557582, 0x16ec8ccb, 0xf9a2fe62, 0x1cf1ba84, 0x68222a14, 0x65f7e004, 0x9d16f611, 
0x03d8a689, 0x75d4ff22, 0x5ff4b6ce, 0x94c8ce68, 0xdfc686b1, 0xad6ae110, 0xfaca3511, 0xbf062591, 
0xfd6b461f, 0x6292f2a9, 0xd0305c59, 0x6be6b9b1, 0x1f99964f, 0xaa48578a, 0xa4e8f6f6, 0xf32776f6, 
0x2f8ad384, 0xece85cad, 0xf9616312, 0xc885a7fc, 0x0a77a48e, 0x66624270, 0x7100bdd8, 0xf12164d0, 
0xacc1eb78, 0x30c29348, 0xab618aa6, 0x241789a9, 0x64ba6cb9, 0x1452ac11, 0x7010644d, 0xeab7f39d, 
0x803ac076, 0x8ffe583f, 0x2d87f80a, 0xd032f0e3, 0x022132d2, 0xe1b42d72, 0xea47b57e, 0xdf898f85, 
0x30c8a6fa, 0xfadcbc4b, 0xa81ae40e, 0xfbd71eee, 0xaddf3a53, 0x7e2dfe40, 0x0b8a1422, 0x8a74eca6, 
0x10d571aa, 0xb1c21ea3, 0x1c111a1c, 0xee5dd22c, 0x2a77388f, 0xd60ee491, 0xd8df67e9, 0xc1921493, 
0x1d69f0ea, 0xeab4acaf, 0xd6ffb296, 0x262bf6ec, 0xde3e7c2e, 0x8874c10d, 0xd648caf8, 0x5e4d4123, 
0x9fde6edf, 0xc7e2991d, 0x0871711a, 0x952de5bb, 0xc7762e82, 0x964fb6ad, 0x9cef3a8a, 0xbe242e06, 
0x0075b4ba, 0x700b358f, 0xfbd5d9e2, 0xba5b37e4, 0x0c365ce1, 0xafc8db66, 0x46c8e22a, 0x4ab5e0f2, 
0x583ecbd0, 0xdb61c5eb, 0xe3cad470, 0xdd739a5d, 0x7dfde52f, 0x39ecd4b2, 0x979480ad, 0x3b31e715, 
0x8f3dcbdf, 0xeb9d5196, 0x3a6f5192, 0x70d4d02c, 0xd1eebde4, 0x24bae911, 0xaefccc9c, 0x3132d6da, 
0xa0ec9a21, 0x1559ccd3, 0xc4c59e19, 0x45e4c07b, 0xda2763ef, 0x498a794a, 0xb5c3b696, 0x5061bfa6, 
0x0443a83e, 0x6cbd2700, 0x2f01235c, 0x385b0def, 0x24ded055, 0xd77128b0, 0x7a8f4356, 0xb1c95143, 
0x188e6fc5, 0xffdb0fb4, 0x96bdf8db, 0x92b9f77f, 0x5086fb52, 0x67519810, 0x186edb88, 0x02a06842, 
0x326a99e5, 0x071ff7dc, 0xa3dc8df9, 0x183a3b91, 0x2300151e, 0xdaef8946, 0x71f3fb89, 0x0086f50a, 
0x315e4af1, 0x751ea67e, 0x377dde40, 0xe818123c, 0x12ea9c96, 0x8cf3ee82, 0x34b5f271, 0xcc7b1cb7, 
0xe9b8722e, 0xdbbf77a9, 0x486431ba, 0x85d01439, 0x6471f836, 0x43e25f17, 0xfb8f6fbd, 0x20eee19e, 
0x8f30c1e6, 0xb1d457c1, 0x8169fe10, 0x8ae46efc, 0xd8236194, 0xedce9579, 0x6a316e8a, 0x4fd56cac, 
0x6bd47b33, 0x7d1622e1, 0xea0fa241, 0xe0547586, 0x8eb01b95, 0xa305ac4a, 0x05fd2254, 0x673408c4, 
0x7d88282d, 0xc02981d3, 0xe8c96037, 0x93e6cedd, 0xb3cc7271, 0x4012e407, 0x8de8cd5f, 0x859a88c9, 
0x5ea5d5b8, 0xea8461ef, 0xb5b122c7, 0x61b101e9, 0xbb42574c, 0x0f30e69f, 0xadd8ea1f, 0x0ea5936d, 
0x53316809, 0xcdbb0049, 0x18275c67, 0xd9e5d785, 0x994d18f4, 0x20807238, 0xc7698812, 0x5110f95b, 
0x739dbfc9, 0x84e9c46c, 0x2297d5d8, 0x42983a7e, 0x753de10b, 0x55da0ad7, 0xba6d8ef3, 0xdfb8ca2f, 
0xe04660d8, 0x61784f65, 0x544bc8b1, 0xc622d8e0, 0xcfe6fe48, 0x6419a714, 0x5e0d0699, 0x91a620a2, 
0x32ad9bae, 0x847d6fd5, 0x93072268, 0x5cf5c2df, 0x6b44f506, 0x9a657f64, 0xb17bbe95, 0x759a08df, 
0x5d270ac3, 0x99029fee, 0x780ac2b0, 0x6a96504b, 0x527ead3a, 0x6f2ca30b, 0x76349913, 0xb94b5b71, 
0x0ac27493, 0xb94d8a2a, 0xbdf6f854, 0xb9149761, 0x9c3ae521, 0x368db01c, 0xd3150df5, 0xf8541b63, 
0xec69e0ff, 0x126b2803, 0x80b1040b, 0x80435023, 0x44596761, 0xc1f755b2, 0x00bdcc0a, 0x1cc8e279, 
0xb2660102, 0xe0361149, 0x062f6f5d, 0xa4b7aa6d, 0xcb59a0c6, 0xbf0c9d2c, 0x934d3838, 0x2acf48c1, 
0xae48f654, 0xedd090b9, 0x874eba17, 0xc56a588b, 0x7b8462eb, 0x94001084, 0x3e425c49, 0x3ef06b6c, 
0x55abe065, 0x40131866, 0x6a13f87b, 0x81cc8d05, 0x4b01fc8c, 0x216fb870, 0xae7683d7, 0x8e641683, 
0xa51c5e93, 0x4d899db6, 0xd4560c2f, 0xad5dc1a7, 0x69eaa428, 0x9b57abc4, 0x4b39c0a6, 0xa9798112, 
0xcc54508c, 0x14bfabdb, 0x23019f80, 0xee952454, 0xeed43b4e, 0x8df50842, 0x892fd3f3, 0xa7d7dec2, 
0x84184405, 0x61221466, 0x06e82d8a, 0xf37a27cf, 0xc500a5f7, 0x3d5659d3, 0x592a5024, 0x9de4504c, 
0x2f5029a2, 0xd894ce97, 0x0c07a2fa, 0x3402c7a4, 0x0ed820bc, 0x423a4df3, 0xe19df51e, 0xc4bb5064, 
0xb3cdd505, 0x6961afcd, 0x4908742d, 0x81200599, 0x6a7cfacb, 0xcde55aaf, 0xed9d6d2d, 0xe8f3d71c, 
0x5e6a9985, 0xdd259600, 0x9ae4d89d, 0x75b15923, 0x581a303e, 0xe447e7ff, 0x57ac118a, 0xbb9979a4, 
0xf7cca50d, 0x94d4c497, 0x979bd009, 0x80384871, 0xe10d61d1, 0x43024f55, 0xbd050890, 0xc9b38d3e, 
0x3052da7e, 0x64d1ec36, 0x40fa6d0d, 0x43c05007, 0x451786e9, 0x693f7692, 0x23aae909, 0x4e938189, 
0x0bf12cfd, 0xec8b57b6, 0x44c33252, 0x3d581c5e, 0x112e6f49, 0xb09dac5b, 0x0fd6b3ba, 0x332da547, 
0xdfc5e2d8, 0x44eb5b9a, 0xd85e4902, 0x37943c00, 0x081473c9, 0xb9c194cb, 0x87859126, 0x4cc986f6, 
0x265194b9, 0xca1ff9fa, 0x77f26628, 0x8b9790ec, 0x94d1672a, 0xb17db88c, 0xc62dad6c, 0xf119c70a, 
0xa8cbd9de, 0xf86cb669, 0x13c6bc1f, 0x51d31d9b, 0xb3ea8a9b, 0x6464c1b2, 0x97f43b45, 0x46f0b914, 
0x4966b0e0, 0x42152e73, 0x711d0d28, 0xd7394c2a, 0x2be6f057, 0xec55f6d4, 0x32bcdec5, 0xade6a0f3, 
0x67ddd0a2, 0x863af498, 0x8e1e79a9, 0x6b393230, 0x6e049b2c, 0x2f1c9918, 0xc2240a81, 0x2277df7d, 
0xa9b08fa8, 0x71ce4d4a, 0x6daab228, 0xa152d609, 0x647af9e6, 0x525dd179, 0xfa65bddc, 0xfc9e57e7, 
0x0c2b5dd4, 0x45f6d788, 0xe0c3ab23, 0xcf38bfa8, 0x58786cf9, 0x719d8b41, 0xc7c4f3b8, 0x3345d32a, 
0xd6427a29, 0x49002bd4, 0xf67f0c89, 0x4d5fea65, 0x7e15ee1d, 0x64b8e4bc, 0x00f31da6, 0xd2bf0b46, 
0x2c22bd7f, 0x732499b8, 0xf94372fb, 0x60ab4726, 0xef2e6f5f, 0x5cbdd728, 0xac3a6316, 0x9608b8b3, 
0x3ac1035c, 0xef13334f, 0x1b7bb20d, 0x0ccfdbf9, 0xd677eeda, 0xae29165e, 0x72b6c566, 0x08da7282, 
0x9385ac40, 0x149b25ff, 0x0ebfff53, 0xcf40b95e, 0xf3c20970, 0x620a9f95, 0x1ce9c973, 0xc37a6bab, 
0xcb8f8222, 0x01602d8e, 0x4b1da619, 0xcb5b9f55, 0xfb9f14e1, 0x822099ae, 0x56151bfc, 0xaedcda64, 
0x116a28ac, 0xfad67732, 0x8ce0d173, 0x223d676d, 0xcf370585, 0xc15c0627, 0xc9e82086, 0xedff13b2, 
0x4d683e91, 0x46ab250c, 0xb4a15e4d, 0x4ba09806, 0xc28282c7, 0xadae3095, 0xada19be1, 0x416ee0bd, 
0x1fe81157, 0x3940d0a0, 0xa1a6099e, 0x40a55060, 0x7cc7fb4b, 0x5df3bd40, 0x47c52a1c, 0x53ff7386, 
0xc795d7d2, 0x345df05c, 0xb8394b7d, 0xa8741b5d, 0xca610207
};

   
const uint32_t mldsa_entropy[] = {
0x3401CEFA,
0xE20A7376,
0x49073AC1,
0xA351E329,
0x26DB9ED0,
0xDB6B1CFF,
0xAB0493DA,
0xAFB93DDD,
0xD83EDEA2,
0x8A803D0D,
0x003B2633,
0xB9D0F1BF,
0x3401CEFA,
0xE20A7376,
0x49073AC1,
0xA351E329
};


void main() {
    printf("----------------------------\n");
    printf(" Running MLDSA SIGN RND Smoke Test !!\n");
    printf("----------------------------\n");

    //Call interrupt init
    init_interrupts();
    mldsa_io seed;
    uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], entropy[MLDSA87_ENTROPY_SIZE], privkey[MLDSA87_PRIVKEY_SIZE], msg[MLDSA87_MSG_SIZE], sign[MLDSA87_SIGN_SIZE];

    seed.kv_intf = FALSE;
    for (int i = 0; i < MLDSA87_SEED_SIZE; i++)
        seed.data[i] = mldsa_seed[i];

    for (int i = 0; i < MLDSA87_SIGN_RND_SIZE; i++)
        sign_rnd[i] = mldsa_sign_rnd[i];

    for (int i = 0; i < MLDSA87_ENTROPY_SIZE; i++)
        entropy[i] = mldsa_entropy[i];
    
    for (int i = 0; i < MLDSA87_MSG_SIZE; i++)
        msg[i] = mldsa_msg[i];
    
    for (int i = 0; i < MLDSA87_PRIVKEY_SIZE; i++)
        privkey[i] = mldsa_privkey[i];

    for (int i = 0; i < MLDSA87_SIGN_SIZE; i++)
        sign[i] = mldsa_sign[i];  


    mldsa_signing_flow(privkey, msg, sign_rnd, entropy, sign);
    mldsa_zeroize();
    cptra_intr_rcv.mldsa_notif = 0;
    

    printf("%c",0xff); //End the test
    
}



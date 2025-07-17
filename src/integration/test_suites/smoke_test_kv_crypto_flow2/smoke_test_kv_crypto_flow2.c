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
#include "ecc.h"
#include "hmac.h"
#include "sha512.h"
#include "sha256.h"
#include "doe.h"
#include "mldsa.h"
#include <stdlib.h>

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#ifdef MY_RANDOM_SEED
    unsigned time = (unsigned) MY_RANDOM_SEED;
#else
    unsigned time = 0;
#endif


volatile caliptra_intr_received_s cptra_intr_rcv = {0};

/* DOE test vector
    obf_key = e1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c
    uds_enc = 32cd8a75b5e515bd7b0fe37a6de144696aeedb1f5e03225a71fc690f5b004ff593794db7a99ced97c376385149c4ecafd3afd70cb657a6f6434bfd911983f4ff
    fe_enc  = 7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b
    IV_UDS  = F046BDE48AB68862484604A56024F793
    UDS     = 96cff59db2e5fb5800da7f598e032d465e1db55a3d52c5108e60b64608a2c857de5ca4924a13134a2d93b337a832609ec74b26e881c37f4be2eb38aa6abd1e83
    IV_FE   = 15CEB4E68F5D504D1D022FBA9EEEB655
    FE      = 7a874800c351a20d0fdd8eef818f30e95e6018e9837c56da1ff2bd99249d9e53
*/

    const uint32_t iv_data_uds[]  = {0xF046BDE4,0x8AB68862,0x484604A5,0x6024F793};
    const uint32_t iv_data_fe[]   = {0x15CEB4E6,0x8F5D504D,0x1D022FBA,0x9EEEB655};
    const uint32_t iv_data_hek[]  = {0x15CEB4E6,0x8F5D504D,0x1D022FBA,0x9EEEB655}; // FIXME unique value from FE?

/* CDI HMAC512 test vector
    KEY =   96cff59db2e5fb5800da7f598e032d465e1db55a3d52c5108e60b64608a2c857de5ca4924a13134a2d93b337a832609ec74b26e881c37f4be2eb38aa6abd1e83
    BLOCK = 7a874800c351a20d0fdd8eef818f30e95e6018e9837c56da1ff2bd99249d9e53800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000500
    TAG_forCDI = 4abaecefd122c4fd4ec4709c4999aab31850208e5fbaab24990003fcbc035f4fa6bbed8e46564ef467b675266c2e29b2cf2f634dd9d56c2de086baad355f024c
*/

/* DOMAIN SEPRATION HMAC512 test vector
    KEY =   4abaecefd122c4fd4ec4709c4999aab31850208e5fbaab24990003fcbc035f4fa6bbed8e46564ef467b675266c2e29b2cf2f634dd9d56c2de086baad355f024c
    BLOCK_forECC = 6964657669645F6563635F6B6579800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000470
    TAG_forECC = b1fc09a3bfacf391865abb5ac4361f236226a93f05916614f925209fdd53dc131e48b6464e524437d3eb89068cdfec7d1215a9f612340eab243c71498d30fbd1

    BLOCK_forMLDSA = 6964657669645F6D6C6473615F6B657980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000480
    TAG_forMLDSA = 0460a54d2fa8319a0d3d926a1ac8389242b0768fb015ddc35edfad5c20b277f2ae864ddd34295a1861c4a492aeaadbb52b2f6aae155368baa50cbe5d7e8ffc54
*/

    const uint32_t msg_tbs[]     = {0x5fcd5be8, 0xc6564caa, 0x85957069, 0x0096112a, 
                                    0x7bb850ea, 0x9573af1b, 0x3fe2a423, 0xff8b4645,
                                    0xfbe85d7f, 0xe05d3bf7, 0x6bbc42c3, 0x8d17c2c5, 
                                    0x690672f6, 0x6da2654f, 0x4c49b035, 0xa00823b0};

/* ECC test vector */
    //seed        = b1fc09a3bfacf391865abb5ac4361f236226a93f05916614f925209fdd53dc131e48b6464e524437d3eb89068cdfec7d
    //ecc_privkey = 855475e65f76bbe28a5380ab3f986cd52e01061377101e3ed437cad54423b02330ddd75805ea5b70a56fa7fd08e26dc2
    const uint32_t ecc_pubkey_x[] = {0x71a6574a,0xbc1dbf94,0xe61849f1,0x0f86e00a,0xb16e4581,0xe04e33f5,0x5a1a57f5,0xb463ab2e,0x873aa023,0x4c0d06f2,0xfa31b0ee,0xfe020a87};
    const uint32_t ecc_pubkey_y[] = {0xfa1e39d3,0x478a87c2,0xb45748cb,0xfead4246,0x9913a26c,0x177b8be3,0xf77e9bcf,0xe208538d,0xd783dcc2,0xb4337797,0x1375ec77,0xc9a6f2e7};
    const uint32_t ecc_nonce[]    = {0x336b9416,0x8b5c6665,0xdcf7cb72,0x2467606c,0x2262ed05,0xc4f47af5,0x85722e3a,0x1fe0f126,0x77db3beb,0x5510ecae,0x2c56cfa5,0x6fe6d349};
    const uint32_t ecc_sign_r[]   = {0x8d5f5a54,0x363c08c2,0x24bd7cbb,0xf542dce0,0xeacab7b4,0xaaf3c697,0xf754ad30,0xc9f41701,0xc629d4a3,0xf00ab860,0x8c640fde,0x6576164c};
    const uint32_t ecc_sign_s[]   = {0x8609425a,0x37504fde,0xbc216da4,0x89dd4da5,0xa9b28c3d,0x3f10f3ed,0x2d06eaeb,0x72cc891e,0xe325b40a,0x3c1f8601,0xf0f8ae98,0x46c34db0};

/* MLDSA test vector */
    //seed = 0460a54d2fa8319a0d3d926a1ac8389242b0768fb015ddc35edfad5c20b277f2
    //msg = 5fcd5be8c6564caa859570690096112a7bb850ea9573af1b3fe2a423ff8b4645fbe85d7fe05d3bf76bbc42c38d17c2c5690672f66da2654f4c49b035a00823b0
    const uint32_t mldsa_pubkey[] = {
            0xf1353964, 0x7623c20e, 0xfab1f2ce, 0x2165dbbf, 0xa3241104, 0x22aa1040, 0xda68961f, 0x507f26e2, 
            0x81eef19e, 0xbc48ef26, 0xb08436d0, 0xa8a9a491, 0x762a58ab, 0x188cc3e7, 0xa6b28524, 0x6bbc8215, 
            0xb7ac5c3b, 0x67737864, 0xd119a7d1, 0x3fc4f818, 0x3d8f145d, 0x6207b9cc, 0xbb3d085e, 0x85c1a818, 
            0x6db11d6c, 0x04df6f8b, 0x3cc7f913, 0xee2405df, 0x875b95a6, 0x75d22dd2, 0x4ddbf66d, 0x3a5a350d, 
            0x027f9b44, 0x5512cf0c, 0xe2956f57, 0x57d41a2b, 0x916873bc, 0x9c5b429d, 0xdb00d080, 0xd26ef421, 
            0xae3276f7, 0xe42402ea, 0x0d693d92, 0x3ccd34b2, 0x90abc756, 0x37e1c44d, 0x296c269d, 0xbb9c4574, 
            0x031e9cd9, 0xca4cf91b, 0xb4f5f6b0, 0x487e9816, 0xe9535c81, 0x5b7d2937, 0x2ada2f2b, 0x2f75b97b, 
            0x74adee56, 0x91d66c34, 0x86f70681, 0x70045cf1, 0xbeafa5f5, 0x0947fb13, 0x94a85f1c, 0x334a2ae8, 
            0xef14119e, 0xeefdc20a, 0x2e537b56, 0x909967fb, 0x0e9c2e9f, 0x967279ea, 0x23f3e671, 0xe187844e, 
            0xf1cb793c, 0x6157e879, 0x87196540, 0xdbcfe2a2, 0xe70e2892, 0x2bcf03d7, 0xdd87c7f8, 0x1b3bc8e0, 
            0x4165bf91, 0x55cb93d6, 0x9aa1bd5e, 0x61748ee1, 0x7dba772f, 0xdab90be0, 0x7e02a716, 0x1d72be27, 
            0xab331337, 0x4e271f85, 0xca7a6949, 0xd8bd73d9, 0x8341aae9, 0xed387fb5, 0xbd49365b, 0xb1a63338, 
            0x855dcbb3, 0x9895be7c, 0x2f3fc86e, 0x91e99bbd, 0x3ba43e90, 0xbcdfbbbe, 0x47cc6e8d, 0x74c16878, 
            0xa69070b8, 0x6aa67f85, 0xd199019d, 0x74112ed5, 0x80e497e6, 0x3a360088, 0xab865626, 0xf75cb140, 
            0xa8f2029b, 0x11099886, 0x650322e0, 0x75a2b076, 0x11523e4b, 0xb75b7090, 0x17f0bad5, 0x382eae4e, 
            0x4c9c2d67, 0xac5fb72a, 0x38da10a2, 0xe16313b3, 0x92048915, 0xd3e6ea3b, 0x0b967391, 0x4b7f4da3, 
            0x5b62efc0, 0x4bd22d01, 0x93b47017, 0x4c2063dc, 0x024134c4, 0xe9aca139, 0xac76224a, 0xe56ceb27, 
            0x3cc79234, 0xacfe25ab, 0xcc03d1b2, 0x92cf5807, 0x72d5c559, 0x437fc781, 0xade61a88, 0xdf8a8b9c, 
            0x2fe2300d, 0x34746004, 0x18c36819, 0x1c2cb11f, 0xe75bcf26, 0x23d23f1c, 0x68bb9e9e, 0x52792437, 
            0x913aa974, 0x7da5c2f1, 0xfeb0ecda, 0x54b837b2, 0x8b9f92c5, 0x1a4100c8, 0x0780c4c5, 0xf500678e, 
            0x513371b6, 0xd4954feb, 0xc16efc03, 0x50ff1bff, 0x9e133b47, 0x77ef82ad, 0x07aee797, 0x35b7c7a7, 
            0xa8191f8d, 0xf774cb55, 0x7c96bcc1, 0xc4bfe064, 0xc7d4d97c, 0x61695356, 0x3862b99a, 0x6a002e79, 
            0x9bd8dcab, 0x601febbb, 0x3a183e57, 0x21cb090d, 0x07d6664d, 0x156f7fc7, 0x57df2e07, 0x252dcfa4, 
            0x151bf71b, 0x4c51d4e5, 0xbfc4b5e1, 0xb88fa542, 0x2ff2af92, 0x0d093a6f, 0x008c6db7, 0x7d626882, 
            0x23d65c44, 0x0c8c8df4, 0x2855c943, 0xedf4c70c, 0xd1b3e64e, 0x20b112b0, 0xc144178b, 0xdd1a65e1, 
            0x1ce713e8, 0x71a15f88, 0x8523e000, 0xcc828845, 0xa5d3e46d, 0xc865e00a, 0x6cb4429f, 0x1cb8a5a8, 
            0x2f4dae32, 0x7fd3141e, 0x7b07b93d, 0x29cfe23c, 0x2fadae42, 0xc2a8d7fe, 0x7c235c33, 0x186a966d,
            0x18b89fc7, 0x532a4c50, 0x4b5b5e6b, 0xcb2e7cb7, 0xa5adc970, 0xb5527bcd, 0x7914ee06, 0xea6b4186,
            0x52a5db50, 0xbc9d001f, 0x3e29f441, 0xd33def5d, 0x1676b4b4, 0xbb89f764, 0x36dd5f73, 0x7e9e46ef,
            0x38eb835d, 0x27ce87f6, 0x1973b696, 0x585031a0, 0x773cfdd0, 0xdff822d9, 0xd8fbfc58, 0x3a97fc6c,
            0x0ccb567a, 0xeba74637, 0x73f41bb2, 0xbace9e03, 0x568c5858, 0xe08bbefb, 0x1ae20ed1, 0x5e32e1b1,
            0x5d71e260, 0x9f6988f0, 0x43008389, 0x4ff2f77f, 0x76e43d57, 0xa5d3d656, 0x3599123b, 0x2d483602,
            0x65dff0af, 0xdce48b9a, 0x15a5f330, 0x9de095ba, 0x96e6e060, 0x9c4c0aba, 0x7f281157, 0xc2a8864f,
            0xcfc24c62, 0x7ad9a65f, 0x63d21786, 0x107bd442, 0x8e4103f3, 0x95b71dc1, 0x4c56e4ff, 0xc248eff4,
            0x9f27793f, 0x05a7a211, 0x2af84632, 0x8d7d07c1, 0xafee25c2, 0x56698680, 0x743da397, 0x5f39c618,
            0xa506a313, 0x32079148, 0x86beb6a4, 0x000c24b4, 0x6222bbaf, 0x511c5167, 0xc86cee82, 0x170c300b,
            0x23bfdf46, 0x6b30e3c3, 0x0a20f88c, 0x694fbaff, 0x57b7b773, 0x50f5a496, 0xb1f9b11e, 0x1c06bb1e,
            0x90fc70bd, 0x0903a934, 0x30803c6c, 0x55dbf60f, 0x2b439cee, 0x90929575, 0x3b4201ae, 0xb81a98ac,
            0xb959d7f3, 0x415ae3f6, 0x7f67bb83, 0xb78a7431, 0x223be8c3, 0x3d24fa20, 0xb647d997, 0x27678c95,
            0x915b26a5, 0x3ef86071, 0xdf618a3d, 0xbc362274, 0x4674bab6, 0x48278208, 0x6e750f1c, 0x23fc4137,
            0xf1952866, 0x40dbb20c, 0x2b082037, 0x997d302f, 0x0abe7ec2, 0x972fde23, 0xd55380ee, 0x0b9993fb,
            0xa48c672e, 0xffe4929a, 0xbe0de201, 0x530b03d1, 0x6fb0f09b, 0xd629af53, 0x933b31b9, 0x40bbdeac,
            0x68b34f84, 0x635124d4, 0x46acba9c, 0xc9e6199d, 0x72977fb0, 0x47fec3d4, 0xea0ba9be, 0xa90a452b,
            0xc23fd93c, 0x18bf33bd, 0xe6e11702, 0xe8239749, 0x456308d0, 0xf150e156, 0xfafe39d8, 0x0b4f072a,
            0x4398863b, 0xd4aef65f, 0xa1c4ed80, 0xa20b99ff, 0x270e3619, 0xa19ea3de, 0xf4d2c163, 0x94145c08,
            0xa558f588, 0x966d85a8, 0xc2e0cb39, 0xad87d46d, 0x17618e8f, 0xa888aa9e, 0x0608d620, 0x1853839b,
            0xa68b3277, 0x854b249d, 0x8398738f, 0xf3a01a8f, 0xc976548f, 0x371b2ce4, 0xa9dcab91, 0x9764946b,
            0x8a3127db, 0xfb7c42dd, 0xceb18cd5, 0xe72e40dd, 0x137b6b24, 0xdd69e804, 0xb56e94c0, 0x9e895841,
            0xf629a151, 0x8bec8220, 0x58a89ed5, 0xcd71cf58, 0x8ff77b74, 0xf621f9ba, 0x4a5b0205, 0x9c3f49b4,
            0xae5cf66c, 0xfb745dcf, 0x79b243d5, 0xb95c1f42, 0x98d8c08e, 0xc0e3e553, 0x5136fd22, 0x10a20a5e,
            0x221126e5, 0xaab1b6df, 0x813ef0a0, 0xc7d246ec, 0x6e56a7b4, 0x8b4a2730, 0x29a98cae, 0xdd5d3d8c,
            0x48ae6961, 0x48d9fb01, 0xf81fa781, 0xc357e334, 0x514d741e, 0xbf153aef, 0xa8fb3cc1, 0x0b90c20c,
            0x952117c1, 0x3bc308d3, 0xa2d2f8e2, 0xa04e5f88, 0x4a66a0b4, 0x7de74d48, 0x844a2b89, 0xdd3b970c,
            0x7e6b091c, 0x35f6b105, 0x6ae43aee, 0x846d2c84, 0x6833fccb, 0xff552770, 0x2ace85a3, 0x6f7dd602,
            0xfb8a7b5c, 0x408752c0, 0x5c2166c8, 0x5e9bf147, 0x4118ccf6, 0xd3c9fdfa, 0xa6842669, 0x1ee8b2f4,
            0x791c2483, 0x678166a7, 0xda0e8dd7, 0xa6d0b0aa, 0x0c8d0ef8, 0x9b43874f, 0x509599c0, 0xdb256efc,
            0x60f15670, 0x86746ab5, 0x565397e3, 0x54bc4620, 0xbc342d80, 0x37b200bf, 0x15685371, 0x255ea3ed,
            0x237a0093, 0xf5fa1535, 0xc066ca58, 0x1a92f5c0, 0xc37f2b85, 0xd63adc14, 0xdfcc1758, 0xae631f89,
            0x468ff162, 0x83184423, 0x8af7d4fb, 0x92d85e5f, 0xba883da6, 0x07ec582f, 0x7a5bf86a, 0xe0b56b04,
            0x9238eb04, 0x8ce8ab06, 0x16690099, 0x6359895c, 0x69163bca, 0x8227ebaa, 0x9680b4ed, 0xd15998d9,
            0xc6feaca0, 0x35ec679a, 0xcd2ef8f0, 0x04b92f59, 0x1733c1c2, 0x3b7f040b, 0x98fcb7b6, 0x6fb77217,
            0xcd7dfd8d, 0xdbc0d02e, 0x4279aa40, 0x8c3e2c2a, 0x8d9761c1, 0x07219edc, 0xeccefc1a, 0x18db0c2a,
            0xa1685e2e, 0x54afb009, 0x11233403, 0x86d89477, 0x9edb27ad, 0x670740be, 0x1e264c60, 0x1e0ce4bb,
            0xd0cd7510, 0xa0905aca, 0x00ff8ee2, 0xe1c52a16, 0x6770aa9a, 0x967f3b6e, 0x3fa46edb, 0x7e47fbd0,
            0x9eb9c62f, 0x9cd34243, 0x537aa1ed, 0xbf66d08b, 0x1d30e1d0, 0xbd0fdd93, 0x9c7153a2, 0x0606eb42,
            0x6b1c9259, 0x38491c11, 0x92a3dacf, 0x4c5c6721, 0x62cef428, 0xf47b3904, 0x08392165, 0xa1b0df9b,
            0xf91d7e4e, 0x9b938834, 0x0c9a6b72, 0x03898571, 0x36b5538e, 0xd65b8338, 0x09e62455, 0x81362361,
            0x9443f5f2, 0xcc018cef, 0x1497b4c2, 0x8ea9930c, 0x1f6ed1d1, 0x0f2f0cf7, 0xf56176e7, 0xc7c1d778,
            0x8afc2373, 0x1f232f8d, 0x4943f982, 0xb157ac82, 0x27dbca0f, 0x36cf83d6, 0x93317e8c, 0xbe0aba45,
            0xa27dabc8, 0xf791395c, 0x2926f71c, 0xa3158ded, 0xe71cf8b5, 0x8d6aa9ea, 0xb2bad80c, 0x0981f98c,
            0xf5ac1a5c, 0x06ca1d47, 0x2986a678, 0x7f597038, 0xf6277b7e, 0xa7a126ca, 0x5801c8fe, 0x1ff1c251,
            0x08df614f, 0xd0542e7d, 0xd3c86b9b, 0x91d53f07, 0x17697ae8, 0x8c1582a8, 0x5c8bbb07, 0xc5a3f891,
            0x659d51da, 0x29ad06c8, 0x1376b805, 0x158472ab, 0x36da08cc, 0x79ef7e93, 0xa0cf9f9d, 0x689f86f9,
            0xb6668ea5, 0x8199abbc, 0x9e67d390, 0xd5ff887d, 0x13258feb, 0x2a5915c7, 0x651e6fdf, 0x3f629d0d,
            0x2d994bee, 0x5d9bd7cf, 0xa04c7881, 0xbfd88f23, 0xeeafb355, 0xd95d3301, 0x5dd68e26, 0xd4c32e6e,
            0x57f52ec9, 0xe1cae5fb, 0x0cb1d881, 0x9972b34e, 0xd89e18e2, 0x31e50b79, 0xfdba1096, 0x02814dfe,
            0x262e4703, 0x77ae4893, 0xb9b8981f, 0x4d89e25c, 0x6e2b9a96, 0xb3d925c5, 0xe9cca3d0, 0x336fdeda,
            0x83d87b93, 0x9f2650e9, 0xdf295aa1, 0xcd3099d9, 0xfc9b42b4, 0x32903122, 0x67a9b59c, 0x82632d73,
            0x052fefb2, 0xb9910a27, 0x64ae7ba7, 0xa5230774, 0x93d5dc25, 0x05d55cc3, 0xe17205bb, 0x496bc78d,
            0x8cb6ae12, 0xbedfc9fd, 0xb802a909, 0x34adc8ec, 0x7375edb2, 0x8b75e9e6, 0x52468adb, 0xf11f87c6,
            0xc3a02160, 0x1e4b0dbe, 0x9b79857e, 0x851aa878, 0x2e75cc9c, 0xbd6dcbfd, 0x6c71a201, 0x79d36d49
            };

    const uint32_t mldsa_sign[] = {  //additional 00
            0x003a342a, 0x241f130e, 0x09000000, 0x00000000, 0x00000000, 0x00000000, 0x0000ffd1, 0xb99d7336, 
            0xe2c99492, 0x78716452, 0x3519f783, 0x74591e06, 0xe277532a, 0x1af8f3e4, 0xbebcbab4, 0xa5826e3f, 
            0x01f3e394, 0x5236dcbb, 0x4d432ec1, 0xc0989493, 0x8f67554e, 0x10c9256f, 0x2c40860a, 0xed244098, 
            0x077cb147, 0x5e84b4df, 0xba0fc063, 0x4afb7597, 0x84b93568, 0x386f1941, 0x93220d19, 0x74e782da, 
            0x0462466d, 0xcd1851a6, 0x9ac941f9, 0x155b77ad, 0xfd642168, 0x4c786b3e, 0x2c068385, 0x288376b4, 
            0xec67cf70, 0x5a8ac91a, 0x0e496ad6, 0xb8c0b25c, 0xe58cd6c7, 0x47c6c303, 0x33dc5a72, 0x5a358263, 
            0x6b12b35b, 0x321a6cd2, 0x132c57a5, 0x286e0289, 0xa8927591, 0x8ebbda8a, 0x74449cc4, 0xa0ee9d8f, 
            0x66e2307b, 0x7dad17b0, 0x6faad6b5, 0x3bde8e87, 0xb9716c4f, 0xc20bb8cf, 0x3802065f, 0x367c14f3, 
            0x10bd7ac3, 0xb8dff5d0, 0xa0b8bd72, 0x3e4d0486, 0xd1f0ca95, 0x3206da5d, 0xec4660aa, 0x19236d0f, 
            0xf3eba6d5, 0x5c6a5cf4, 0xf654b297, 0x6d3e01b2, 0x99a90c69, 0xcce905a8, 0xec5f12a0, 0x37fe6d87, 
            0xd3bc447d, 0x63846b6d, 0x2b0a39f6, 0xabf1844b, 0xc16bfa69, 0x8ca59d93, 0x9102a60c, 0xd3f0755b, 
            0x6c21df17, 0xac0ec010, 0x32da16e2, 0xcfae965c, 0xbe8209d2, 0x4d7eeb66, 0xe22802c4, 0xaa68bd05, 
            0x3bd2681a, 0x98745c05, 0x30be642a, 0x692ee981, 0xf84a525c, 0xe8d7ee79, 0x782a5aea, 0x93afb476, 
            0x29118e1d, 0xc7d245c5, 0xc5afd8cd, 0xa5da3565, 0x94437269, 0x9d3c3cbe, 0xcb3ccdb8, 0x8c13be84, 
            0x76c452dc, 0xb423a9b2, 0x5a606910, 0x18e08f03, 0x42928e43, 0x1f910914, 0x70f2ac36, 0x8827d54d, 
            0x11bce3c3, 0x05d3477a, 0xa2dce312, 0x10e814f3, 0x1e7a5014, 0xc4bca052, 0xd4a36082, 0x4a6c2787, 
            0x010c925b, 0x24d0a27f, 0x13d2ce71, 0xcb5786ac, 0x52233feb, 0xf24e347a, 0x560d0454, 0xb7ef0a9f, 
            0x8c3fbd3a, 0x0a67557a, 0x00aedc39, 0xbb8b5a66, 0x6a9d46ba, 0xe09f45dc, 0x81ec7af5, 0xfeab215d, 
            0x37731c16, 0x4f3de920, 0xda7bfd97, 0x68333b38, 0x32be83db, 0x37d3b4ba, 0x7c5d7c3f, 0xb27e88bb,
            0xbea6d1a9, 0x303aabcf, 0x028ff18c, 0x77d8b32c, 0xbc1a5507, 0x69a97b48, 0x70316d6b, 0xc9b3c66e,
            0x4609c3eb, 0xb484e4cd, 0x11b7675c, 0x6ae20634, 0xd4978e5f, 0x2380779a, 0x5259de9d, 0xd75008b2,
            0xa7366844, 0x3fc03ec9, 0x99ea2589, 0xb6c00f6d, 0xf21c134a, 0x13b1f748, 0xd8d0eec4, 0x822f1de3,
            0x741b2679, 0xd4aed64c, 0x021534ef, 0x685dfa86, 0x3c656a91, 0x2c2e2d4c, 0x779d1477, 0x26472554,
            0xf8e914d4, 0xcc16e2c1, 0x474de73a, 0xf4948d99, 0x0ba4191a, 0xaad90729, 0xcbf24d0c, 0x0a9ddc43,
            0x9a1bf75f, 0x9df9d55c, 0x5fd535c4, 0xe89136af, 0x03ed9eb3, 0xcf1f7002, 0x6b575e49, 0x98e876c3,
            0x4954eaa7, 0x4f50228b, 0x48536cce, 0xba37554f, 0x61536762, 0x535664a4, 0x2023fa1c, 0xeccff0a2,
            0x0ae9f13a, 0x0d7bc596, 0xd94648a3, 0x42c65be9, 0xe6f6ade9, 0xb40a3a74, 0x52b60f64, 0x4ed4f8f5,
            0x74fb4a5f, 0xf7206d5f, 0x1c2547d0, 0x7c1a39f0, 0xf4386b3b, 0xd37f3da6, 0x698e0d40, 0x97731589,
            0x7edcd0e9, 0xdffdf434, 0x2d88d3ac, 0xdb22ec60, 0x6e2aebbf, 0xf3d61f9a, 0x648c1c28, 0x7563748b,
            0x6d2e2c40, 0x35a6543e, 0x387b982e, 0xe7c2fe21, 0x010b21ae, 0xb7b85bab, 0xdbb8d46e, 0x356e5b55,
            0x2864b4c1, 0xae2ff8dc, 0xa04df9fd, 0xb95876b4, 0x9e126076, 0x95a159a7, 0xba1150e3, 0x51d577cc,
            0x3c95e4c4, 0x4db682fe, 0xc2fcdd72, 0xcf194295, 0x0e684e50, 0x5c39b351, 0xedf2ebfb, 0xc7ea3ad8,
            0xfc49bf37, 0x60ca3613, 0x3eef3d8e, 0x1642fde9, 0xfae712e0, 0x5a82a5c1, 0x014ab6df, 0xdb71db33,
            0x376506cb, 0x79133792, 0x75a74d1b, 0x7c2a285e, 0xd7713ae1, 0x6f76258e, 0xb33be87c, 0xc1f2b1c8,
            0xea277b1f, 0xef10344b, 0xa6e69f61, 0x06b5296a, 0x425f9603, 0x5addbe90, 0x6f9c9690, 0x21a81e40,
            0x1e0d6a60, 0x39911f41, 0xc6b330a3, 0x9bb0036a, 0x98e9061e, 0xe02245c4, 0x5fabfadb, 0x0599755e,
            0x5e111693, 0x1d5df9db, 0x45c2b1e2, 0x9c40bf76, 0x6c289ffa, 0xcd3f7554, 0x76d3e278, 0x702bd882,
            0xe77c3b56, 0x786992a4, 0x3b288655, 0xd3e95e70, 0x6ca16569, 0x6a5587a9, 0xb86fb553, 0x7299a5dc,
            0x8ea58aa6, 0x2aa9f369, 0xa261eba5, 0x6bd56a57, 0x3d043882, 0x7b939b32, 0x858d5130, 0x73ff0ad8,
            0xd040e10e, 0x1cbde3ef, 0xac141bdb, 0xccfe9be6, 0x59650486, 0xee192013, 0x285b0da8, 0xe3874344,
            0xcb2fe473, 0x256eb315, 0xfd2a7023, 0xf382182e, 0x76123677, 0x0f95f46f, 0x8c9079de, 0xcb45696f,
            0x9cc6af36, 0x62eabec6, 0xe50e18bc, 0xe0a04f08, 0x4f96c384, 0x195400d7, 0x2eccf383, 0x88289aa5,
            0x0d23460f, 0x20ea674b, 0x6213f5c3, 0xa6c500d0, 0xae92051d, 0x297a6db8, 0x69aec356, 0x3af5431c,
            0x1b33c319, 0xa632df87, 0x29cacdf2, 0x16dacd18, 0x0a875d41, 0xaec3dcc6, 0x253cd470, 0x8531f0b0,
            0xcb9af000, 0x0ca4f20f, 0x27ecbc4f, 0x68c6e071, 0x02c3cbc2, 0xcd854a1b, 0xb944eaa6, 0x3dc0ea4b,
            0x0e171837, 0x1600adfc, 0x51e2b0f6, 0x7d186349, 0x0f8c151b, 0x4977190a, 0xe45135f5, 0xcfe74496,
            0xc5fb70b3, 0x163efc44, 0x67152316, 0x88f433d1, 0xb6edcd24, 0x3fb0e990, 0x4fec9d16, 0xcd23c0b8,
            0x6e7751e5, 0x3a152ea9, 0xfe949cd1, 0x2f9d3e04, 0xc9fdf818, 0xa968f7d8, 0x422ab064, 0x8413303b,
            0xb4ed8652, 0x46cf3517, 0x590aff9d, 0x52d3ce24, 0x37b7628b, 0x23015fa9, 0xe93acabc, 0x981c357c,
            0x96f7363e, 0x18266704, 0x733741ef, 0x07123276, 0xabc711fc, 0xcbdbbdc9, 0x4f3947c9, 0x45275154,
            0xb284c25f, 0x7083ce1c, 0xf277b457, 0x36807cdf, 0x65ab9eea, 0xdaaf18de, 0xb163598d, 0x2d4e51d6,
            0xede2236a, 0x02c589f4, 0xec2d8d90, 0xf7a8f0b5, 0xd7719476, 0x8698610a, 0x3b9fe340, 0x5d3850a5,
            0xa7f8b25f, 0xad2d36bb, 0x4b768c5a, 0x492b5053, 0x94e70100, 0x55cab9ae, 0xf57bd6ce, 0x86464464,
            0x3fd3b140, 0x37ac2fb8, 0x2ceb8f12, 0x2799be1d, 0xfbbb99b2, 0x5a58665d, 0x8295b3fe, 0xef1998dd,
            0x3a9dc2dc, 0x5fa0c65e, 0x7b09b1f8, 0xc8c2bf47, 0x9a2e4cb4, 0xa9d66107, 0x26ee2fa7, 0xdbfdf5de,
            0x5002c7ac, 0xc0b2f3bb, 0x731bd90c, 0x3b945426, 0x242452db, 0x038c5118, 0xd1113c5b, 0x47d79326,
            0x92acaf60, 0xc291283b, 0xe0f86ba7, 0x0b6d2e7e, 0x5f7025e4, 0x05b274ef, 0x6c8bab00, 0x284adfc9,
            0x23718476, 0x65c31bb0, 0x0eb512c7, 0x2b48d643, 0x7fe69436, 0x19cdb098, 0x00090aa0, 0xd27423d8,
            0x40c0c39e, 0xa8131402, 0x0ade5974, 0xeef75769, 0xd18fd47b, 0x26a08bb9, 0xfb457d81, 0x981bf517,
            0xb2bf5352, 0xde3c5550, 0x6ef57c6a, 0x9ebf97c5, 0xef0774f9, 0xddd57619, 0x9c297d93, 0xaf2efd74,
            0xfef47b54, 0xf08a44bc, 0xe18de89e, 0xa6eeebe2, 0x288e2eda, 0x24050150, 0xbfbcabd4, 0xb8010ada,
            0xaff6ef89, 0x5b66bf45, 0x34823613, 0x7a94a532, 0x82a52deb, 0x3ef0faaa, 0x7fba2e67, 0x250063f3,
            0xe7fd57ef, 0xb329cb82, 0x55519178, 0x92f2e80e, 0xbcaaee9b, 0xb23d252f, 0x2ad750ff, 0xa2a6765b,
            0x283a0988, 0x23e56d08, 0x3fab4f11, 0x30134c69, 0x709d7785, 0x6b9f5ac7, 0x08fa39a3, 0x5e2d0d84,
            0x0c922663, 0xf4a134f9, 0xeb201dbc, 0xc2c85afe, 0xab94abd3, 0x60dd657e, 0x1f8e481a, 0xae166271,
            0x29e3ddf8, 0x005cfc67, 0x9001a31e, 0x5a386ad5, 0x40a3fe36, 0x1cee07b5, 0x53e3e482, 0xad50375c,
            0x08f21780, 0xb5406eb3, 0x0bf87506, 0xedbf3001, 0x00033e87, 0x7848e117, 0xf10eae3b, 0x36e81944,
            0xf44bba35, 0xbf684bb0, 0xbeff8695, 0x7a46968e, 0xf74793da, 0xe001105d, 0xfa6f2861, 0x3dca7e8f,
            0xdd8c3d0e, 0x603e502a, 0x28f587cd, 0xc1d9c52c, 0xd7aea6d0, 0x2d8fd147, 0x06f047ed, 0x6ea58030,
            0x89977b8d, 0xf57f25fe, 0x2920fc72, 0x71c31fd6, 0x071c4e28, 0xd8ffc94e, 0xc43b04a2, 0xb56ca010,
            0x0c8907b6, 0xbe627b0f, 0x0fb50430, 0x8698ad64, 0xdef26af6, 0xe37efcf7, 0x8f4ca2d7, 0x0b627d0c,
            0xdf92f0e9, 0x0a6de706, 0xac5d36ee, 0x8656b837, 0xa4af7eb7, 0x1a9c3a06, 0x5325b8d6, 0x60c1c3a3,
            0x63c413b3, 0x8277bad6, 0x8f751a04, 0xeb61c732, 0xc6c13c2a, 0x99eeb584, 0xdd208a24, 0xb494fd80,
            0x57863ef6, 0xb660c149, 0x1bc0dec0, 0xbc8390ad, 0xa0acf495, 0xcf465d92, 0x2581b0af, 0x102d9e0c,
            0xf7b7c200, 0xdc594540, 0x7b6d122d, 0x236fedb8, 0x78456407, 0x90da5752, 0xff2643d0, 0x33c9edba,
            0x756493dd, 0xd36f8bca, 0x937ad63f, 0x54eecc0c, 0xccc6d08c, 0x8a6c6a8f, 0xa0668988, 0xd042d9d5,
            0xb1146b77, 0xc5e5023c, 0x4454e81c, 0x88705b8c, 0xb8bb1720, 0x1b2e76d7, 0x60d5aeb2, 0x088c86c3,
            0x80d1053e, 0xe9fc2ace, 0x4b924488, 0x7e5cd6ae, 0x674ee677, 0x48580853, 0xba701540, 0xe94a6a91,
            0xf2b5ff74, 0x0882cb9e, 0x6e1c2dc2, 0xb1329028, 0x66f8a525, 0xcbb0c69b, 0xe1e9395d, 0xb9d369eb,
            0x1463fbe7, 0x364dc119, 0x52bc61f3, 0x2c5a5efe, 0xa57edeb7, 0x72cfe84a, 0x4676abaf, 0xee2ef86d,
            0xacf03844, 0x0b72ad70, 0xfe5acb7b, 0x47773620, 0xf1658119, 0xc875ae66, 0x61c9686a, 0xc2b287d8,
            0xafdf2c4c, 0xba9a7638, 0x69f9699d, 0x1c41d1e5, 0x101c31ec, 0x3d83240a, 0xd3e98a79, 0x5d7c3eaf,
            0x2ece3e9a, 0x99cd4190, 0xfbc8d14e, 0x4bd4a083, 0xa25cb856, 0x31ef898b, 0x36c5feea, 0x1aa21fb9,
            0xf621f835, 0xe9f83a66, 0x00b20cd3, 0x0c8b700e, 0x14c644bd, 0xd28cebfc, 0x47e3585f, 0x686a3ba0,
            0xaa8e18ee, 0x0e211be5, 0x3ce3be1e, 0xa826af5d, 0x754e9b0a, 0xc1709c43, 0x86af73ba, 0x6a46c35d,
            0x8be782c7, 0x8fb9ebfb, 0xc63c939c, 0x1ba48718, 0x82d1f6f8, 0xb91b6b57, 0xdb2b63a6, 0xeb03c641,
            0x8e5f3053, 0xc2ed1379, 0x411792d1, 0xbf7e8a35, 0x515d3d46, 0xc5efe9b1, 0x7627b686, 0xa0f572a0,
            0xc1474812, 0x8f5af1ea, 0x4f72ec02, 0x77909bd6, 0x77ca4bbd, 0x07b9366a, 0x63e962da, 0x3b48b725,
            0x8f78304d, 0xdac73b9a, 0xe04935b9, 0xb550b5e5, 0x2492c94f, 0xe3b8a467, 0x556fcddb, 0xed9b1198,
            0x9cf77f63, 0x6b798dba, 0x51203266, 0xe5a97756, 0x074224bd, 0xd1fb3108, 0x730b566d, 0xcfaeb8c2,
            0x1ca0f112, 0x19fcc861, 0xbc8c1d13, 0xa7019301, 0x86856f7c, 0x952592f5, 0x4bc18516, 0x7bf38802,
            0xb6073763, 0x24e6f3ba, 0x2a9c3408, 0x48745f39, 0x5e45b4a1, 0x6d05b9f8, 0x7545d897, 0xcab09393,
            0x166cfc13, 0xb58053aa, 0x36f6cae7, 0x41687df5, 0x331cb4b5, 0x0717e272, 0x184fafe8, 0xd1622304,
            0x7ae50bc4, 0xf57d866f, 0x0b671b71, 0xfbceb50c, 0xbe8b69a5, 0x6cfa5876, 0x10a8375e, 0x5162f40d,
            0x6814b8dc, 0xd5d6ba69, 0xe5c792cb, 0x115d8b24, 0x8193b21c, 0xa579bda8, 0xa3d16a88, 0x0f33c161,
            0xe604725d, 0xcacc8fe8, 0xb5239943, 0x749354b0, 0xed25ad07, 0xbd73c5bd, 0xb008d0b1, 0x1623f559,
            0x7f262450, 0x8326a13f, 0xfbf684ed, 0xa5f4e5af, 0x60f56f77, 0x6b715e8d, 0xc5df35d9, 0x46d2c7d1,
            0x1c748fef, 0x3ef09d17, 0xb0e0d6b9, 0x63108f73, 0x20e055fa, 0x959a5475, 0x9a077704, 0xbe4795d5,
            0x813f7e0e, 0x49c70585, 0x8f9931fd, 0x307ccc81, 0x318f53a0, 0xbaa03027, 0x1c163451, 0xf7b4d061,
            0x0eccbe47, 0xcf736d1f, 0xa0a1ee56, 0xc006e915, 0xfccc80dc, 0x5c83d5e4, 0x2de1db6f, 0x1192adb6,
            0x847b0c9e, 0x7da4f9a3, 0x1e93d841, 0x64bcb891, 0xf95b3f6a, 0xcb538418, 0x65d339b9, 0x407fb1b7,
            0x5fd99572, 0x2441a1aa, 0x0592d327, 0x56b65135, 0x529e13be, 0xd5ff3cef, 0x249487a7, 0xe0be4800,
            0x94721eab, 0xb2fc177e, 0xf0a94ab3, 0x3dbdc819, 0xd4ba6da0, 0xd77acdc4, 0xa24faf2f, 0xe9f220c7,
            0x762c6383, 0xdb5b59bc, 0x8301dffb, 0x6ba12ce1, 0x1d809aad, 0x79f341f1, 0x6acd6586, 0x4b437d8c,
            0xbcefb6a9, 0x6913efb7, 0x4826bb69, 0x6fd45e5a, 0xe4e0a776, 0x12aa3074, 0xdcac3da8, 0x76aa8798,
            0xff8a032f, 0x1c796004, 0x4db0a80f, 0x2a3c256a, 0xa903e58a, 0xfde02b08, 0x72e7b328, 0x6f6c2122,
            0xea9ca829, 0x0d88f2b6, 0x0362cece, 0x8587018e, 0xd3edf5f7, 0x1fa9cf51, 0xdb477a86, 0x5bf484c1,
            0xd4176330, 0x3cd014da, 0x1fb52624, 0xd969aec1, 0x195eeb63, 0x5306b9b2, 0x84c93dc6, 0x94e1a2aa,
            0x7bcebbdd, 0x87b3048f, 0x8d391431, 0x0e797ec1, 0x5dfcf64c, 0xe7e11c13, 0xb31476e9, 0x8ddbe52e,
            0x443f04bb, 0xec8901ae, 0x28b53d48, 0xc329938f, 0x8bb87ccb, 0xc696f98a, 0x4f08b5b5, 0xadc803b4,
            0x6d463f39, 0x9c329612, 0xa8361f12, 0x53ce0b76, 0x1ceb9dfa, 0x037a25c4, 0xa5fb4ac5, 0x7705e2dd,
            0xf49c352e, 0x36d42271, 0xc968d3a0, 0xdd376940, 0xa65ea453, 0x1c0e22ef, 0x33bf54e0, 0x97d93d18,
            0xb7761b42, 0x4a5ad015, 0x508fc858, 0x21e332c6, 0xcc3a957f, 0x1982fc91, 0x14a474c5, 0x4e883f0b,
            0x15d44f95, 0xff506b70, 0xe4b939d6, 0x36fe3c7c, 0x0ddc311b, 0x358220c3, 0xf42429fa, 0x6a4d83d4,
            0x869ea203, 0xb319e844, 0xa409da51, 0x2e0231d3, 0x8ea284c8, 0x2f6b3ac7, 0x289ae4c3, 0xea1b1326,
            0x08327f24, 0x8b24457a, 0x493baf0d, 0xecfc4d8d, 0xab7cfebb, 0x6aee1bc1, 0xd12e003d, 0x2f806ee2,
            0x06fbf460, 0xbc83999f, 0xc9d3cc5f, 0x524a9250, 0x1d33bf66, 0x2e3b3d70, 0x6018addc, 0x4f90ef19,
            0x1a4209ea, 0xcc3ae5f4, 0xe1c7a59e, 0xc5446393, 0xe548eb1e, 0xda04c606, 0x407a99a1, 0x64e5e394,
            0x0a23cda3, 0x4f8aed8c, 0xe7aed750, 0x4a76dabc, 0x2f9c6b45, 0xa1d0e4ab, 0x560665d2, 0x26ab11f0,
            0x02d106b3, 0xaa031435, 0x047f27da, 0xd4bc562b, 0x17e86b80, 0x0e5346e6, 0x4644bf3c, 0xf345f874,
            0x4a0a4cf1, 0x3d116b28, 0x911d768e, 0x9c3f1fcf, 0x2961bcf5, 0x0ead694f, 0xeee0109c, 0x82c74810,
            0xa81502be, 0x509b2bea, 0xd9f71e03, 0x36ae31b0, 0x1fc78dca, 0x47695f52, 0x09dcab4e, 0x80770676,
            0xd509386e, 0x8f900a09, 0x8912f382, 0xfaddc1bd, 0x047a9284, 0x1760bfbf, 0x6a2ecd99, 0xa49fcf88,
            0x30c72be4, 0x4e74198f, 0x3c93e7e1, 0xdbaf478e, 0x94ca88eb, 0x4ffa9842, 0x65a8a94e, 0x3bfe1093,
            0x28cf2832, 0x61b13297, 0x2c7e064e, 0xfe69230b, 0x5fa234eb, 0x1057f896, 0xc53a5fed, 0x0ed43265,
            0x9982594a, 0x614cc401, 0x3ade7d81, 0xab19e62a, 0xb72d4034, 0x447558d3, 0x5ee4d788, 0xf0d65c2f,
            0x3587e8de, 0xf00652ac, 0x8563e6d5, 0x86313dec, 0x6bee0dcd, 0xffb2078a, 0x1d75efca, 0xa85885c7,
            0x59ab4104, 0x5c289495, 0xa55ac7e1, 0x81a29522, 0x72ab3bd8, 0xc78bce58, 0x1aea7b12, 0xaa63721a,
            0x321ce25e, 0x96692e31, 0xc3801a83, 0x64c1f48c, 0xf042879b, 0x674ca506, 0xece0a4d3, 0x133caec2,
            0xeb1a761f, 0x2b6ab3d6, 0x797799d7, 0x2646081f, 0xd7f2f1f5, 0x9f79f655, 0x2ffa09cf, 0x1fe4444c,
            0x873b9af3, 0x8f847d17, 0xd284e618, 0x5112bde4, 0xd6850370, 0x0535b6f0, 0x5cca23c9, 0xfcc8edfa,
            0xc1903f9b, 0x470582e6, 0xae6053f5, 0x4748d8f6, 0x901b4848, 0xb09a64b7, 0x46522569, 0x547cd7fc,
            0x2cd50046, 0xc48d2ec0, 0x693652d9, 0x64749a70, 0x77746d6a, 0x182caf79, 0x7677c1c7, 0x173f7f56,
            0xbbb206e1, 0xc3b27e06, 0xf552d33c, 0x15ee295a, 0xe04041c7, 0x1315d3f3, 0x6ac84825, 0x516e8742,
            0xe858e73d, 0x7e975ac2, 0xc84414cd, 0xcaaae2a6, 0xea3211fc, 0x652f49be, 0xed4bc75c, 0x0b10fe6e,
            0x25adb866, 0x7a9b2676, 0x988a7e35, 0x7768e166, 0xdfcee733, 0x22560aeb, 0x2a994ced, 0x9c1ed54b,
            0x14e07127, 0xe3d1b1c4, 0x07a1424d, 0x7800bb66, 0x366d4633, 0x3f30b834, 0xb5298e7a, 0x28e44338,
            0xd4f89cfc, 0xa5171b4f, 0x219712e0, 0xba732074, 0xf17e7f70, 0x0a7d0b5e, 0x5083d5d7, 0xf62c28c3,
            0x2e6608dc, 0x7299caba, 0xc2c146ae, 0xa49c3d6d, 0xc0d21771, 0x5860a4b1, 0xe1538dba, 0x9c02c2e1,
            0x96cb0e36, 0x65ec5a23, 0x487263b1, 0x216f2dc3, 0xa7119a71, 0xc10b3acc, 0x873ecfc3, 0x20a4805f,
            0x07603823, 0x48b1cad6, 0xaf4887c8, 0xdf04c243, 0x25368332, 0x43eadd2d, 0x5aa84154, 0xbcdd25d4,
            0xe625b31c, 0xe8faf288, 0x24a53aa4, 0x8f2a7e2f, 0x1d62503f, 0x9dd75fb8, 0x85467fda, 0x077e635d,
            0x1bac6c2a, 0x470b5c82, 0x12542907, 0x622c883d, 0x4e69e57a, 0x422afa4e, 0xd972f9df, 0x1aef38f5,
            0x011b7e3b, 0xed5ddad1, 0x701793cf, 0x985d9175, 0xbd331271, 0x59c10ef8, 0xc0257bb3, 0x005b06e1,
            0x167197d0, 0xf8bef512, 0xcf914a3c, 0x6ffa51d2, 0x6c8fa68b
            };

//******************************************************************
// DOE(IV_OBF, IV_FE)
//****************************************************************** 
void kv_doe(uint8_t doe_fe_dest_id){

    doe_init(iv_data_uds, iv_data_fe, iv_data_hek, doe_fe_dest_id);

    VPRINTF(LOW,"doe_fe kv id = %x\n", doe_fe_dest_id);

    doe_clear_secrets();
}


//******************************************************************
// HMAC(OBF_KEY , FE)
//****************************************************************** 
void kv_hmac512(uint8_t key_id, uint8_t block_id, uint8_t tag_id){

    hmac_io hmac512_key;
    hmac_io hmac512_block;
    hmac_io hmac512_lfsr_seed;
    hmac_io hmac512_tag;

    hmac512_key.kv_intf = TRUE;
    hmac512_key.kv_id = key_id; // UDS from DOE
    VPRINTF(LOW,"hmac key kv id = %x\n", hmac512_key.kv_id);

    hmac512_block.kv_intf = TRUE;
    hmac512_block.kv_id = block_id;  // FE from DOE
    VPRINTF(LOW,"hmac block kv id = %x\n", hmac512_block.kv_id);

    hmac512_lfsr_seed.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac512_lfsr_seed.data[i] = rand() % 0xffffffff;

    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = tag_id;
    VPRINTF(LOW,"hmac tag kv id = %x\n", hmac512_tag.kv_id);

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);
}

//******************************************************************
// domain separation
//****************************************************************** 
void domain_separation(uint8_t key_id, uint8_t ecc_seed_id, uint8_t mldsa_seed_id){
    
    VPRINTF(LOW,"\n\n *** domain separation between ECC and MLDSA\n");

    hmac_io hmac512_key;
    hmac_io hmac512_block;
    hmac_io hmac512_lfsr_seed;
    hmac_io hmac512_tag;

    hmac512_key.kv_intf = TRUE;
    hmac512_key.kv_id = key_id;

    uint32_t idevid_ecc_key[] = {0x69646576, 0x69645F65, 0x63635F6B, 0x65798000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000470};

    hmac512_block.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_BLOCK_SIZE; i++)
        hmac512_block.data[i] = idevid_ecc_key[i];

    hmac512_lfsr_seed.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac512_lfsr_seed.data[i] = rand() % 0xffffffff;

    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = ecc_seed_id;

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);

    uint32_t idevid_mldsa_key[] = {0x69646576, 0x69645F6D, 0x6C647361, 0x5F6B6579,
                                0x80000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000480};

    hmac512_block.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_BLOCK_SIZE; i++)
        hmac512_block.data[i] = idevid_mldsa_key[i];

    hmac512_lfsr_seed.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac512_lfsr_seed.data[i] = rand() % 0xffffffff;

    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = mldsa_seed_id;

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);
}

void kv_ecc(uint8_t seed_id, uint8_t privkey_id){

    ecc_io seed;
    ecc_io nonce;
    ecc_io iv;
    ecc_io privkey;
    ecc_io pubkey_x;
    ecc_io pubkey_y;
    ecc_io msg;
    ecc_io sign_r;
    ecc_io sign_s;

    VPRINTF(LOW,"\n\n *** ECC computation\n");
    //******************************************************************
    // ECC_KEYGEN(hmac512_tag, NONCE, IV)
    //******************************************************************     

    seed.kv_intf = TRUE;
    seed.kv_id = seed_id;

    nonce.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        nonce.data[i] = ecc_nonce[i];
    
    iv.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        iv.data[i] = rand() % 0xffffffff;

    privkey.kv_intf = TRUE;
    privkey.kv_id = privkey_id;

    pubkey_x.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        pubkey_x.data[i] = ecc_pubkey_x[i];
    
    pubkey_y.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        pubkey_y.data[i] = ecc_pubkey_y[i];

    ecc_keygen_flow(seed, nonce, iv, privkey, pubkey_x, pubkey_y);
    cptra_intr_rcv.ecc_notif = 0;

    //******************************************************************
    // ECC_SIGN(MSG, PRIVKEY, IV)
    //******************************************************************    
    privkey.kv_intf = TRUE;
    privkey.kv_id = privkey.kv_id; 
    VPRINTF(LOW,"ecc privkey kv id = %x\n", privkey.kv_id);

    msg.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        msg.data[i] = msg_tbs[i];
    
    iv.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        iv.data[i] = rand() % 0xffffffff;

    sign_r.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        sign_r.data[i] = ecc_sign_r[i];
    
    sign_s.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        sign_s.data[i] = ecc_sign_s[i];
    
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s);
    cptra_intr_rcv.ecc_notif = 0;
}

void kv_mldsa(uint8_t seed_id){

    mldsa_io seed;
    uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], entropy[MLDSA87_ENTROPY_SIZE], pubkey[MLDSA87_PUBKEY_SIZE], msg[MLDSA87_MSG_SIZE], sign[MLDSA87_SIGN_SIZE];

    //******************************************************************
    // MLDSA_KEYGEN(hmac512_tag, entropy)
    //******************************************************************     

    seed.kv_intf = TRUE;
    seed.kv_id = seed_id;

    for (int i = 0; i < MLDSA87_ENTROPY_SIZE; i++)
        entropy[i] = rand() % 0xffffffff;

    for (int i = 0; i < MLDSA87_PUBKEY_SIZE; i++)
        pubkey[i] = mldsa_pubkey[MLDSA87_PUBKEY_SIZE-1-i];

    uint32_t privkey; //no returnable when seed came from KV

    mldsa_keygen_flow(seed, entropy, privkey, pubkey);
    mldsa_zeroize();
    cptra_intr_rcv.mldsa_notif = 0;


    for (int i = 0; i < MLDSA87_SIGN_RND_SIZE; i++)
        sign_rnd[i] = 0;
    
    for (int i = 0; i < MLDSA87_MSG_SIZE; i++)
        msg[i] = msg_tbs[MLDSA87_MSG_SIZE-1-i];

    for (int i = 0; i < MLDSA87_ENTROPY_SIZE; i++)
        entropy[i] = rand() % 0xffffffff;

    for (int i = 0; i < MLDSA87_SIGN_SIZE; i++)
        sign[i] = mldsa_sign[MLDSA87_SIGN_SIZE-1-i];

    mldsa_keygen_signing_flow(seed, msg, sign_rnd, entropy, sign);
    mldsa_zeroize();
    cptra_intr_rcv.mldsa_notif = 0;
}

void random_generator(uint8_t *fe_id, uint8_t *cdi_idevid_id, uint8_t *ecc_seed_id, uint8_t *mldsa_seed_id, uint8_t *privkey_id, uint8_t *cdi_ldevid_id){

    /* Intializes random number generator */  //TODO    
    srand(time);

    do {
        *fe_id = rand() % 0x17;   // FE kv id
    } while(*fe_id == 0);

    do {
        *cdi_idevid_id = rand() % 0x17; 
    } while((*cdi_idevid_id == 0) | 
            (*cdi_idevid_id == *fe_id));
    
    do {
        *cdi_ldevid_id = rand() % 0x17;
    } while((*cdi_ldevid_id == 0) | 
            (*cdi_ldevid_id == *fe_id) | 
            (*cdi_ldevid_id == *cdi_idevid_id));

    do {
        *ecc_seed_id = rand() % 0x17;
    } while((*ecc_seed_id == 0) | 
            (*ecc_seed_id == *fe_id) | 
            (*ecc_seed_id == *cdi_idevid_id) | 
            (*ecc_seed_id == *cdi_ldevid_id));

    do {
        *mldsa_seed_id = rand() % 0x17;
    } while((*mldsa_seed_id == 0) | 
            (*mldsa_seed_id == *fe_id) | 
            (*mldsa_seed_id == *cdi_idevid_id) | 
            (*mldsa_seed_id == *cdi_ldevid_id)  | 
            (*mldsa_seed_id == *ecc_seed_id));

    do {
        *privkey_id = rand() % 0x17;
    } while((*privkey_id == 0) | 
            (*privkey_id == *fe_id) | 
            (*privkey_id == *cdi_idevid_id) | 
            (*privkey_id == *cdi_ldevid_id) |
            //(*privkey_id == *ecc_seed_id) |
            (*privkey_id == *mldsa_seed_id));

}

void main(){

    printf("----------------------------------\n");
    printf(" KV Smoke Test With Crypto flow !!\n");
    printf("----------------------------------\n");

    uint8_t doe_uds_dest_id;
    uint8_t doe_fe_dest_id;
    uint8_t cdi_idevid_id;
    uint8_t idevid_ecc_seed_id;
    uint8_t idevid_mldsa_seed_id;
    uint8_t idevid_ecc_privkey_id;
    uint8_t cdi_ldevid_id;

    //Call interrupt init
    init_interrupts();

    doe_uds_dest_id = 0;
    random_generator(&doe_fe_dest_id, &cdi_idevid_id, &idevid_ecc_seed_id, &idevid_mldsa_seed_id, &idevid_ecc_privkey_id, &cdi_ldevid_id);
    
    if(rst_count == 0) {
        VPRINTF(LOW, "1st FE flow + warm reset\n");
        
        kv_doe(doe_fe_dest_id);
        
        //issue zeroize
        ecc_zeroize();
        hmac_zeroize();
        sha512_zeroize();
        sha256_zeroize();
        mldsa_zeroize();

        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }
    else if(rst_count == 1) {
        VPRINTF(LOW, "2nd FE flow + warm reset\n");

        kv_doe(doe_fe_dest_id);
        
        //Issue timed warm reset :TODO
        rst_count++;
        printf("%c",0xf6);
    }
    else if(rst_count == 2){
        VPRINTF(LOW, "3rd FE flow + Cold reset\n");
        rst_count++;
        printf("%c",0xf5); //Issue cold reset and see lock_FE_flow getting reset
    }
    else if(rst_count == 3) {
        VPRINTF(LOW, "4th FE flow after cold reset\n");

        printf("doe_fe_dest_id = 0x%x\n",doe_fe_dest_id);
        printf("cdi_idevid_id = 0x%x\n",cdi_idevid_id);
        printf("idevid_ecc_seed_id = 0x%x\n",idevid_ecc_seed_id);
        printf("idevid_mldsa_seed_id = 0x%x\n",idevid_mldsa_seed_id);
        printf("idevid_ecc_privkey_id = 0x%x\n",idevid_ecc_privkey_id);
        printf("cdi_ldevid_id = 0x%x\n\n",cdi_ldevid_id);

        kv_doe(doe_fe_dest_id);

        kv_hmac512(doe_uds_dest_id, doe_fe_dest_id, cdi_idevid_id);

        domain_separation(cdi_idevid_id, idevid_ecc_seed_id, idevid_mldsa_seed_id);

        kv_ecc(idevid_ecc_seed_id, idevid_ecc_privkey_id);

        kv_mldsa(idevid_mldsa_seed_id);

        kv_hmac512(cdi_idevid_id, doe_fe_dest_id, cdi_ldevid_id);

        //issue zeroize
        ecc_zeroize();
        hmac_zeroize();
        sha512_zeroize();
        sha256_zeroize();
        mldsa_zeroize();

        printf("%c",0xff); //End the test
    }
}

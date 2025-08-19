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
    obf_key = 31358e8af34d6ac31c958bbd5c8fb33c334714bffb41700d28b07f11cfe891e7
    uds_enc = e4046d05385ab789c6a72866e08350f93f583e2a005ca0faecc32b5cfc323d461c76c107307654db5566a5bd693e227c144516246a752c329056d884daf3c89d
    fe_enc  = b32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835
    IV_UDS  = 2eb94297772851963dd39a1eb95d438f
    UDS     = dff9f0021e1ab0bda2781e1a709cafdb341953bdbd6836d9c1ea520a6043041daf7218b19ce98302a5f8f95a6b51f5c1219a09d73819e2ba0d2c4b932489c586
    IV_FE   = 144516246a752c329056d884daf3c89d
    FE      = cfc155a3967de347f58fa2e8bbeb4183d6d32f7427155e6ab39cddf2e627c572
*/

    const uint32_t iv_data_uds[]  = {0x2eb94297,0x77285196,0x3dd39a1e,0xb95d438f};
    const uint32_t iv_data_fe[]   = {0x14451624,0x6a752c32,0x9056d884,0xdaf3c89d};
    const uint32_t iv_data_hek[]  = {0x14451624,0x6a752c32,0x9056d884,0xdaf3c89d}; // TODO unique value

/* CDI HMAC512 test vector
    KEY =   dff9f0021e1ab0bda2781e1a709cafdb341953bdbd6836d9c1ea520a6043041daf7218b19ce98302a5f8f95a6b51f5c1219a09d73819e2ba0d2c4b932489c586
    BLOCK = cfc155a3967de347f58fa2e8bbeb4183d6d32f7427155e6ab39cddf2e627c572800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000500
    TAG_forCDI = 32cd8a75b5e515bd7b0fe37a6de144696aeedb1f5e03225a71fc690f5b004ff593794db7a99ced97c376385149c4ecafd3afd70cb657a6f6434bfd911983f4ff
*/

/* DOMAIN SEPRATION HMAC512 test vector
    KEY =   32cd8a75b5e515bd7b0fe37a6de144696aeedb1f5e03225a71fc690f5b004ff593794db7a99ced97c376385149c4ecafd3afd70cb657a6f6434bfd911983f4ff
    BLOCK_forECC = 6964657669645F6563635F6B6579800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000470
    TAG_forECC = 86c247003f3f4c6638defa2f9c53b39411c0cc97a1fd7938ebb70da1cadfb64e53b45ac2e53b2304a0401c21667d7847faf2f9156e7aa200ff7a187cea0c56e3

    BLOCK_forMLDSA = 6964657669645F6D6C6473615F6B657980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000480
    TAG_forMLDSA = 782728e2bfee2de7a4d12a8045fcc6537aa62f5075541c0f0ec0206bccaffd285c02325df422b4042cd71927ecd07217882641e2c0ed8c3024fe04c32dfdd029
*/

    const uint32_t msg_tbs[]     = {0xBEB06525,0x1497FCE1,0xD4C43092,0x8BC09E14,
                                    0x7B250CF3,0x25A40258,0x784262F6,0x858B8056,
                                    0xD68C6A23,0xD4CC5CBD,0xCEAD7EBF,0x8F6A97E6,
                                    0x63711440,0xB7AD9A08,0xF9C15788,0xFF54875D};
/* ECC test vector */
    //seed = 86c247003f3f4c6638defa2f9c53b39411c0cc97a1fd7938ebb70da1cadfb64e53b45ac2e53b2304a0401c21667d7847
    //const uint32_t ecc_privkey[]  = {0xb039c5b7,0xc97d4ddb,0xf09d273a,0x9e777ae2,0x35660a88,0xc7cac86f,0xde67abfb,0x86023f72,0x6095c7cc,0x47507bde,0x9c6b47b6,0x7743a575};
    const uint32_t ecc_pubkey_x[] = {0xfb5711c0,0xdb7df321,0x1fee8d69,0x47c3540f,0x50f37ebd,0x5e22284b,0x37956d3d,0xea19df46,0x3959a89f,0xc69235b1,0x076baeba,0x38c4b6d4};
    const uint32_t ecc_pubkey_y[] = {0x22ebd645,0xdebe1275,0x87709669,0x3d86642e,0x9ea09a78,0x79c0f817,0x7aac2020,0x0e4addcd,0xd3c6b0fa,0xab3493d1,0xedd215dc,0x9723258f};
    const uint32_t ecc_nonce[]    = {0x1B7EC5E5,0x48E8AAA9,0x2EC77097,0xCA9551C9,0x783CE682,0xCA18FB1E,0xDBD9F1E5,0x0BC382DB,0x8AB39496,0xC8EE423F,0x8CA105CB,0xBA7B6588};
    const uint32_t ecc_sign_r[]   = {0xff7a18ca,0x001b8116,0xabc335d8,0x5ac433b2,0x7825739f,0xa55c3326,0x3c6e37f3,0xdffdd743,0x94e84d22,0xdf33cd5e,0x5f102114,0xaba9da51};
    const uint32_t ecc_sign_s[]   = {0x336b9416,0x8b5c6665,0xdcf7cb72,0x2467606c,0x2262ed05,0xc4f47af5,0x85722e3a,0x1fe0f126,0x77db3beb,0x5510ecae,0x2c56cfa5,0x6fe6d349};

/* MLDSA test vector */
    //seed = 782728e2bfee2de7a4d12a8045fcc6537aa62f5075541c0f0ec0206bccaffd28
    //msg = BEB065251497FCE1D4C430928BC09E147B250CF325A40258784262F6858B8056D68C6A23D4CC5CBDCEAD7EBF8F6A97E663711440B7AD9A08F9C15788FF54875D
    const uint32_t mldsa_pubkey[] = {
            0x8c9af2ea, 0x5127c6a5, 0x624be352, 0x75e4325f, 0xd7091f6b, 0x03c9ed96, 0x6318e0f3, 0x52067abe, 
            0x2a9aad99, 0x0d8a5214, 0x9b24e950, 0xccd657f8, 0xec018d47, 0x53c1c05d, 0x60ee364d, 0xd3dfc1d2, 
            0xe9ce128d, 0x6df1f40b, 0x92d28ce4, 0x2ea0b1b8, 0x07be0171, 0x3bbc2216, 0x6b28eb95, 0x09127485, 
            0x3a2cb78a, 0x323b8259, 0xecd3f76a, 0xcd206f45, 0x4aa0c3f1, 0xd7001569, 0xecd39938, 0x76b964d7, 
            0x940650f3, 0xf2dab341, 0xa7bdf620, 0x76c73125, 0x6cbc96fb, 0x388514c3, 0xb82d2748, 0x9edcd3a1, 
            0x804e6614, 0x6aa81313, 0x6ffd1de4, 0xaf13c3b5, 0xda16def0, 0xe1e4b46b, 0x3871ea15, 0x3675c97f, 
            0x0d3f70e2, 0xf2c0995c, 0xbc1e30dc, 0xc5ff4db9, 0xa99138d0, 0x2f67432b, 0x0a4b4f79, 0x5314b66a, 
            0xfb29bbef, 0x46c54065, 0xf8e5fa9b, 0x219327e3, 0xe845fecb, 0xbd7ff684, 0x521f5981, 0x07a85b42, 
            0xa12c273a, 0xe6069e86, 0x49037761, 0x83ddeaf9, 0x3eb0be52, 0x6632c360, 0xeaf75564, 0x6fe9680a, 
            0x38867734, 0xc94b3d26, 0xab15fc48, 0x8a2b52ff, 0xa15af61b, 0x82cbf132, 0xe2837174, 0xe9acf0c6, 
            0xe547577f, 0xf6cef6a5, 0x0441cb73, 0x1b4e4671, 0x23748901, 0x6c3af206, 0x6783e61b, 0xf515973d, 
            0x0123a4cb, 0x8dff4bc0, 0x4542924c, 0xa693bb00, 0x80d03fec, 0xd0863e1d, 0x1a65a241, 0x714164c9, 
            0x4b89cda4, 0x4e0b03bd, 0x28136ce8, 0xbfecc248, 0xd543804e, 0xf88d8464, 0x1f85fce5, 0x88583ffe, 
            0x453c6110, 0xbc49c4bf, 0x1c7af8f0, 0xf71d6263, 0xcbe8f1fb, 0xd8faef80, 0x12ff3830, 0x072e12df, 
            0x0b4aa37d, 0x3e24ea34, 0xfd8ca27f, 0x2a67ff81, 0x26fbef87, 0x57bff168, 0xad6de91a, 0xd4183765, 
            0x01704e8d, 0xe9728a95, 0x916cb77a, 0x8599815f, 0x431a8c18, 0x5ae5518f, 0xf717d828, 0x001efdd5, 
            0xd3697073, 0x2f7ad0f6, 0x07727e8c, 0x2dba4598, 0x8b71e5cf, 0x11a9a27f, 0xca1d98c6, 0xd40afbc2, 
            0xa199453d, 0xf165ec65, 0x1ba1f591, 0xf86f84e9, 0x93b4ab7f, 0x738c4bd5, 0x5cbab522, 0xc53fe9e9, 
            0x9dbf51b8, 0x4dde6b25, 0x2d433803, 0x9dc65647, 0x201fa4d8, 0xaa113180, 0xb5050a45, 0xebbe6b54, 
            0x41d24571, 0x1a1643b1, 0xa66a4a30, 0xb27e8b5c, 0x75c04dbd, 0xd967146a, 0x40e75c42, 0xe2b58bdd, 
            0x35cb4073, 0x84ec07d8, 0x22e918e1, 0xf8778031, 0x76f437f0, 0x68f24b8b, 0xcc4afd7b, 0xa3941b58, 
            0x23c56591, 0xa27832ce, 0xd71336ad, 0x2f9769eb, 0x74ce1003, 0x9109b366, 0x8ad988c4, 0x94c78ce8, 
            0x4c2cc276, 0x30083f4b, 0x285acf4f, 0x506de88f, 0xbf210af2, 0xe8a7fe0b, 0x7339b5c2, 0xc5e453a7, 
            0x7848e6c4, 0x95a40844, 0xa5230fb4, 0x62ae08eb, 0x05230697, 0xbc2378fd, 0x91010769, 0x9fb4eda8, 
            0x1626c31d, 0xabba7f12, 0xda049d15, 0x551e82f1, 0xb61326e9, 0x2d8d14a2, 0x8d116124, 0xe1b543c4, 
            0x7b2b16ad, 0x07729403, 0xeb5d9326, 0x3844253a, 0x9f45f39f, 0xe1fe5e00, 0x65af0b6a, 0xde506e84, 
            0xa4b935e3, 0xd0a52410, 0x362d41da, 0x4e936df2, 0x1f716b8b, 0x8711a548, 0xe33b8a2d, 0x831ad193,
            0x0953428c, 0xda6b8cde, 0x76873594, 0xe5174adb, 0x23d663b0, 0xf9f0d667, 0x7b2dae60, 0xe13f1e8c,
            0xb5a42738, 0x9ec51b80, 0x11f8f032, 0xf65acd7b, 0xc836667b, 0x83bcbef5, 0x915d1626, 0x5b1deb44,
            0x6fd9cb31, 0x8c7b385d, 0x441b9d0f, 0x974c077e, 0x8a83d655, 0x4d3f5be8, 0x8ca4e328, 0x75b1f92f,
            0x77ef3ce1, 0x8356a720, 0xca2736ad, 0xbbc525aa, 0x520b7a11, 0x7da8494a, 0xdf3966dc, 0x8d5420e9,
            0xeccf1bf9, 0x276dfe89, 0x8891a00d, 0x1df6b00c, 0x8582812e, 0x892501cb, 0x45750cf2, 0x7e72ef42,
            0x35d8b783, 0xcaa7272a, 0x8b9cb23d, 0x59f6784e, 0x94618574, 0x87eab298, 0xbfe57a2a, 0xaa406e9a,
            0x65b06fa7, 0x7fa5e692, 0x362e5abc, 0xeb804860, 0xd9995820, 0x374ac75d, 0x3caae211, 0xaeed2eb9,
            0x985863b5, 0xe1c18d14, 0x5f91a69f, 0x48b200c9, 0x7b5a385a, 0xec9bf8db, 0x4de3d4b3, 0xf3afa93f,
            0xb5079323, 0xe64326c4, 0xd5bc2bc1, 0x569d089b, 0xd5516379, 0x6b5bec04, 0xc7f225f1, 0x94681608,
            0xfe885267, 0x208ffcae, 0x86a947a0, 0xd9b491b8, 0xfc38210f, 0x0c1a10a7, 0x5e88e879, 0x9adc66fe,
            0x5a568b4e, 0xeebcd8ac, 0x64f6c0b0, 0xf2612651, 0xbe445253, 0xc35982a5, 0x4f80f550, 0x3342451a,
            0xb7aa8bd0, 0xe8e806a2, 0x5788109a, 0xaa0c99d4, 0xcd347f85, 0x215bcfd1, 0x88659e77, 0xedee6714,
            0x3302eace, 0x44ac9de8, 0x3973f49c, 0x3d34d573, 0xac640607, 0x1a19b07c, 0x620d379b, 0xed2fbb5e,
            0x96460759, 0x1f2c9988, 0x8f87c8a5, 0x1e748bb6, 0xb57dc798, 0x3d982e74, 0x5e7ed6db, 0x139706e0,
            0x3c68e2c1, 0x85116b23, 0x8c88949e, 0xc830fc9a, 0xfee6faaf, 0x09c3ca0c, 0x7a06ee4f, 0xaf69d7ce,
            0xcac33f51, 0xf5a2bc7a, 0xa5c0da0a, 0xa46eb304, 0x0fd1f74f, 0x6eb151c3, 0x2deea396, 0xefdebe1f,
            0x60a6914a, 0x38780dbb, 0x78e09881, 0x2e6e77bf, 0x821f8eae, 0x642667c2, 0x530d1b4d, 0x318af88b,
            0x17419773, 0x9dc3b18f, 0xe3e0ca45, 0x07aee4a5, 0xdeecc6a9, 0x08991e9f, 0xe102d815, 0xb62564f2,
            0x25ab0503, 0xf1c4c865, 0xc40cb2a4, 0x96bc90b8, 0xab5bcec0, 0xa371c2a2, 0x26a59af8, 0x20dac5d0,
            0xcb0d5536, 0xaa338add, 0x93fbb38a, 0x52cd354c, 0x1938978c, 0x837beba4, 0x89a73c65, 0xc4396541,
            0xa5b0fe22, 0x6fab1cf9, 0xf4a91baa, 0x7455160b, 0xe09fdc79, 0xd285a90c, 0xfdbd98e5, 0x483c11fb,
            0x4bcd1626, 0xb934c87e, 0xfa1ab4a3, 0xb8a8711d, 0xcff8fbeb, 0xf9973285, 0xcc1e5bd0, 0xa8b22fc8,
            0x0c283500, 0xaa8fc18c, 0x43ad9296, 0x88fe7a3d, 0x47819026, 0x801bc958, 0x89d88df3, 0x1b9fe7e3,
            0x8f8b10fa, 0x60e14539, 0xae014f7b, 0xcfda5eaa, 0x8c58305f, 0xc554d62e, 0xb754e84c, 0xe0c62e3f,
            0x7285401b, 0x684f60d3, 0x10f6fa17, 0xa2f13cc9, 0xd9f9c52d, 0x065c6105, 0xe0e4d8ca, 0x384d6e79,
            0xec60822b, 0x6cb31fd6, 0xaa7a5445, 0x82f244b3, 0x671cdf7b, 0x5b755d04, 0xad34a04e, 0x6794886e,
            0x3c782535, 0x4e7f628f, 0x9ac4880b, 0x50b13623, 0x3a7e0ca5, 0xf025b7a2, 0xd26ef444, 0x78a7100f,
            0x374d1a5c, 0x4f6f41ca, 0xc78cc672, 0xf83201a2, 0xacd5df48, 0xa6bdb4e4, 0xb02e1a61, 0xc794ac9f,
            0x01156bce, 0x6a1b71ad, 0x73dcf6de, 0x323bd3d5, 0xef8e6b8d, 0x4b85e377, 0x1c74620d, 0xe250b25b,
            0x5c25d1c3, 0x86c1679d, 0x05902cb6, 0xe6c2e535, 0x77ed0467, 0x3b139dc3, 0xbbb641a7, 0x09cf875b,
            0xbcb67a74, 0xdb6d3971, 0x338e96ca, 0x15415c3e, 0x168214f4, 0xb31e36eb, 0xd7d05c90, 0xa8f419c2,
            0x9f994d69, 0x2f29e04a, 0xe2c12ead, 0xd67740dc, 0x26dbdd0f, 0xc52c14ca, 0xcd8f808a, 0xd448b656,
            0x765d00e3, 0xf81a846a, 0x01109481, 0x3111e07b, 0xa10a590e, 0x4104790d, 0x9bb79331, 0x4c8cc573,
            0x5913f8a3, 0x794674c9, 0x4a86f580, 0x1584bfd5, 0xb699c013, 0x9ec68548, 0xfa393b96, 0x1638a4a3,
            0x3a62e7e5, 0xdd31652a, 0x5fd4347a, 0x19bb797d, 0x774eaee5, 0x1bc62071, 0xc5ffabab, 0xf8c40797,
            0x1da921cb, 0x08341bc6, 0xfbb40f1b, 0x80101e14, 0xd6bbbe95, 0xc33fb607, 0xb600cbe4, 0x8ca1a327,
            0xc22326a2, 0x19b914ff, 0xf5845a64, 0xdb0b4423, 0xce8743d6, 0x94160885, 0xc0bb7702, 0xe675f5d8,
            0x2926f785, 0x62e9dcca, 0xa15b246a, 0x80ec00ac, 0x06b6c6f5, 0x4d63e0d8, 0x88e91dcb, 0x609ed273,
            0xdfdbbed5, 0x87227878, 0xdbea9ef1, 0xd5c94b7c, 0x75b6e700, 0x2ea0dc32, 0x5f3f8b0c, 0x19a23f41,
            0x205919d7, 0xc0138bcb, 0xe5468990, 0x54c173f3, 0x21f48809, 0x35cd92be, 0xe45d5505, 0xd77f5af1,
            0x8ab7453d, 0x7375cfb0, 0x0374c5f7, 0x61e7c7e9, 0xf0eb9691, 0x64440264, 0x4f78bec0, 0x49718005,
            0x0b8f5aea, 0x43c881bf, 0x1345bc61, 0x7c22ea63, 0xdfdd3ac0, 0xf5860437, 0xb4934bca, 0xf02669f9,
            0xf03621b0, 0xfa741c49, 0xbcff629f, 0x15d61112, 0xe6999d8a, 0xa30b2bb6, 0x116cd65f, 0xf2f776b2,
            0x2ebe6a94, 0x0baa84d5, 0xf43318cb, 0x34e99f9b, 0x9575015a, 0x8ddad31a, 0x37222d37, 0x73ba60ca,
            0xbc1c018a, 0xd06badc8, 0x2dc8ec42, 0x462678c3, 0xafc62fb6, 0xbd5dd96c, 0x78e841c8, 0x25842f73,
            0xfa9d1415, 0xf6f97db9, 0x0f872c23, 0x9aef26c1, 0xbae85853, 0x832caa12, 0xb8be6d1b, 0x4a315589,
            0x7f4029f3, 0xbc33447d, 0xa0493fed, 0xd12e2ec1, 0xa9733127, 0x545e6490, 0x6457e4fc, 0x4f2530e8,
            0x1ea89e14, 0x77bc4034, 0xdfd591b3, 0x02c7898d, 0x84d4bd8e, 0x25c2a91e, 0x4d1872c1, 0x7fd57bfa,
            0xf7ad1758, 0x56a03de7, 0xea5fd7da, 0x1b425b20, 0x92a1911a, 0x4d7fcc71, 0xde3ca485, 0xa6479510,
            0xf2ce50f5, 0xb63ecd0a, 0xa05af65d, 0xe8320562, 0x40930337, 0xb866e964, 0xfdf3948f, 0x703913c7,
            0xb64c490c, 0xc19d9b34, 0xafe0677d, 0xc7c89e99, 0x6252f126, 0x7359f487, 0x94cb1507, 0x47689c40,
            0xda3d5ca3, 0x6d0be00e, 0x92cab9f6, 0x77cd64f9, 0x38ad0229, 0xb861c60f, 0xbc0171a8, 0xf38f69e3,
            0x580466b3, 0xeede5c84, 0xb0450fc0, 0x7dfbd10d, 0xe5599ef5, 0x1f1986ad, 0x3a347def, 0xebd2d292,
            0xd7995201, 0xfa103183, 0x81c079f6, 0x301224a4, 0xd1736cd0, 0xdb5715c6, 0xc02af7fb, 0x39974470
            };

    const uint32_t mldsa_sign[] = {  //additional 00
            0x003c3530, 0x271e180d, 0x06000000, 0x00000000, 0x00000000, 0x00000000, 0x9b8c6748, 0x3d3531fb, 
            0xc4b29a3b, 0xf5b2a595, 0x91868061, 0x1df0dec7, 0xa09f7742, 0x1a15f0d8, 0xa69f8720, 0xa3a19991, 
            0x716b4631, 0x2d2b28cc, 0xc29b8a60, 0x4101f6d2, 0x807a3b05, 0xe4480ffb, 0xb4c8d43f, 0xeb841380, 
            0x64542c47, 0x71d2dcaa, 0x3acaee94, 0xfdff2093, 0x5cce818a, 0x8e8a290b, 0xa1d7092f, 0x31cd3c5d, 
            0x5955ef0e, 0x3881e5d6, 0x9c67ccc8, 0x5871ac8d, 0xbded4096, 0xa3db41bb, 0x9561729f, 0xe6857cdf, 
            0x648648e0, 0xcf044ecd, 0x6dc2c6f5, 0x4fea4b4f, 0x8a3161f3, 0x99c577a1, 0x56f5834c, 0xd3ac4a63, 
            0xac6d6f48, 0xff0a7a31, 0x4bf0cdac, 0xc62f5634, 0x184b0ab4, 0x578ffa06, 0x14ffc10d, 0x7ddcd658, 
            0x50daa018, 0xeafdcdb6, 0xc8b9c8c7, 0x7dfac0de, 0xf4cdce3a, 0xfac10b4e, 0xb89386d8, 0x78a3573b, 
            0x34485836, 0xe3b323b5, 0x83086e68, 0x7d9fc672, 0xccffd63d, 0xa6dce9c1, 0xfe5c36e5, 0xb7cbec67, 
            0x6e3f4617, 0xe73fb854, 0x64c4747d, 0x32854958, 0xea94b2c6, 0x166f4229, 0x1f5dad71, 0x7333e291, 
            0x1b20dba2, 0x204967e0, 0x8f1dfacb, 0xb79b8cb8, 0x4e70a91d, 0x9d5cf583, 0x81564700, 0x35930ba4, 
            0x42347c86, 0x2d143c30, 0xdb50fbef, 0x5f3602fa, 0xb102f814, 0xb52d9a7e, 0x9ec7eb53, 0xd1f14cb1, 
            0x4f030851, 0x0c5ae880, 0x5b2f0fe1, 0xb70fe43c, 0x7bbb9f83, 0x88887480, 0x72251588, 0x92a30849, 
            0xc1e14634, 0xdb46408d, 0xddfef463, 0x8603e2a7, 0x306b9b29, 0x2f960057, 0xecc8d566, 0x37a4a6c1, 
            0x3ac3dd27, 0x583c61be, 0x67acebee, 0xe40cca4d, 0xbf6d2b05, 0x0d9e80b7, 0xfbbcbf52, 0xfbd8aaee, 
            0x709ef92d, 0x7e6d3e6a, 0x23104f16, 0x37272b5c, 0x56df24f0, 0xd45ed07b, 0x8e09c4fa, 0x2d20fe81, 
            0xbd720b62, 0x7eeb245b, 0x142d18d3, 0xad696548, 0xb5c277a0, 0x6e5ad933, 0x1f88838b, 0x9444d9a8, 
            0x54c30203, 0xfc3fc53a, 0xf625c3e0, 0x76ee0f04, 0xad023e5a, 0x2f178d2c, 0xc5dda729, 0xc6a57c1b, 
            0x3e9da575, 0x8a48b8fb, 0x4ec8ef28, 0x83a49c57, 0x1d2c498e, 0x9a19f5f3, 0x90f45624, 0xe54d646f, 
            0x88ed5ec5, 0x048adf5c, 0x45a172e7, 0x885e1507, 0x330e2ce1, 0x87cd2adc, 0x1cdb2088, 0xfc2533c8, 
            0xfe5984fa, 0x85877e17, 0xea6c730b, 0xff662bd2, 0x62610ecd, 0x784626b8, 0xc4665c68, 0x6d3104d7, 
            0xbad66c98, 0x86dae9a8, 0xd7e05ee5, 0x9f9d8dcd, 0xd7c301ae, 0xf79bd3f5, 0x1e4f5b45, 0x65d62fd0, 
            0x8e54caf5, 0x113a8fe1, 0xed490f94, 0xde05bdda, 0xa66aebd3, 0x7e96c3ad, 0x23bd4bca, 0xcec862a8, 
            0x5fb1cf42, 0x42115ba2, 0x92dacaa0, 0x59fca486, 0x3098a81f, 0x2c7e2e79, 0x8564e495, 0x3a3ed30c, 
            0x5ab29d74, 0x0d6e47c9, 0xf4941115, 0x0434025e, 0x0e317578, 0x256de0c7, 0x51fcd0a6, 0x1e9f144d, 
            0xae2f1b66, 0xda30b61f, 0x843aee8c, 0xc37ec98b, 0x1bdfb975, 0xc44f98e1, 0x92205f5d, 0x5ef6bd42, 
            0xe24fa09a, 0xb176d44a, 0x6b5ea3fc, 0x3c57de21, 0xd3f3dc29, 0xf88d1d18, 0x7a9ba1f5, 0x460a487e,
            0xf74f85ce, 0x6bf61118, 0xf01b54c5, 0xc69ad5c1, 0x9cca0fd4, 0x119d9ec5, 0x3609f057, 0xfb589d56,
            0xb5077f4b, 0xd2fe5b00, 0x017c74d2, 0xf1019535, 0x9e0e6826, 0xf0f9c6eb, 0xb9f86b2e, 0xf68883cc,
            0x496d2fba, 0x434f3275, 0x3d794f02, 0x564a6084, 0x248668ab, 0x48de6b04, 0xdfa0d67f, 0x42a917b1,
            0x356a6914, 0xafa6499a, 0x65dd5daf, 0x298c25f8, 0xdd60f389, 0xe6d9afcc, 0x801c48f7, 0xd23a1564,
            0x18c22699, 0x243c3093, 0x8ca499f2, 0x7121670e, 0x33446689, 0x962f15ae, 0xa0e62388, 0xe8799c34,
            0x24d1ec5f, 0x4486f0f4, 0x98d71930, 0xc91303cd, 0xacd7257a, 0xbdc1f75e, 0xc4143a28, 0xe96913dc,
            0x34ad2bd7, 0x497ffd17, 0x04c9bc4e, 0xb7762b43, 0x3dd496b5, 0x57856c79, 0x379fba2f, 0x021d4d50,
            0x5d8fe6b4, 0xce155601, 0xcd570708, 0x564c6e7b, 0x1ccea31b, 0x94e4a615, 0xe366bd54, 0x4ae38944,
            0xb99a9a13, 0x5381ce0d, 0xbf4b73f0, 0x1d743dd3, 0x8b696ee4, 0x40ce47f8, 0x92a5d16e, 0x9cced9dd,
            0x41e8f42f, 0xb8307df2, 0xac3e6ba4, 0xe00ca221, 0x78aca6d3, 0xf12c449a, 0xd3fe365e, 0x2ff847b7,
            0x01eec5e7, 0x62710923, 0xfe3a10ee, 0x149cf43b, 0x14ad7205, 0xd671d16d, 0xbfd47dd1, 0xd7169660,
            0x40f0a78e, 0x4fafa1e5, 0xcb79951a, 0x501ecf66, 0x96f55cfa, 0xf0e61264, 0x334e5a35, 0xc3422489,
            0xbba945b2, 0x9fde40de, 0x6bf67109, 0xa0bfb3bc, 0x4944f42c, 0x45f563be, 0xb15b1d13, 0xe6787060,
            0xa5909b7e, 0xd01491d2, 0x64a6b82e, 0xd046b703, 0x553fce6e, 0x3254c2d1, 0x59a77452, 0x0f055dc5,
            0xd8f64dbd, 0xccb02ae6, 0xd9827f29, 0x63175d0d, 0x0a76b289, 0xbe4fc4f5, 0x1d8b08cf, 0x31a2d8a1,
            0x29f3f8d3, 0xa33d4fcb, 0x1c02fc29, 0x2b1664d4, 0xa4e3bfc3, 0xabed5112, 0xc597069f, 0x05256cd0,
            0x4136fc53, 0x0c48409a, 0x27ef2214, 0xab82b4c3, 0xb6c93ceb, 0xb9e25ba2, 0x35e71c11, 0xbe6b0b5e,
            0xd9b2dc74, 0x030cacbc, 0xe9064c94, 0x4afee7b9, 0xf99f6b6f, 0x8cd5eb47, 0x1d4414c1, 0xda166fe7,
            0x02031c86, 0x73ea8387, 0xb128fdcf, 0x44c5ffd8, 0x5eb14a77, 0x83739e4d, 0xf7e90c1b, 0x436426b2,
            0xfb2f1655, 0xf496b78d, 0x1f9cc885, 0x0e3dedb9, 0xd4bbaf3e, 0xe97e7429, 0x85d4da04, 0xf3957bdd,
            0xbe12bb30, 0x205d9c5f, 0x260fd138, 0x3ad459cc, 0x6e08479b, 0x5231da9e, 0x62be3900, 0x21562951,
            0xbd871789, 0xb38ff740, 0xb92238ab, 0x8dd90aca, 0x56866016, 0x9adbf0d3, 0x8cbe7035, 0xa3752443,
            0x46c05fd4, 0x1f5185d8, 0xb561989a, 0xa2536e04, 0xf49ea68e, 0xb87ffb80, 0x15ebc0a4, 0xd6c16ed2,
            0x91e86eff, 0xceecfc42, 0xccd33ee5, 0xf8527c04, 0x52266cc9, 0xc7b1b891, 0x9d105fd3, 0x9a488913,
            0x04b7f2c9, 0x8c21b090, 0x7187f37d, 0x3b19c0dc, 0xd83605a3, 0x8b04315e, 0x0f2954b8, 0x4021418a,
            0x58fd6455, 0x5e7ff860, 0x756c616b, 0x77a72f9c, 0x1e855f3a, 0xff598c75, 0x1d676891, 0x16ec7b74,
            0xba852731, 0xb713335d, 0x2d1089d7, 0x8ff2d38a, 0x2cb05925, 0xde0b851c, 0x4a4f991e, 0x85791710,
            0xb9340ced, 0x8d86bf7f, 0xab4004dd, 0x12827dc2, 0xd9e19406, 0x4ff8c8d7, 0x99ea6e4a, 0xc7c12b39,
            0xc44295fc, 0xe064c82b, 0x5b0987af, 0x380042a0, 0x33922f0b, 0xd25ecaef, 0x5e9c46ed, 0xfa52b304,
            0x51b7f667, 0x2635e9a3, 0x93c1170c, 0x962c83ff, 0x88f7df33, 0x30c58a24, 0x44b89c49, 0x79d464ee,
            0x51300ab2, 0x1ba75826, 0x35c9e51f, 0x6a7c2598, 0xc0894fe1, 0x1620e1d6, 0x7043355c, 0x60a7bffd,
            0x9d08169e, 0x257737d5, 0xe2c28334, 0xb3ec3567, 0xf7d5ab85, 0x28668fa7, 0x22dfeb7d, 0x1b540e1f,
            0xaea03ae1, 0x7318b6e4, 0x6417b651, 0x257d13bc, 0xb08366ca, 0x133f5e37, 0x5f0cdf66, 0x2918d1e3,
            0xed6361bd, 0x4e19f1f5, 0xa7da171d, 0x464998ae, 0x7f6a454d, 0x35645cf6, 0x2f4a5347, 0xcb290374,
            0x7a3c943b, 0x7d61b6cd, 0x783c9b35, 0x9182709f, 0x209115ec, 0x2fbee090, 0xa5fa2970, 0xbfe782ab,
            0xa6199fd0, 0x90be0c06, 0xf71edf12, 0x0fcf06f9, 0x2fb739be, 0x88c02074, 0x39b4caf6, 0x6e410b03,
            0xbaaee37c, 0x4cbaec31, 0xe50003b6, 0x4302fa67, 0x466b500f, 0xbcd5b1b5, 0xc8d336d7, 0x99a01063,
            0x323bb566, 0xf7284b29, 0x4ab4af94, 0xa51e3b96, 0xbf0908aa, 0x9ca72c38, 0x72a10c77, 0x02181e59,
            0x0fac0f56, 0xc832d5d0, 0x01eefdfd, 0xe79d1914, 0xbc929373, 0x3617b23c, 0xe36b86c0, 0xc31fc2e8,
            0x13c80f9b, 0x29677c01, 0xd6ed9a6e, 0xb0ad172b, 0xdf40fa10, 0x00bf1ed6, 0xa2cc53f0, 0xa998c81d,
            0x0182fb2d, 0xd25f8eed, 0xcea1266c, 0xe2d90dd5, 0xf0f84336, 0x52cf3dae, 0x091fde91, 0xd993de79,
            0x87822c99, 0xa1a57004, 0x6b67db69, 0x7de7792a, 0xe39843af, 0xbb8915fb, 0x7af0f5ce, 0x71644bf8,
            0xe8a10d14, 0x34707d50, 0x9cb0bd74, 0x6748b4e4, 0xf34f105a, 0x3ebcffba, 0xb44ed431, 0x8b4aec2a,
            0x651f0a3b, 0x32b552d8, 0x27515da4, 0x448be4c2, 0x908ad7bf, 0x62d0eb6f, 0x346b3b05, 0x5bcb7ceb,
            0x8b41c555, 0xa73cc569, 0x2f0b57af, 0x19e58174, 0x12754079, 0x8f691add, 0x0c9747f2, 0x13b5ad8b,
            0xe815c585, 0xb93a0791, 0xdeb8d5c1, 0x478751f0, 0x19473bd1, 0xc8b2e589, 0xffe67a0e, 0x150a02c4,
            0x3e302d3c, 0x49ee6dfe, 0x73c31c7d, 0xd6632365, 0x854aa1b8, 0xc33090ac, 0x00dc3f0e, 0x7c4b36b8,
            0xc8485dab, 0xb453e4a2, 0x7a16c553, 0xf0ef6546, 0x8b238680, 0xe224dc3c, 0x21e0431c, 0xae0dde1a,
            0xa7497856, 0xd5d217b0, 0xee66e262, 0x4eac25a9, 0xaae6343f, 0xf67f871f, 0x89a22512, 0xb7c1c46f,
            0x2b671e62, 0x4851730d, 0x37fe1870, 0x16563838, 0xb853c628, 0xd03d3918, 0x7eb4b0c9, 0xcc4bbc1e,
            0x07c7feec, 0x3bd73f58, 0x5de02a9b, 0x5ca571c8, 0x20bf4114, 0xa2a9a9e8, 0xf24a8e17, 0x7f4ea713,
            0x7e22cd8e, 0x09a8358d, 0x79ef68f6, 0xc1d42580, 0x74ccec68, 0xe0176c07, 0x7178e924, 0xbb77b435,
            0xb7a7c422, 0x3f73bd4e, 0xe520d9d6, 0xb0043516, 0xe42074af, 0x78ad7c74, 0xc123431d, 0x6e4d1447,
            0xfcd035a1, 0xfbf12da6, 0x1e6dd3c3, 0x40c8c968, 0xa86c4c3d, 0x47ef5e93, 0x2d89ec27, 0x396df067,
            0x16c6c542, 0x7028642f, 0x75d537d4, 0xec4cdaa8, 0xeb6dfd51, 0x97f25672, 0x0202ac10, 0xc027ead3,
            0x778f21b1, 0x1ea4eac9, 0x6ea76c23, 0xd710e53b, 0xea56e4fe, 0x23307909, 0x887feb9c, 0x11f1e77e,
            0x429f6255, 0x5de7f3b9, 0xa576e9b1, 0xda127f9e, 0xaabd060d, 0xf1c24eb0, 0xd60e326f, 0xd9e37a37,
            0xa3507321, 0x3c4aa68d, 0xec4cd348, 0x5ea8a3d8, 0xb341170b, 0x21ed427e, 0xe18081b3, 0x37dc2e04,
            0xe52b3c66, 0x208859c0, 0x151dccef, 0x59b5c517, 0xff75e5ba, 0x4ec75667, 0xd6e4de79, 0xc40d371a,
            0x1689cd0d, 0x1e891011, 0xb0986695, 0x9472712e, 0xfb12b919, 0xeb68a3ec, 0x2190bab6, 0xa87efe4c,
            0xf80d45b9, 0x9082f1c5, 0x2e85aa5a, 0x50ea14c9, 0x9961ba50, 0x5875b8d5, 0x8f465135, 0xa518bceb,
            0x3679ba05, 0x29e7e5a0, 0x263ab783, 0x70ee1b19, 0x864f05e2, 0x43ef32b3, 0xc4bb0405, 0xd45e68bc,
            0x0a28a295, 0xd4d3636c, 0xb97eb43f, 0xf0dbd0ce, 0x8d44c5fc, 0x0e5a59a7, 0xb95085de, 0x37291205,
            0x2ae4efaf, 0x130752e1, 0x4292f70b, 0xd8781460, 0x5e48ef5b, 0x91357eca, 0x0b56d288, 0x6d577713,
            0x6de4397c, 0xf6ac6776, 0xe96378c5, 0x7ae040ae, 0xb2e93fda, 0x796e4c6f, 0x07e4864e, 0x36d165e2,
            0x34d5d365, 0xc94e9105, 0x71986817, 0xf15e7d2d, 0xb861ce2e, 0x1a32433a, 0x0a077bd3, 0xd1f59488,
            0x78b0e204, 0xbfb50689, 0x87fd8225, 0x1814222d, 0xcf24abb0, 0xb9e4fc43, 0xbda18b36, 0xc441796d,
            0x8c213806, 0x561d53aa, 0x5177d01f, 0xbd14a271, 0x93f3bfb0, 0x49242483, 0x3bb839cc, 0xc1f77f4b,
            0x0d9fb354, 0xad289aff, 0xd81e579f, 0x10a2f599, 0x40a78e62, 0x469246a7, 0x597ae77e, 0xdd9276df,
            0xf1753920, 0xf8b5b833, 0xfa482212, 0x08311d3f, 0x16f0ff32, 0x62f5ffe1, 0x6deef8be, 0xb1c86ebb,
            0x03ba859e, 0x99a2bce5, 0x04da5936, 0x88c40286, 0xa011787f, 0xd1ac0e1d, 0xb38897c2, 0x09d40e4d,
            0xd50a8fe9, 0xe7c4972f, 0xc20cc04e, 0x3a833d8f, 0x082a4150, 0xb3be4900, 0x9c06e0c6, 0x5bba9a17,
            0xcc18219c, 0xe8cacb38, 0xcdd2027d, 0xc6bead00, 0x22149fb7, 0xac2df8d8, 0x363fcc97, 0x1bbe0197,
            0xcbbb01d6, 0xf28ab478, 0x88a21ab4, 0x479ddb8c, 0x0ab7a053, 0x72b4b0e8, 0xb28a4649, 0x09b5f520,
            0x2e2bc34c, 0x93459caa, 0x7dc1f6bb, 0xcab12578, 0x3c0dcb45, 0xb34cc3a9, 0x1e57b661, 0x6a427ddc,
            0xdb877617, 0x6bded3af, 0xebceeb17, 0x6afeaf2a, 0x01c82161, 0x5beb00f6, 0x74c26cb7, 0x04c3d33f,
            0x45009731, 0xbde7d9ce, 0xbe1ec24c, 0x77c33701, 0x572d9cd3, 0x8adb0316, 0xd86f58e6, 0xa8798e40,
            0xe3e62ff9, 0xfe4969d6, 0x20aa062a, 0x99707466, 0xddf68fd3, 0x59401d33, 0x244ef432, 0x65a9461e,
            0x50830ec9, 0xa369660b, 0x511aef99, 0xa4a07c5b, 0xa6fa496e, 0x810ef902, 0xe4af5066, 0xe4ff21c7,
            0xdfe1067f, 0x16f31b5e, 0x7416ed4d, 0x3db589f7, 0x096b42dc, 0xb790d280, 0x3bc52163, 0xa006b7f7,
            0x630ecc4c, 0xf55cdbf9, 0x94cdb30e, 0xcf5cc2d1, 0xf47a12bc, 0xa5e51236, 0xad18d384, 0x4b662878,
            0x310a3768, 0x52905a40, 0x11f37b9a, 0x3b388b7d, 0xd7cd99e8, 0x5f8c2de9, 0x6b244053, 0x74e2e0bd,
            0x39b5ec11, 0x9c340e77, 0x5c9af2c3, 0x88998c01, 0xac87602f, 0x175577f9, 0xa04c845d, 0x13adc056,
            0x7e87ef57, 0x8ff6777d, 0x8c24f8c1, 0xa246f50b, 0xe1fb3d95, 0x6c5b4d13, 0xec34d826, 0x87432e87,
            0xd1de8f97, 0x9f56e52e, 0x9bd8eca4, 0x02cfafa3, 0x75cc768a, 0x39081bda, 0xbbe9fced, 0x83e2d2ba,
            0x16c9fd66, 0xca3ef1ee, 0xda99aeed, 0x91042f3c, 0xa748deac, 0x7b4350da, 0x56ca0bcc, 0xe3cc7e55,
            0x64c337ab, 0x68d99a90, 0x74190fc4, 0x42b58353, 0xc5b30176, 0x0a431225, 0x568c9f2d, 0x5cb0f29e,
            0x1e0957bd, 0xce843382, 0x201338ab, 0x92b4962d, 0x73ce99d6, 0x06dadc44, 0x1824e614, 0x24b897cc,
            0x0ada8a2b, 0x49a61f3a, 0xd929ee50, 0x93eab1db, 0x5486ca92, 0x217c6f3c, 0xb7c2a894, 0x5457fedc,
            0x9a12361d, 0x63393402, 0xc00a738f, 0xf7ed5c91, 0x1061da55, 0x920a20cb, 0xe36003a8, 0x54ceedb3,
            0xe7616985, 0x5351b838, 0xa1a3dc47, 0xd9740606, 0x16d0b977, 0xecd91dc4, 0xaeee8d81, 0x9697eea0,
            0x782867c4, 0x4142382b, 0xf4f0df6d, 0x8a21a5a5, 0xfd105ea9, 0xef75ba7b, 0xc1c86492, 0xa90cf093,
            0xfa1ca046, 0x7fd0a949, 0xc9282965, 0xa4910150, 0xbe2e286a, 0x710cf382, 0xaa7c20b6, 0xfe76ccd6,
            0xfabb3f80, 0x777dd2b3, 0x1d42834a, 0x1d0b49ec, 0xfe98c8d1, 0x75f813be, 0xf4a0137d, 0x23b30c17,
            0xe8c73b4d, 0xe7040c22, 0x8d075e9a, 0x0139403c, 0xb702db9b, 0x8c332419, 0x404c33bb, 0x78987219,
            0x6a0e6db9, 0x5ab41235, 0x2e5f83ea, 0x60dd9ec0, 0xc1ca59cc, 0x2e8ec539, 0x9f243efd, 0x18fb9090,
            0x92825686, 0xf7046fa4, 0xd45e9649, 0x6b5ca373, 0x27db6e15, 0x45d47315, 0xe705b88e, 0xecf1f4cc,
            0x23cd201c, 0xbb11af32, 0x25f117e8, 0xb2826bbd, 0x7a53a5aa, 0x3814a4b5, 0x3b635746, 0xeac54ec6,
            0x7d1068bc, 0xe38ec941, 0x4130766d, 0xcdfb01f0, 0x1779c1f8, 0xa392621a, 0x932d3db5, 0x4fa14f61,
            0xcd996128, 0x6c753e4c, 0xbb3b6855, 0x525b445b, 0x758f40d3, 0xa4482dcb, 0x810437bd, 0xde1c17b8,
            0x2fd6aeb3, 0xc91fcf4a, 0x3d1b9781, 0x2895e61b, 0x3256f2e7, 0x99545339, 0x1295bbdb, 0xcb774f1f,
            0x588dce7d, 0x448108f5, 0xc1405c69, 0x7c1daf78, 0x1e6295f5, 0x661b2a6d, 0x3636a85a, 0xc9fbd8fe,
            0x21f065d7, 0x7aca940b, 0x38dc83bd, 0x11fbeaf1, 0xeb31cc0e, 0xff70cfff, 0x7ff0d4f6, 0xdcd1ad00,
            0x0f0329ef, 0x0af9e154, 0xd9b604b2, 0xaf00c98a, 0xfefe9cde, 0x99315860, 0x0324919d, 0x4b457d9c,
            0x7aadba33, 0x61c78579, 0x868ce5a8, 0x37bcc95c, 0xa8181e71, 0x5d2f8674, 0x09a44b6c, 0x046023b1,
            0x1b18746a, 0x2a184c03, 0xa7e8a1f8, 0xbf7d9433, 0x7553d299, 0x0a1149ea, 0x0ceb88f8, 0x418b5a43,
            0xaae99b43, 0x5d626d60, 0xbd4954d0, 0x1ceb177f, 0x856c3589, 0x80840d3a, 0x062beece, 0xef6c71fe,
            0xe6b162a3, 0x588623b2, 0x26b9948d, 0x7d77d9e0, 0xf03903d3, 0x3383a056, 0x41737c7d, 0x8959008e,
            0x7cb9b14d, 0x159a06b7, 0x079d62c2, 0x3b8bfc21, 0xc90193b7, 0x446888bf, 0x674feaf9, 0x47cc8387,
            0x3222dbed, 0x2e6b0863, 0x16ccda7c, 0x62e5fb71, 0x10d7db11, 0x96a0a5ea, 0x9cbb2c57, 0x1829456b,
            0x23b1cb19, 0xb61b8913, 0x41733273, 0xe97aaa5d, 0x2f64ea59, 0xa63c3ed4, 0xfcac3760, 0xcc1d62ca,
            0x2fa622df, 0x741b06f5, 0xc14cf094, 0x1afa5de3, 0xb2168dbb, 0xcfd6fadd, 0x4dcca727, 0x11601d8c,
            0x05c84e58, 0x5a036ee4, 0x375228cc, 0x5287eab2, 0x8e68ba1c, 0x9908c0ae, 0x4548e243, 0x7d55f641,
            0x2c11bb23, 0x2750f293, 0xee098130, 0x92f588a1, 0xbac67723, 0x7f3ac5c8, 0x2a1cce0c, 0x8a0d7556,
            0x58cd5be8, 0xc6664caa, 0x7c957069, 0xd096112a, 0x7bb470ea, 0xc573af1b, 0x36e2a423, 0x3f8b4645,
            0xfbe25d7f, 0xe02d3bf7, 0x60bc42c3, 0xfd17c2c5, 0x690c82f6, 0x6da2124f, 0x3c49b035, 0xb00823bf,
            0xf7c640ed, 0x8e64c6d8, 0xd55d8407, 0xd6b24cff, 0x47c3a371, 0x7682a067, 0xc3a60aa7, 0x22150b9a,
            0x69831642, 0x8e2a682d, 0x539a25d1, 0xd9a05aef, 0x77c4e670
            };

//******************************************************************
// DOE(IV_OBF, IV_FE)
//****************************************************************** 
void kv_doe(uint8_t doe_fe_dest_id){

    doe_init(iv_data_uds, iv_data_fe, iv_data_hek, (uint32_t) doe_fe_dest_id);

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

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE, FALSE);
}

//******************************************************************
// domain_separation
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

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE, FALSE);

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

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE, FALSE);
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
        pubkey[i] = mldsa_pubkey[i];

    uint32_t privkey[MLDSA87_PRIVKEY_SIZE]; //no returnable when seed came from KV

    mldsa_keygen_flow(seed, entropy, privkey, pubkey);
    mldsa_zeroize();
    cptra_intr_rcv.abr_notif = 0;


    for (int i = 0; i < MLDSA87_SIGN_RND_SIZE; i++)
        sign_rnd[i] = 0;
    
    for (int i = 0; i < MLDSA87_MSG_SIZE; i++)
        msg[i] = msg_tbs[i];

    for (int i = 0; i < MLDSA87_ENTROPY_SIZE; i++)
        entropy[i] = rand() % 0xffffffff;

    for (int i = 0; i < MLDSA87_SIGN_SIZE; i++)
        sign[i] = mldsa_sign[i];

    mldsa_keygen_signing_flow(seed, msg, sign_rnd, entropy, sign);
    mldsa_zeroize();
    cptra_intr_rcv.abr_notif = 0;
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
    printf(" KV Smoke Test With DOE flow    !!\n");
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

        kv_doe(doe_fe_dest_id);

        printf("%c",0xff); //End the test
    }
}

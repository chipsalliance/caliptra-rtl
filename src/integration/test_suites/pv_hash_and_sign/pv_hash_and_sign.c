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
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "keyvault.h"
#include "sha512.h"
#include "mldsa.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = MEDIUM;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    VPRINTF(LOW,"---------------------------\n");
    VPRINTF(LOW," KV PCR Hash Extend Test !!\n");
    VPRINTF(LOW,"---------------------------\n");

    uint32_t msg[] = {0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000};

    uint32_t exp1[] = {0xf57bb7ed,
                       0x82c6ae4a,
                       0x29e6c987,
                       0x9338c592,
                       0xc7d42a39,
                       0x135583e8,
                       0xccbe3940,
                       0xf2344b0e,
                       0xb6eb8503,
                       0xdb0ffd6a,
                       0x39ddd00c,
                       0xd07d8317};

    uint32_t exp2[] = {0x11143121,
                       0xbeb365e6,
                       0x3826e7de,
                       0x89f9c76a,
                       0xe1100411,
                       0xfb9643d1,
                       0x98e730b7,
                       0x603a83a4,
                       0x977c76ee,
                       0xe6ddf74f,
                       0xa0b43fbf,
                       0x49897978};

    // exp3 = SHA512(31*384'h0 | exp2 | nonce)
    uint32_t exp3[] = {0x4f373650,
                       0x83ef4325,
                       0x29e9bcdb,
                       0x404adf86,
                       0x05566e5c,
                       0xe1f01af8,
                       0x01a485ec,
                       0x46d049d1,
                       0x48028f54,
                       0x31afc07f,
                       0x4abc21c1,
                       0x5df9f791,
                       0x125cff3b,
                       0xbff7aa9f,
                       0x7610ca06,
                       0x819ec76a};
                       
    uint32_t exp_ecc_sign_r[] = {
                             0x871e6ea4, 
                             0xddc5432c, 
                             0xddaa60fd, 
                             0x7f055472, 
                             0xd3c4dd41, 
                             0xa5bfb267, 
                             0x09e88c31, 
                             0x1a970935, 
                             0x99a7c8f5, 
                             0x5b3974c1, 
                             0x9e4f5a7b, 
                             0xfc1dd2ac};

    uint32_t exp_ecc_sign_s[] = {
                             0x3e5552de, 
                             0x6403350e, 
                             0xe70ad74e, 
                             0x4b854d2d, 
                             0xc4126bbf, 
                             0x9c153a5d, 
                             0x7a07bd4b, 
                             0x85d06e45, 
                             0xf850920e, 
                             0x898fb7d3, 
                             0x4f80796d, 
                             0xae29365c};

    uint32_t nonce[] = {0x01234567,
                        0x11111111,
                        0x22222222,
                        0x33333333,
                        0x44444444,
                        0x55555555,
                        0x66666666,
                        0x77777777};

    uint32_t exp_mldsa_signature[] = {  //additional 00
0x0036312d, 0x29211a15, 0x0b000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x0000923a,
0x35120192, 0x8c7902ee, 0x3a3305f8, 0xd6cdc4bc, 0xb7380deb, 0xe1b3967b, 0x250ae5c6, 0xa1763af5,
0xc7bb8e74, 0x69676649, 0x0ceae8c0, 0xab965d34, 0x2f140e05, 0xee0d03e9, 0xfb53319a, 0xe1692381,
0x1e5ea6df, 0xd6434c22, 0xa561dc9b, 0xae1b21e8, 0xc6d6092e, 0x6a3ab09d, 0xcba8145c, 0x30c2b4ce,
0x077d03a0, 0x25b03776, 0x9b1b7036, 0x7762b8a8, 0x1ad7e4ef, 0x3eaf6fd7, 0xcdfbf65f, 0x26c41a42,
0xc34e95bb, 0x4cb371d4, 0x8a8b3153, 0xab176918, 0x11d19515, 0x818c2f51, 0x88db04bd, 0x95fbfe64,
0x73c1d612, 0xfbe2c71e, 0xd742b90b, 0x2d4f13be, 0x8bba5c10, 0x65e44cae, 0xf77d3c63, 0xae9bf94c,
0xb836454c, 0x24cc0440, 0x3a70a18b, 0x3acb5759, 0x0f7d637a, 0xbd930eb4, 0x96506a26, 0xec02d343,
0xb4633f7b, 0xa8169781, 0x727e7f4a, 0x107d38f0, 0xc4a2e471, 0xedbf8ea9, 0xdc676e78, 0x46078b4b,
0xcd027ce7, 0x80993786, 0x814afce1, 0x331fd9b2, 0x0571990c, 0x9d2909d2, 0xbc3b47d1, 0x0ef2239c,
0x7b96f6e6, 0xdf2fbb5c, 0x5a9d7527, 0x37219cab, 0xfd5ae9dc, 0x4d131045, 0x43ce0239, 0xf1f1b44a,
0x5ec3c232, 0x74531c13, 0x65779213, 0x261c93c2, 0xe751a4cb, 0x18a8ccc1, 0x26ad1f4a, 0x523a7f47,
0xf0c85d03, 0x98fd2c01, 0xa51672e4, 0x188c13a3, 0xf90669b3, 0xee48a4d5, 0x303fbd71, 0x3a43523e,
0x0c0bfb94, 0xebab1954, 0xd20e8e80, 0x98810ab2, 0x4bb50345, 0x719cb84c, 0xf4cf1494, 0xd421c089,
0x845c7561, 0x8ed00e8c, 0x87f33570, 0xd30db6d5, 0xf3fa5268, 0x7a6cdd34, 0x342f01f2, 0xf64f3ac0,
0x917d5096, 0x41454a3a, 0x3c027579, 0x7e8503dd, 0xe8b33e36, 0xdda70384, 0x145b8231, 0x7e8165ad,
0x27e76223, 0x066c5e46, 0x554a213a, 0x3d2b3c6f, 0x683e8040, 0x9e9910c8, 0xd60142c7, 0xf6992422,
0xbc795d32, 0x2de14e57, 0xb73aa2ad, 0x1a2124f6, 0xc3245e44, 0x5222a8f8, 0x9894952b, 0xcc46318c,
0x4b24cd74, 0xe3794f60, 0xb2341ede, 0x18b27363, 0xa5ea14c9, 0x3802cf01, 0x2606d3ab, 0x219d792b,
0xdfc53480, 0xa742ce21, 0xc74f90f0, 0x86177a19, 0x90ab8a88, 0x4a9e5fa7, 0x0e9864dc, 0x894a6a62,
0x98865b48, 0x3a15164a, 0x549814cb, 0x2c03254d, 0xd8038ecb, 0x33dd1c95, 0x0d6fa8ad, 0x8249be1b,
0x5eb0a9f2, 0x3e799102, 0xe8bca683, 0x379ec694, 0xe0a0b6dd, 0x323f110e, 0xef34e510, 0xc2f2054c,
0x234b2c0c, 0x210ac1a0, 0xd0b06e09, 0x0d30925c, 0xf6496cc5, 0xc91b1018, 0xaf3e8711, 0x42ac170b,
0x204ad031, 0xfedb0cd0, 0x9fa66d15, 0x845555a3, 0x189baf07, 0x2ee87265, 0x5f6569d6, 0x27248f82,
0x2f060f48, 0x5a28cb9f, 0xf06c35c3, 0x3f41b2eb, 0xa32f701c, 0x08c50777, 0xf7290341, 0xeb60f822,
0x62d13a42, 0x2ff880cb, 0x859bdcac, 0x4e98f2c3, 0x0712471e, 0x66d78334, 0x3dc7c396, 0x3bbb1298,
0x010f0da2, 0x85bab8d1, 0x59fefa8d, 0xd15a0fca, 0xd70cc8d3, 0x1097605c, 0x840753f9, 0x3637dc45,
0xdc4ca0c3, 0x2e747956, 0x2de69719, 0xc05d1489, 0x9cf67b52, 0xb99ef53b, 0x9995a5d3, 0x0dc2570a,
0x1495c802, 0xa9774a44, 0x38eb53df, 0x3fdd1e27, 0x97d67c7e, 0x99a95a0b, 0xdc62aeb4, 0xeef47a4d,
0xf858384a, 0x892a068b, 0x8db701ee, 0x51c7d15b, 0x72cdc84d, 0x2795bced, 0x16809770, 0xf87a55b1,
0xb00415f2, 0x48d89cbb, 0x6e1e6d4a, 0x490c4aa2, 0x6a0f1b68, 0x87ec2e70, 0x711b19ec, 0x73627ed6,
0x506b7032, 0xea06ceb3, 0xea2fba42, 0xc9207e1a, 0xfcc4bd7e, 0x76c7213c, 0x0f96c7be, 0x22382ca7,
0x452f65c6, 0x025ddb1b, 0xed786ded, 0xd2ce7fc1, 0x1beb56fd, 0x49ef3d94, 0x875b3895, 0x6bbbc4eb,
0xd819fb0f, 0x41ecff18, 0x6c4e3732, 0x4d79c763, 0x057a8cb7, 0x65f5d5d7, 0x0a62f4d1, 0x91fb4ff0,
0xce40558d, 0x8725579b, 0xc4cb82e0, 0x1f512b79, 0xedd33521, 0xd2d07a93, 0xffe45f15, 0xf4a329a1,
0xdb2e07df, 0x9bfe4404, 0x3cf10c02, 0xe6faf14e, 0xa214d894, 0x716462e9, 0x52fbf348, 0x406b3f85,
0x3700b09c, 0x4c9dcc5f, 0x1a7b80c3, 0x75779bf9, 0x79ec8940, 0x645a067c, 0xb8cc2fff, 0x69ededba,
0x9f271b10, 0xd4b83d70, 0x4cc7a4ab, 0xb8485ead, 0xcc4f8618, 0x288e9098, 0x010f145c, 0x58829246,
0x3c5686df, 0xac1947d6, 0xb568b212, 0x9ecc1cfa, 0x3e1fcb57, 0x274efaa6, 0x33df8a43, 0x24dec957,
0xb47874e9, 0xe1056877, 0x101fae54, 0x38b873ac, 0x3252e264, 0x08de955c, 0x061887b0, 0xd3d45e62,
0x5907c7ec, 0x78ea8075, 0x7b2a8ddb, 0x56765f83, 0x9738fd72, 0x444102b0, 0xf38395ad, 0x76c43d1f,
0xceef62a9, 0xea1e400b, 0x2c5128b3, 0x5b464615, 0x9fc79805, 0x342b4296, 0x72ed5453, 0xa6b2fa8b,
0x940877fb, 0x6907f32a, 0xf85e07df, 0x91811bca, 0x10001456, 0x9e01351c, 0x931c1adf, 0x935b3384,
0x33d8e10a, 0x6c4d8f83, 0xe1d9f0fe, 0x75436a65, 0x08f0c303, 0xe74a47bc, 0x50a70d00, 0x1f3d59ec,
0x03d7085e, 0x84d67e08, 0x035966a0, 0xcd6b68f5, 0xe2f60f43, 0x0ac584eb, 0xd0d824ea, 0x990ae3f2,
0xc8d4d510, 0xf1a911cc, 0xa75e4cc6, 0xdb22cbe7, 0xc6e80336, 0xea558d3f, 0x9e7764e6, 0xe58220a7,
0xbe8a3466, 0x3dd8a5d8, 0x96f60419, 0xcc67c3df, 0x976c8aed, 0x75fe251f, 0x1f3494e7, 0x047a0cc1,
0xd0139887, 0xa0e0d59b, 0x85aa8af0, 0x4cad9d67, 0x1207fc66, 0x18160ab8, 0xf5d332b6, 0x42bc439c,
0x58b3cec7, 0x2fb83bd6, 0xb5dc3a54, 0xb304c080, 0x525d5ea3, 0x9fdc1854, 0x4423c882, 0x83a1b08f,
0x723c5621, 0x17f9a34e, 0xff0b1d09, 0xb3fe468d, 0x634563fa, 0x2b21ce13, 0x3b32454c, 0x95f3d294,
0x6263e5a6, 0x5c903158, 0xf2993d21, 0x1c9e4375, 0x95e84b60, 0xf2bf99e7, 0xe5d2224c, 0x8fef017c,
0xaa26ddd9, 0x3b072dd1, 0x45f0c049, 0xad5cbef6, 0xeb57a1ca, 0xbeea54de, 0x7c3399e8, 0x85435448,
0x0a082985, 0x7b20150f, 0x34d05866, 0x4096dc48, 0x6725d770, 0x6f1b7064, 0x7ae6b9bc, 0xd3a22b17,
0x2c22f2a8, 0xd843d933, 0xbf9d57ba, 0x1d313acb, 0x518efdae, 0x42fcd0af, 0x1f1d3fac, 0x97756dee,
0x87f34023, 0xda0d50ab, 0x274d0fbf, 0x0c5e6c09, 0x92ecfb04, 0x6245e537, 0xf9244569, 0x0e03b4a8,
0x7aaf085f, 0x7712e0ca, 0x83a38805, 0x7a38d71d, 0x17cf40bb, 0x38ed9c2e, 0xa16fb1cc, 0x44d7a955,
0xa63e1d93, 0xffbe5fb3, 0x17753072, 0x821f1b99, 0x5744356d, 0x2d3da976, 0x58036e7f, 0x90f61083,
0x505e3090, 0xd17188de, 0x013eba65, 0x5f523c8b, 0x1aedbb43, 0x79e3e696, 0xe5f6f031, 0xc1ec26ab,
0x28751cf2, 0xca18bded, 0xe130d6ca, 0x02b7cee7, 0xcf43faa5, 0x6bfabb78, 0x26ae26d1, 0x029bcbad,
0x6580c914, 0x6e029320, 0x5fc0c9a7, 0x2e96333a, 0x8d6d12ce, 0xe75202f7, 0xa3fd0d64, 0x5741dc66,
0x340f7c1b, 0x3f06f105, 0x506f23cc, 0x8095e324, 0x90f9de2e, 0x2c81cb47, 0x25c75120, 0x798daeb8,
0x05c14bc5, 0x2d11adda, 0x8f4a43a1, 0x7b9b5c88, 0xaec569b5, 0x400a5f22, 0xf41f2ff1, 0x8275179b,
0x41bea18e, 0xecb4ecd4, 0x6558e07b, 0xfe20668d, 0xe12f4033, 0xf2f76de2, 0xb4579ab5, 0x2ba812e4,
0x0c10b92f, 0xe1e7427a, 0xfecc0a96, 0x3f9f86c7, 0x30dde2f8, 0x203d93e3, 0x78b1cc18, 0x4c2077ce,
0x3dec7690, 0xc55683e3, 0xce2dd140, 0xce640791, 0xc7889629, 0x5e154684, 0xc3266122, 0x5dd17bc5,
0xeeaba55f, 0xc9c7fc49, 0x395342d7, 0xa70b223c, 0x1d64e135, 0x05fff72a, 0x1cbad05f, 0x22dd2940,
0x39ae766d, 0x6ee0de6e, 0x42ad5f43, 0x47b8140f, 0x63d07d7f, 0x372272bc, 0xc4261889, 0xaea7128a,
0x61f4ae8b, 0x2bcf0631, 0x8ea101a4, 0x433b2f37, 0x379bb5e3, 0x97cf66bf, 0x7d0cb997, 0x6fb31baf,
0x7b1e41eb, 0xd6fcbbb3, 0xbb3282bc, 0x4a04ccfa, 0xb01edf52, 0xfb581b81, 0x94342b63, 0xfce89aae,
0xcbc79d36, 0x87d18eac, 0x9b101ef7, 0x1f0cef01, 0xdb1fd2f5, 0xc288bbe5, 0x3ae2d73e, 0x951f32d5,
0xb9698b35, 0x8a7403ea, 0x7e1cce8e, 0x8a598d29, 0xb88bb5ae, 0x334a8582, 0x0566c4b8, 0x978696a2,
0x0ce21905, 0x20135512, 0xb3e65937, 0x58d766ba, 0x728d8316, 0x83a82389, 0xcd6a9110, 0x825c6531,
0x74bdeb89, 0x35190c71, 0x76983bd4, 0x405a36ad, 0x790873e2, 0xab3bcfd1, 0x29f947e4, 0x82ce595a,
0x891649c2, 0x9b65ea1e, 0xb3b76bfb, 0x5ac0e9e4, 0x0b5411ef, 0x9d4a396b, 0x67493e04, 0x1c472780,
0xb4f8a0cd, 0x0112d962, 0x9ed93a68, 0x16a43d9f, 0x5f4e44ee, 0x357d4bff, 0x7116242d, 0x793c6b2e,
0xdaed8986, 0x62bd5f63, 0xa2532eb0, 0x0ac9480e, 0x27427e00, 0xf33e398b, 0x56cab9df, 0xd71f7085,
0xfc0e2af3, 0x88282e62, 0xf9aa46d5, 0x695d490a, 0x8c37032a, 0x80b2e8bf, 0x97cf7580, 0xfd3ff1c6,
0xfa4e0d1b, 0xe0b829a5, 0x4349dabe, 0x63027538, 0xe47f23cf, 0x9c6747ce, 0xf9d30111, 0x488ece3d,
0x32709ec2, 0xbeee5839, 0x160715d8, 0x6f8c4031, 0x21024c34, 0x096925d2, 0x59c581e5, 0x52054a05,
0x2367f5bc, 0xff6b9107, 0xd1e4d2bc, 0x176a3843, 0x3588ebb7, 0x12d0fbf9, 0x921271c3, 0xe91a7c99,
0x6fee8997, 0x6e5352f2, 0x2fd6ecb9, 0x3bcd8c7d, 0x89d9a5fd, 0x6c667785, 0xcfd604f9, 0xb46f39d3,
0xbeb862d4, 0x6db9f38a, 0xf92935b5, 0x25cdc961, 0xb80499e1, 0x181cd569, 0xad04601a, 0x274d9102,
0x6f1f102b, 0xb07fc676, 0x6480d6de, 0x784d0e1a, 0x2a1c426d, 0xb24276e0, 0xc851ff52, 0xb3953cd9,
0x34222a74, 0x721f116c, 0x5c576365, 0xda162562, 0x25de7459, 0x1715da83, 0xec8856cf, 0x8cfc2e9d,
0x3fddf07b, 0x93fd1b0e, 0x43b91abd, 0x4785b4a4, 0xc036ee15, 0xf0053447, 0xf023023c, 0x773932c7,
0x2c20d783, 0x7f02272d, 0x05d5fada, 0x6e6bbe98, 0xd4221673, 0xc167df9e, 0x474fdf35, 0x0ad626e9,
0xe0d2e42c, 0x2dd3c14f, 0x377dfd8b, 0x2b6baa28, 0xec09c4a7, 0x1dbfab41, 0x76bf27b1, 0x3e1ac139,
0xaa8825ca, 0xe096ab30, 0xdaeb7476, 0xd0aa3621, 0x6d467b2e, 0x5871551a, 0xc93ccf3d, 0x3078c9fc,
0xfae04238, 0x86d771d5, 0xe3535698, 0x27058c28, 0x25fc0528, 0xc5ae89ce, 0x369dc912, 0xbddc397f,
0x3ee17cf7, 0x159d2766, 0xb2c2e686, 0x704ebba3, 0x13ac874d, 0x39403468, 0xe3aa4a00, 0x5ee922a3,
0x98383d99, 0x891b3825, 0x68487d79, 0x2696b5a0, 0x34a5d245, 0xc50db6cf, 0x7d47cc40, 0x090dc825,
0x2ceb1d4b, 0xe0ae74a0, 0x822729aa, 0xf0e6ac94, 0x30ded6e0, 0xa3bcfd88, 0xdc0f8174, 0x9d5c7cdc,
0x8819fd59, 0x616a9cf9, 0xcc0c5277, 0xed7f4ef9, 0x435627b1, 0x08f111be, 0x8dd3a1c1, 0x07b23b25,
0xfac12ea3, 0x26178391, 0xceb16072, 0xc3413b63, 0xd7afce42, 0xbe405c7e, 0xe104f655, 0x8e277130,
0x5ac38ceb, 0x6c1e5872, 0x90ee59dd, 0xc3b1edc9, 0xc3df0ee6, 0x6252ce1a, 0xca837261, 0x09b807fb,
0x6449d108, 0x8993f74c, 0x5b5e45a4, 0x212ee503, 0x002b9acb, 0xd7eeea81, 0x6eb902c3, 0x6fef1213,
0x24b32a28, 0x0fd67f1c, 0x44aed4d1, 0x5cb14e76, 0x59d5d2f4, 0x2c838659, 0xe3b48760, 0xe3db4d52,
0x69c99259, 0xfb150669, 0xd9854e67, 0x4c1dfed5, 0xc492dec4, 0x245e8969, 0xad2ebb21, 0x03cab8c3,
0x1d9c6d37, 0x27976dcd, 0xad3d8962, 0x316625cf, 0x885126f7, 0xc2af6263, 0xde9b6dbc, 0xde66022e,
0x12b39152, 0x984b17ff, 0x38c20512, 0x13e02707, 0xb98d0663, 0xf958fc25, 0x117777b3, 0x66c3afb2,
0x6af5f521, 0xd88715a9, 0x833a9ee8, 0x3e8a3911, 0x28ea297b, 0x27cd902d, 0xefafc04c, 0x85c3e74f,
0x305a962b, 0x797680a5, 0xb065a7df, 0xc0315f46, 0x3c01da04, 0xf3d84cb3, 0xd8417dc6, 0x2be72b0c,
0x865010ae, 0xdeb3ce1b, 0x05e6ee28, 0x49f75977, 0x643a949a, 0x40729c67, 0x5ac35c8a, 0x4bd69299,
0x48482b14, 0x232012ec, 0x3bf37c15, 0x94838756, 0x1f5b516f, 0x2a46d273, 0x18b02e18, 0xa993a48f,
0x076f6ac8, 0x4b9383c7, 0x9736a641, 0x4ee85678, 0xbfa77340, 0x2e300ee3, 0xb6a555ec, 0x1d6b6caa,
0xba95044d, 0xe66da238, 0x309c4988, 0x0c8da434, 0x6444867a, 0x3fb0018e, 0x43c0a60e, 0x08db737d,
0x59fbee24, 0x009a2a90, 0xfd133276, 0xf5b19b18, 0x55510917, 0x4e046423, 0x5d01c2b5, 0xbf07f799,
0x72e4bd65, 0x29b7221f, 0x9fc554a5, 0xee892f9d, 0xd2b92856, 0x16c239ba, 0x974fcc8d, 0xd5b88f4b,
0x9f9e2891, 0x97f3cd42, 0xc5ade759, 0xe223d875, 0x84100977, 0xbbba97ed, 0xcfdab6c2, 0xed8c433a,
0xba053b97, 0x9c722054, 0x59c79cc7, 0x66d3d9ba, 0xc67d660a, 0x992dade9, 0x652b4358, 0xf532470e,
0x1027e4c5, 0x6f13fb18, 0x716e42ac, 0x3f3d528c, 0x32f7f85c, 0x5736eae7, 0xe4273836, 0xfa772382,
0x73487d1c, 0x74f145e4, 0xe886c3fe, 0xca8c1322, 0xafcb9ad8, 0x93c8d0c8, 0xab916a02, 0x8358c19e,
0x31b22fbd, 0x45f3d16c, 0x89fd7d9f, 0x05b6cf46, 0xd01c0f1d, 0x1a7acc3b, 0x3bac6c1e, 0x1eff9f30,
0xb7e40fbb, 0xd81d6908, 0xdf190fb4, 0x754fbbcd, 0x50c487c9, 0x1ad8c99f, 0x0614c6da, 0x0194dafe,
0x8a87fe19, 0xcb775138, 0x8964b059, 0xa0dcaf2d, 0x79b9fc22, 0x078f7d5c, 0xb2ba8416, 0xaa9bfebe,
0x8097ff69, 0xc82782e4, 0xe65f27cd, 0xd680859c, 0xf87c5cd1, 0xda048c6a, 0xd80afd59, 0x91b9adbc,
0xa1be1d5b, 0x944b2eeb, 0xf399afa6, 0x3a71b733, 0x8804bfed, 0xddc42449, 0x15923fb0, 0x07c741c4,
0x56810265, 0xe09f9613, 0x41f44afe, 0xcb8c7820, 0x9a8f361a, 0x9db484ea, 0xd573af56, 0xca3bdb4e,
0x3bd20a3f, 0x0ea4df10, 0x154d7bba, 0x3a0dd671, 0x359559b3, 0x0c13ca8f, 0x304ab6ba, 0x7f4779cd,
0xd8f387ea, 0x22273b99, 0xc93fc073, 0x60095293, 0x260da785, 0x56bc27bd, 0x7dbf4904, 0x5b166100,
0xacfa0f71, 0xfdac6833, 0x69a0d81c, 0xd9f30e07, 0x6c36be80, 0x7d504574, 0xf661fc47, 0x05a1f18c,
0x346d5435, 0xba407c9d, 0x0adbebc0, 0x8c0f9a21, 0xbef41db3, 0x9ceeeb16, 0xdaa9087f, 0x7f0de503,
0x21b61f61, 0xda381d35, 0x58f2eb29, 0xedf3f4ec, 0x13c46925, 0x92ad2466, 0x98900eeb, 0xe203b680,
0x586131df, 0xee95fc07, 0xe5ec24e1, 0x83df268c, 0x0f14e2cd, 0x4dd43a8c, 0x6d04398a, 0xd13056cc,
0xcc19f366, 0x7e79d5ce, 0x12fe644b, 0x248a7d7c, 0x1ed3219b, 0x87090e76, 0x25a2e093, 0xdefe7342,
0x0808e818, 0x0b354f70, 0x751e09b2, 0xbc67985e, 0x2f524a71, 0xfdefea01, 0xd4c0be3e, 0x706547bb,
0xc1d6893c, 0xb5de2dac, 0x2e4eb649, 0x72c7d552, 0x4d44153f, 0xf05ac448, 0x61f99c5d, 0xf7b2eb92,
0x86f421b8, 0x9d076216, 0xa4953930, 0xa3f2ac40, 0x65d56af2, 0x8d35a03a, 0xf28598c8, 0xab7520d3,
0xa17a7335, 0xf33fb253, 0x90701ac0, 0x6caa6b62, 0xd7c7d22c, 0x34948c7f, 0x774573a9, 0x2f738920,
0xd1adec4a, 0x8d66e134, 0x09d11d94, 0x2ca901a8, 0xc0cb9dfb, 0x01bda2c3, 0x2c130096, 0x1ce14740,
0x3bee8e14, 0x7633b70d, 0xe183fb4d, 0x7b253ec7, 0x1d867c51, 0x54c30a9f, 0xf381c4f0, 0x6f5442a3,
0x4e76a33f, 0xf54c64dd, 0x3d466a36, 0x9ac7669b, 0x057e350d, 0x51a3cacc, 0x5243f230, 0x9f0d8afa,
0x0b2e0705, 0x1b59b489, 0x6fb9739a, 0x3acda9ff, 0xc255d659, 0x52c0ffda, 0x0bded84d, 0x084da8fe,
0xb32731b3, 0xfcad050d, 0xf8ea31df, 0x4c7227f9, 0xb0c9f210, 0x44087082, 0x29efc8b4, 0x32c32bc9,
0xd4a85a78, 0x5d86d91c, 0x03d016d5, 0xd43890df, 0xbf7eee9f, 0xce929349, 0x8eda7e2f, 0x495a7269,
0x9312866a, 0x6296f2b1, 0xc71cb01d, 0x1b58d91e, 0x2f508508, 0xf5adc215, 0xbf89b19d, 0x46336c00,
0x08f5e824, 0x5b59eb9e, 0xcd902419, 0x868f3d4f, 0x9a40157d, 0xed008716, 0x5a7b50dd, 0xa12b3588,
0x03373f51, 0xc7642af3, 0xd61cb848, 0x5a28fce5, 0xd995c64d, 0x91a7d1b6, 0x3fa40626, 0x849e0052,
0x158c239f, 0x0b517ded, 0xf5649ba8, 0xf7d707b3, 0x55e8d0e9, 0xb7370bb6, 0xf4dcf7a6, 0x06e84617,
0x53707c64, 0x5ab6f9c6, 0xa884538c, 0x95f29cf1, 0x8629b12e, 0x832761c7, 0x0931b4ac, 0xe7199d4a,
0x4e8a4163, 0x18139ae7, 0x4e0b9934, 0x3fc49ace, 0xddd1280c, 0xa92cdf3f, 0xe2312b0d, 0x81dc7251,
0xe5f2714c, 0x376fae23, 0x47eb3a41, 0xebff724e, 0x3b74d769, 0x7053b0fb, 0xa79044f6, 0x1eb96ddb,
0xa26ed730, 0x3b577027, 0x60080154, 0x911406a1, 0x5e9d0b50, 0x52d3eaa3, 0xaaa59155, 0xd0ec569d,
0x01c11b28, 0xf5a4926a, 0x791fb02a, 0xb06bfd28, 0xa45dbd6c, 0x31bdb345, 0x9c3994a9, 0x54dd20b6,
0x83f77540, 0xd7e53766, 0x784cb5fc, 0x41be7973, 0xf8a8b10b
};


    volatile uint32_t* reg_ptr;
    uint8_t offset;
    uint32_t read_data;
    uint32_t reg;

    //init_interrupts();

    //set hash extend for entry 0
    pv_hash_extend(0x1f);
    kv_poll_valid(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);

    //Write junk to test lock
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_12) {
        *reg_ptr++ = 0x01234567;
    }
    //Extend hash
    VPRINTF(MEDIUM,"KV: Writing SHA Block with known answer\n");
    offset = 0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_24) {
        *reg_ptr++ = msg[offset++];
    }
    //Add padding to extended value
    VPRINTF(MEDIUM,"KV: Padding extended hash value\n");
    *reg_ptr++ = 0x80000000;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_31) {
        *reg_ptr++ = 0x00000000;
    }
    //Add length to last dword
    *reg_ptr = 0x00000300;

    //run the sha function
    VPRINTF(MEDIUM,"KV: polling for sha ready\n");
    sha512_poll_ready();
    sha_init_last(SHA512_384_MODE);
    VPRINTF(MEDIUM,"KV: polling for sha valid\n");
    sha512_poll_valid();
    VPRINTF(MEDIUM,"KV: polling for kv valid\n");
    kv_poll_valid(CLP_SHA512_REG_SHA512_KV_WR_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_KV_WR_STATUS);

    //check expected output from PCR31
    reg_ptr = (uint32_t*) CLP_PV_REG_PCR_ENTRY_31_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_PV_REG_PCR_ENTRY_31_11) {
        read_data = *reg_ptr++;
        if (exp1[offset] != read_data) {
            VPRINTF(FATAL,"SHA Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp1[offset], read_data);
            SEND_STDOUT_CTRL( 0x01);
        }
        offset++;
    }

    //read 384 bits from PCR31 and write to SHA512 BLOCK
    VPRINTF(MEDIUM,"KV: polling for kv ready\n");
    kv_poll_ready(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
    pv_hash_extend(0x1f);
    VPRINTF(MEDIUM,"KV: polling for kv valid\n");
    kv_poll_valid(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);

    //Write junk to test lock
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_12) {
        *reg_ptr++ = 0x01234567;
    }
    //Extend hash
    VPRINTF(MEDIUM,"KV: Writing SHA Block with known answer\n");
    offset = 0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_24) {
        *reg_ptr++ = msg[offset++];
    }
    //Add padding to extended value
    VPRINTF(MEDIUM,"KV: Padding extended hash value\n");
    *reg_ptr++ = 0x80000000;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_31) {
        *reg_ptr++ = 0x00000000;
    }
    //Add length to last dword
    *reg_ptr = 0x00000300;

    VPRINTF(MEDIUM,"KV: polling for sha ready\n");
    sha512_poll_ready();
    sha_init_last(SHA512_384_MODE);
    VPRINTF(MEDIUM,"KV: polling for sha valid\n");
    sha512_poll_valid();
    VPRINTF(MEDIUM,"KV: polling for kv valid\n");
    kv_poll_valid(CLP_SHA512_REG_SHA512_KV_WR_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_KV_WR_STATUS);

    //check expected output from PCR31
    reg_ptr = (uint32_t*) CLP_PV_REG_PCR_ENTRY_31_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_PV_REG_PCR_ENTRY_31_11) {
        read_data = *reg_ptr++;
        if (exp2[offset] != read_data) {
            VPRINTF(FATAL,"SHA Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp2[offset], read_data);
            SEND_STDOUT_CTRL( 0x01);
        }
        offset++;
    }

    //check endianness of result
    //Write first msg to block
    offset = 0;
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_12) {
        *reg_ptr++ = msg[offset++];
    }
    //Extend hash
    VPRINTF(MEDIUM,"KV: Writing SHA Block with known answer\n");
    offset = 0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_24) {
        *reg_ptr++ = msg[offset++];
    }
    //Add padding to extended value
    VPRINTF(MEDIUM,"KV: Padding extended hash value\n");
    *reg_ptr++ = 0x80000000;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_31) {
        *reg_ptr++ = 0x00000000;
    }
    //Add length to last dword
    *reg_ptr = 0x00000300;

    //run the sha function
    VPRINTF(MEDIUM,"KV: polling for sha ready\n");
    sha512_poll_ready();
    sha_init_last(SHA512_384_MODE);
    VPRINTF(MEDIUM,"KV: polling for sha valid\n");
    sha512_poll_valid();

    //check expected output from digest
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_DIGEST_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_DIGEST_11) {
        read_data = *reg_ptr++;
        if (exp1[offset] != read_data) {
            VPRINTF(FATAL,"SHA Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp1[offset], read_data);
            SEND_STDOUT_CTRL( 0x01);
        }
        offset++;
    }

    sha_poll_gen_hash_ready();
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_7) {
        *reg_ptr++ = nonce[offset++];
    }
    sha_gen_hash_start();
    sha_poll_gen_hash_valid();

    //check expected output from digest
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_15) {
        read_data = *reg_ptr++;
        if (exp3[offset] != read_data) {
            VPRINTF(FATAL,"SHA Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp3[offset], read_data);
            SEND_STDOUT_CTRL( 0x01);
        }
        offset++;
    }

    //inject seed to kv key reg (in RTL)
    printf("ECC: Inject PRIVKEY into KV slot 7\n");
    printf("MLDSA: Inject SEED into KV slot 8\n");
    printf("ECC/MLDSA: Inject PCR into msg_reg\n");
    printf("%c", 0x90);

    // VPRINTF(MEDIUM,"ECC: Running PCR Sign Function\n");
    // //run ECC signing on PCR
    // reg = ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK) |
    //       ((2 << ECC_REG_ECC_CTRL_CTRL_LOW) & ECC_REG_ECC_CTRL_CTRL_MASK) |
    //       ((0 << ECC_REG_ECC_CTRL_ZEROIZE_LOW) & ECC_REG_ECC_CTRL_ZEROIZE_MASK);
    // lsu_write_32(CLP_ECC_REG_ECC_CTRL,reg);

    // VPRINTF(MEDIUM,"ECC: Polling for PCR Sign to be complete\n");
    // // wait for ECC SIGNING process to be done
    // while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // //check expected output from sign r
    // reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_0;
    // offset = 0;
    // while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
    //     read_data = *reg_ptr++;
    //     if (exp_ecc_sign_r[offset] != read_data) {
    //         VPRINTF(FATAL,"ECC SIGN R Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp_ecc_sign_r[offset], read_data);
    //         SEND_STDOUT_CTRL( 0x01);
    //     }
    //     offset++;
    // }

    // //check expected output from sign s
    // reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0;
    // offset = 0;
    // while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
    //     read_data = *reg_ptr++;
    //     if (exp_ecc_sign_s[offset] != read_data) {
    //         VPRINTF(FATAL,"ECC SIGN S Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp_ecc_sign_s[offset], read_data);
    //         SEND_STDOUT_CTRL( 0x01);
    //     }
    //     offset++;
    // }

    VPRINTF(MEDIUM,"MLDSA: Running PCR Sign Function\n");
    //run MLDSA keygen+signing on PCR
    reg = ((1 << MLDSA_REG_MLDSA_CTRL_PCR_SIGN_LOW) & MLDSA_REG_MLDSA_CTRL_PCR_SIGN_MASK) |
          (MLDSA_CMD_KEYGEN_SIGN & MLDSA_REG_MLDSA_CTRL_CTRL_MASK) |
          ((0 << MLDSA_REG_MLDSA_CTRL_ZEROIZE_LOW) & MLDSA_REG_MLDSA_CTRL_ZEROIZE_MASK);
    lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL,reg);

    VPRINTF(MEDIUM,"MLDSA: Polling for PCR Sign to be complete\n");
    // wait for MLDSA KEYGEN+SIGNING process to be done
    while((lsu_read_32(CLP_MLDSA_REG_MLDSA_STATUS) & MLDSA_REG_MLDSA_STATUS_READY_MASK) == 0);

    //check expected output from signature
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_SIGNATURE_BASE_ADDR;
    offset = 0;
    uint32_t cnt = 0;
    while (offset < MLDSA87_SIGN_SIZE) {
        read_data = *reg_ptr;
        if (exp_mldsa_signature[offset] != read_data) {
            // VPRINTF(FATAL,"MLDSA SIGNATURE Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp_mldsa_signature[offset], read_data);
            VPRINTF(FATAL,"0x%x,\n", read_data);
            cnt++;
            if (cnt > 200){
                SEND_STDOUT_CTRL( 0x01);
            }
            
        }
        reg_ptr++;
        offset++;
    }

    VPRINTF(LOW,"----------------------------------\n");
    VPRINTF(LOW," KV PCR Hash Extend Test Complete!\n");
    VPRINTF(LOW,"----------------------------------\n");
    
    SEND_STDOUT_CTRL( 0xff);
}

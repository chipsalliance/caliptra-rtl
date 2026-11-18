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
#include "mlkem.h"

// Negative test: ML-KEM ENCAPS must not take its message from the key vault.
//
// A key vault slot is populated with a random value whose dest_valid has only bit 7
// set (the former MLKEM_MSG destination, now reserved). Firmware then supplies
// the encapsulation key and the message through the register API, and programs
// the offset that used to hold KV_MLKEM_MSG_RD_CTRL to request a key vault read
// of that slot. ENCAPS must still use the firmware message: the ciphertext and
// shared key must match the known-answer vector. If a key vault read were
// honored, the slot contents would replace the message and the ciphertext would
// no longer match.
//
// The reserved KV_WR_CTRL bit 13 (former mlkem_msg_dest_valid) must read as
// zero after firmware writes it, so no engine can grant the reserved
// destination. The DMA_DATA destination bit is written alongside it to show
// that the write was accepted.
//
// The former register offsets and bit positions are used directly because the
// register definitions no longer exist.

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
    .abr_error        = 0,
    .abr_notif        = 0,
    .axi_dma_notif    = 0,
    .axi_dma_error    = 0,
};

#define KV_MSG_SLOT                 5u
#define KV_MSG_LAST_DWORD           7u
#define KV_DEST_VALID_RSVD0         0x80u
#define OLD_KV_MLKEM_MSG_RD_CTRL    (CLP_ABR_REG_BASE_ADDR + 0xC008u)
#define OLD_KV_MLKEM_MSG_RD_STATUS  (CLP_ABR_REG_BASE_ADDR + 0xC00Cu)
#define OLD_RD_CTRL_READ_EN         0x1u
#define OLD_RD_CTRL_READ_ENTRY_LOW  1u
#define OLD_RD_STATUS_POLL_COUNT    2000u
#define WR_CTRL_RSVD0_BIT           (1u << 13)
#define WR_CTRL_DMA_DATA_BIT        (1u << 14)

// seed_z = 99E3246884181F8E1DD44E0C7629093330221FD67D9B7D6E1510B2DBAD8762F7
// seed_d = 49AC8B99BB1E6A8EA818261F8BE68BDEAA52897E7EC6C40B530BC760AB77DCE3

uint32_t abr_entropy[ABR_ENTROPY_SIZE] = {
    0x3401CEFA, 0xE20A7376, 0x49073AC1, 0xA351E329,
    0x26DB9ED0, 0xDB6B1CFF, 0xAB0493DA, 0xAFB93DDD,
    0xD83EDEA2, 0x8A803D0D, 0x003B2633, 0xB9D0F1BF,
    0x3401CEFA, 0xE20A7376, 0x49073AC1, 0xA351E329
};

const uint32_t exp_encaps_key[] = {
    0xd48441a0, 0x2a537bbc, 0x4da5700f, 0xe6cd5777, 0x43685a17, 0x2bcb61b8, 0x000c83c4, 0xfc4c5512,
    0x208a2c5d, 0xd93caa27, 0x9b0e1367, 0x111b2496, 0x760c32c4, 0xa723cc49, 0x91e6af1b, 0x688ec0af,
    0x29f4ce0b, 0x18070007, 0x8dceeae4, 0x191482a2, 0x69c2e17b, 0x41b59cda, 0x97cea3e1, 0xc6f9adcf,
    0xfe808705, 0xfadb9367, 0x76a21882, 0x8d2b800b, 0x1a27aaa2, 0x23257738, 0xa73667a7, 0x309d1ba3,
    0xce21ad37, 0x72a411bb, 0xb12e79b8, 0x40b95875, 0xf28308e7, 0x682c5964, 0xb40b249b, 0xbf08543d,
    0xf4326444, 0xa5b9f412, 0xc25c86f6, 0xf43ca452, 0x9103320a, 0xd6915555, 0xd0fd6175, 0x6bab5353,
    0x083a9b01, 0xd55333a7, 0xab13611b, 0x971da52f, 0x25ee4856, 0x239af84a, 0x36a20405, 0x578265a4,
    0xbbdc0b74, 0xb08a70e1, 0x88c5c322, 0x3bdb10a4, 0x068a309c, 0x5bdf5b27, 0xa2d35948, 0x5e297a61,
    0x01f9221a, 0x16d0ba98, 0x34944a6f, 0x31b8c517, 0xc8b26c73, 0xdebf0a58, 0x86b51457, 0xa1c0eeab,
    0xc78ba075, 0x89a2c710, 0xc43ae95d, 0xf71b0638, 0x210d5d76, 0x678141cd, 0x1e9df8ca, 0xbc4834fc,
    0x9bd696bb, 0x820c013e, 0x6cab5cd1, 0x9d79c6ac, 0x9a663936, 0x33a6215b, 0x59f865c8, 0xc87b5b3b,
    0xb82b2600, 0xa624a937, 0x4f0e44c5, 0xb2413bc7, 0x91c39230, 0xeb6b4c2f, 0xc6b4c7b4, 0x37b00829,
    0x226c6675, 0xc8f90d22, 0x44e32388, 0x328330c7, 0x798b5c34, 0xc0e8345d, 0x5a1ff251, 0xb614c221,
    0x87354198, 0x05c3b109, 0xc3c22cb3, 0xcce96a80, 0xff9f81d3, 0x52fe0745, 0x71c2bf0f, 0xbe23bc99,
    0x2a2d9b6b, 0x797571c1, 0x799276ac, 0xc6aaa7e2, 0x471a378a, 0xbe7d3aba, 0xe1146f01, 0x363327a7,
    0xcda5c463, 0x36880f1a, 0x495c7bcf, 0x5c4851ac, 0xc94503a6, 0x8868e090, 0x73030072, 0xb8c52213,
    0x07695ecd, 0x7f15a1fd, 0xfcd38f46, 0x7581fa20, 0x295cc9ee, 0xa82b261a, 0x0899bec5, 0x30894172,
    0xd8392385, 0x7fb3198a, 0xe8cfa3ef, 0x24c27521, 0x14a47c40, 0x9237ebba, 0x832d4d3b, 0x54e14a13,
    0xb4a990e4, 0xb063055a, 0x333c956c, 0x210a4501, 0x617ca076, 0x47e3744a, 0x9f50488e, 0x94ae609a,
    0x78bc8e5a, 0x901d1215, 0x70e0b0a3, 0xcf96a091, 0x257bc502, 0x2681a5bc, 0x9c620cad, 0xeda766e1,
    0x2132b3b4, 0x2bf7d3a0, 0xec62d585, 0x0a7d8b69, 0x80733d91, 0x875c1c6f, 0x03c08eb3, 0x3d3a30cb,
    0x354b1bc5, 0x82676a35, 0xa8da6e6d, 0x983bb9fe, 0x1c2d3b49, 0xa676b611, 0xa10695ad, 0xa813aeaa,
    0x8dc0c724, 0x4d2c6c1c, 0xc74296ba, 0xc8f6a76e, 0xa2644b26, 0xa7a9cc3c, 0xbffc3546, 0x1b0fe003,
    0x14b22257, 0x79906737, 0x0a4f2c3b, 0x07c4b513, 0x8e21b460, 0xdc94251d, 0xd9700ab3, 0x5d2a78c1,
    0xfa7605d3, 0xc8bf4441, 0x81da6e41, 0x7264fc18, 0x95976af5, 0xb03bf386, 0x1b0ffb70, 0x48bc100b,
    0x1be0eb97, 0xd49338ca, 0x25db6ae1, 0x17743a09, 0x838c70d0, 0xe22263a2, 0x0930632e, 0x2b15301e,
    0x7c5923f8, 0xcff4cc04, 0x781533c7, 0x26273af4, 0x2828b4cc, 0x63c8909a, 0x80d19d25, 0x2b14ffc5,
    0x71c741ef, 0x07be9470, 0xb1a26d85, 0x7167fa40, 0x6a356709, 0xc8fb7da4, 0x72b455d2, 0x436db82a,
    0x600a7e9b, 0x2d1d2590, 0xf2d51e4c, 0x0768be0b, 0x0ba965bf, 0x01ecb27c, 0x8002af02, 0x7dacc99d,
    0x69bc3a0a, 0xbc6583c1, 0x5f1859ff, 0x87689933, 0x90856174, 0xae91016c, 0x137e40d4, 0x9b454694,
    0x22689ce2, 0x35447671, 0x63ab243d, 0x9c6a1539, 0xf0094942, 0xb75b02a9, 0x9b772047, 0xd8163fe4,
    0x66c68c1c, 0xd81097e9, 0xccb58bc6, 0x14f3124e, 0x51a525e9, 0x90c59cf0, 0x81f8a103, 0xbb54c203,
    0xf3758d97, 0x0e54d394, 0xcd71e731, 0xec396ea3, 0x582ba654, 0x824d6632, 0xe6f1721a, 0x7fa2bbaf,
    0x265b2984, 0x4998c494, 0xc82b818e, 0xe58f37e9, 0x89c5ce41, 0x2906251b, 0x1272cb01, 0x61c4cde3,
    0xce5bec79, 0xb9c00bc1, 0x50e01d31, 0x87062974, 0x92536afd, 0x28541667, 0xccc8d94c, 0xeb80ba3e,
    0xb52e663b, 0x1651b73e, 0xeb1f4a70, 0x63052d5c, 0x68285338, 0xb84ef2dd, 0x56b82a99, 0x0c499e5d,
    0x0448f1ad, 0x90aa0d36, 0x61ab8e71, 0x6507ab6b, 0xb48739d3, 0x9965fb7e, 0x353256c5, 0xe64b1ee6,
    0x5579e970, 0x972d29ab, 0x3089cb32, 0x2dc88a94, 0x72ac30f2, 0x67237a29, 0xc1946b9d, 0x4859137f,
    0xdcfe5432, 0x9f81052f, 0x449a060d, 0xfce3783b, 0x71f43e6c, 0xfca3054b, 0xa6bb1ca8, 0x06a74202,
    0xd885d80c, 0xbb8199f3, 0x232b0918, 0xd99fa5da, 0x68888357, 0xa0bb098a, 0x9a80bc79, 0x603a8454,
    0x10235e38, 0x02cccbbb, 0xfa3dce13, 0x7fb433ab, 0xbc05639d, 0x7810c695, 0xc485c513, 0x30bf57b6,
    0xb1332854, 0x73f54949, 0xd52a61c0, 0x69aeba24, 0x77120c59, 0x65286cb8, 0xb366bf71, 0x386af4cf,
    0x0699c058, 0x4adf94a7, 0xb0d4e906, 0x103fe4a2, 0x6c6c2af7, 0x6e64e547, 0x719b792c, 0xf0d23ec3,
    0x9345eb1e, 0xe2a4b78e, 0x538c90e2, 0x0d548a55, 0xfa690335, 0x69619c18, 0x1d98f743, 0x02cf1876,
    0xbca2b0a5, 0x57e822c4, 0x7178a4d1, 0x29083d25, 0x9b171c3c, 0x7043c0cd, 0x18741069, 0x98db5f20,
    0x8c3b6256, 0xc994b6a6, 0x174b086c, 0xdfb63bf1, 0xbbcfb212, 0xc3e0b0c2, 0xfcd0004b, 0xb2cfaed0,
    0x98f62479, 0xe27b744e, 0xa8839da0, 0xa8904566, 0x49317307, 0x727d4f1a, 0x3ef24308, 0xa86f2c65,
    0xb48d3040, 0xaa370302, 0x036779d3, 0x23b59f4a, 0x03a77cb6, 0x9e2df030, 0x841e0ca2, 0x57578ecb,
    0x6b89e1c9, 0x41145860, 0xa58a61ed, 0x6ca56db2, 0xc4735a0a, 0x5e75fddc, 0xc84f0b61, 0x214ef81f
};

const uint32_t exp_ciphertext[] = {
    0x19e49f8b, 0xb05f0c25, 0x81813c46, 0xc7cef7fc, 0x736b1377, 0xba5e018e, 0xa47a0631, 0xbb78c3a8,
    0xb82101ac, 0xaef11482, 0xf3e466b8, 0x9970273c, 0xf74b9be0, 0xa3dd1ce2, 0xc1325b0b, 0x60960e8b,
    0xd80106c3, 0x7ac0ae5d, 0x3e344baf, 0xa56f51c5, 0x0863dd01, 0xb99f998b, 0xcac614a4, 0xc0063859,
    0x75c7d48c, 0xf0f09b13, 0xd77636bf, 0x6ed5ed73, 0x83136a61, 0xe35f5f0d, 0xbc5d515e, 0xad3ae484,
    0x7ed56701, 0x30dea960, 0x3fcd6a88, 0xca06207f, 0x077a6ac2, 0xeddbdab4, 0x307fedfb, 0x6a386457,
    0x5b6d72ad, 0x374af12b, 0x488bad6b, 0x91846896, 0x4eb33f73, 0x0ba1de6e, 0x85445efd, 0x696ecb41,
    0xf17dd8e3, 0xffa7af90, 0x75775762, 0x44eaacba, 0xa228614a, 0x1d250002, 0xdc59a78f, 0xa9a6fd60,
    0xe4ff0c73, 0xebe77f99, 0x4a64d1cd, 0x9052d5e2, 0xdd4c07a4, 0x183ce52c, 0x36c32bd2, 0x2787e671,
    0xfea2b5a9, 0xa814b1af, 0xa5965d04, 0x00e28169, 0x376196a0, 0x5a628759, 0xde3e23cc, 0xdef17a81,
    0x7c1ca2ea, 0x3e427743, 0x9bafc573, 0x9da458ff, 0x07fddae6, 0xbdbae3a3, 0xbb621f89, 0x56181da4,
    0x2c50bcb8, 0x15e16ec8, 0x318459a3, 0xb04ab5e2, 0x3ccceac5, 0x9030a0e6, 0xd51f5c92, 0x05b051a2,
    0x963a7676, 0xa2a79439, 0xbf2ee13e, 0xf994b9c1, 0x1744613c, 0x88ef0b8f, 0x7ce75c24, 0x51f62ed3,
    0x90606a82, 0x581a56af, 0xa5c2de64, 0x1f6f841d, 0x4b8bf848, 0x238cf555, 0x7bf6e073, 0x23dc95dc,
    0x46853ea4, 0x237b2a23, 0x22f5494e, 0xbd633a6a, 0x4072edbc, 0xdbc281fc, 0x26ebaa68, 0x23fda271,
    0x88bf9719, 0x7f3ac639, 0x725ef141, 0x421d8242, 0x0fbc0be8, 0x359efa43, 0x5eb2e83d, 0x42c2ffd8,
    0x6a2c51eb, 0x9a916052, 0x11a189ae, 0xcc2b5376, 0x20a562c7, 0x4eec7aa3, 0x81aa0972, 0x4adde0ce,
    0x472c93dd, 0xbe0081eb, 0xee1daa98, 0x8169eaa9, 0xd9cead15, 0x36c5a650, 0x32eb9ad1, 0x528cea5c,
    0x28a2c045, 0x90fb3315, 0xbec29d80, 0xbe7e5690, 0xfe29e26a, 0xa24db409, 0xea852518, 0x9a8a4d69,
    0x24bc3eb3, 0xbd094eb4, 0xb4340f51, 0xb41f0e14, 0x41f96211, 0x06912d5f, 0x0aa0cea0, 0x2009ed26,
    0x5b4e1f02, 0xbfdab3cf, 0xb2da5058, 0x9d882e2b, 0xe0fb1196, 0x97890c6d, 0x5f5eeb08, 0xe0bb2fad,
    0xe0bdc0d5, 0x60e7f880, 0x7d03faed, 0xf077da55, 0xbf9195f3, 0x900c055b, 0xb738a55f, 0x8a238e22,
    0x40f30d29, 0xd6cb8d77, 0xb1a340be, 0xb25f45dd, 0x76e1db7a, 0x29ccf6ae, 0x0b57ea5b, 0xa11b22dc,
    0xb1e30240, 0x23efb013, 0xc9fb5274, 0x2ec4aef1, 0xf1332b0d, 0x0adb3298, 0xebca7161, 0xadee300b,
    0x04b7543a, 0xd4c761b7, 0x6a8feaaf, 0x661515fc, 0xc481a066, 0x042eeb3a, 0x8aefecfe, 0x9b04a4ab,
    0x0b128bd7, 0xa686ba9a, 0xcfa04203, 0xc4116480, 0x4b6cc273, 0x330e54e1, 0xcb8b3812, 0xa73b52c8,
    0x28ea403f, 0x744256d5, 0x7a1d66f3, 0xe8f1a0ca, 0xcf8df2d0, 0x2913506b, 0x57683e96, 0xe8aab2fd,
    0xd6d9a773, 0xf62148c1, 0x50aab6c0, 0x759044ac, 0x252a6fcd, 0x95055a6c, 0x595aab9d, 0x8f8ecc12,
    0x94599f8b, 0x6acefc1b, 0x4aa7cb28, 0x1f2b3820, 0x052d38d3, 0xbcd54765, 0xe6aaf45e, 0x38f0962f,
    0xf9a495c5, 0x79aed601, 0x2978890f, 0x3accd12a, 0x710b801e, 0x45e8bba5, 0x55666433, 0xbd2f75e3,
    0x7bb9026b, 0xd2754e20, 0xf9c2348a, 0x8c8efb90, 0xe6e61cd3, 0x677efa83, 0x7e3603da, 0x62dc478d,
    0xba0f066f, 0x0025042d, 0x612aac4c, 0xe3d282d9, 0x620850d8, 0x02db454b, 0xa21bf52c, 0x74e9b565,
    0x72932a71, 0xeac0caee, 0xc52f2b27, 0xd3d0be6e, 0x1b520521, 0xfea8c4a2, 0xe48c670c, 0xc70259e4,
    0x0b519dba, 0x5f2b7bd4, 0x32d71d93, 0xb4e97df2, 0x39aad42f, 0x2865c7ea, 0xee65993a, 0x8ed8c097,
    0xf7a6ef23, 0x672c2418, 0xbf870b77, 0x8c853288, 0x52fc131d, 0x34bd7008, 0xfbc6b9f2, 0x8b521afd,
    0x4c814f74, 0xe8f4f493, 0x6f310871, 0xe006abe2, 0xa7de9222, 0xfbfef6fc, 0xa75abf17, 0x9b4a6a37,
    0xbf497cdb, 0xe0b19e70, 0x14ef605d, 0x52a785cd, 0xca7bb939, 0xc13c6a9a, 0x97288fb2, 0x3124619d,
    0xce1aacba, 0x7762efe5, 0xb7514d6b, 0xdf630feb, 0x09607750, 0x90ca2372, 0x2de0163e, 0xbfca7feb,
    0xae6dc2be, 0xccd40edc, 0xdc6b7255, 0x5177d131, 0x353cef12, 0x8c92dfd1, 0x0d83b76e, 0x0c57a68c,
    0x8e34ceb5, 0xe8dd263f, 0x5b0ef264, 0x269eb9e7, 0x9d0ebc4e, 0xe4c6e98d, 0xfb3cfeb7, 0x3c8373e6,
    0x08b3e8f7, 0x2c062915, 0x7c5c81b6, 0x2b826607, 0x6be5313b, 0xfe73fca1, 0x5d4bed3d, 0xe2fc5b43,
    0x1d7c99f2, 0x93e29c4b, 0x61d40d22, 0x84e03b10, 0x630712bf, 0x698a6672, 0xc1696783, 0x2ec3d8f6,
    0xe7c27b2c, 0xc81467d6, 0x293a7914, 0xd90dc970, 0x894cf14d, 0x5bd30dc6, 0x7847a152, 0x50e737e1,
    0x3aac83ce, 0xcb7f66ab, 0xb738badc, 0x6b1c6dfa, 0x959db9f7, 0x6d177870, 0x9fa07997, 0xbc5fb784,
    0x9e76112a, 0xb03255f6, 0x9a4cca9a, 0xa1b46637, 0x947f71fc, 0xb8b88f64, 0x543e36d9, 0x1c20c4f1,
    0xb1185c07, 0xb898e0ea, 0x95089835, 0xc09ded85, 0xd1e2966b, 0x38c76dc9, 0xc2bb6e08, 0xb693316c,
    0xfce13941, 0xa122fb1d, 0x6e509378, 0x9257b3f7, 0x1900ebb4, 0x6e689366, 0xceb3deb5, 0x16dd36b4,
    0x0f2ad9d2, 0x8a461fd3, 0x402066f8, 0xfa7b25f5, 0x1c99140f, 0x9909560d, 0x1775f7ee, 0x5a95148d,
    0xd71d09df, 0xdc1fac97, 0x057677ec, 0xf1c07152, 0x0b2d5630, 0xb149670a, 0xb90ddd59, 0x1a2769ac,
    0x3bb819c7, 0xb3e83c68, 0x4aac4223, 0xf8b057b2, 0xc88c3c08, 0xa4af3863, 0x84c986d3, 0xd03e418f
};

const uint32_t exp_shared_key[] = {
    0x578ff35c, 0x95aec48a, 0x74d5fefb, 0xf7ebd8b3, 0x07c91dcb, 0x7327224f, 0x776de360, 0x58c04753
};

// msg = 59C5154C04AE43AAFF32700F081700389D54BEC4C37C088B1C53F66212B12C72
const uint32_t fw_msg[MLKEM_MSG_SIZE] = {
    0x4C15C559, 0xAA43AE04, 0x0F7032FF, 0x38001708, 0xC4BE549D, 0x8B087CC3, 0x62F6531C, 0x722CB112
};

static uint32_t check_wr_ctrl_rsvd0(uint32_t addr) {
    uint32_t data;

    lsu_write_32(addr, WR_CTRL_RSVD0_BIT | WR_CTRL_DMA_DATA_BIT);
    data = lsu_read_32(addr);
    lsu_write_32(addr, 0);
    if (data != WR_CTRL_DMA_DATA_BIT) {
        VPRINTF(ERROR, "KV_WR_CTRL at 0x%x reads 0x%x, expected 0x%x\n", addr, data, WR_CTRL_DMA_DATA_BIT);
        return 1;
    }
    return 0;
}

void main() {
    uint32_t errors = 0;
    uint32_t data;
    uint32_t status_seen = 0;
    uint32_t mismatches;

    VPRINTF(LOW, "----------------------------------------------\n");
    VPRINTF(LOW, " ML-KEM ENCAPS ignores key vault message read\n");
    VPRINTF(LOW, "----------------------------------------------\n");

    init_interrupts();

    errors += check_wr_ctrl_rsvd0(CLP_HMAC_REG_HMAC512_KV_WR_CTRL);

    // Random 256-bit value in a slot whose only destination is the reserved bit 7
    lsu_write_32(STDOUT, 0xa2u | (KV_MSG_SLOT << 8) | (KV_MSG_LAST_DWORD << 13) | (KV_DEST_VALID_RSVD0 << 17));
    for (volatile int i = 0; i < 32; i++) __asm__ volatile("nop");

    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    errors += check_wr_ctrl_rsvd0(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL);

    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_ENCAPS_KEY_BASE_ADDR, (uint32_t*) exp_encaps_key, MLKEM_EK_SIZE);
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_MSG_BASE_ADDR, (uint32_t*) fw_msg, MLKEM_MSG_SIZE);
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, abr_entropy, ABR_ENTROPY_SIZE);

    // Request a key vault message read through the former control offset
    lsu_write_32(OLD_KV_MLKEM_MSG_RD_CTRL, OLD_RD_CTRL_READ_EN | (KV_MSG_SLOT << OLD_RD_CTRL_READ_ENTRY_LOW));

    data = lsu_read_32(OLD_KV_MLKEM_MSG_RD_CTRL);
    if (data != 0) {
        VPRINTF(ERROR, "Former KV_MLKEM_MSG_RD_CTRL offset reads 0x%x, expected 0\n", data);
        errors++;
    }
    for (uint32_t i = 0; i < OLD_RD_STATUS_POLL_COUNT; i++) {
        status_seen |= lsu_read_32(OLD_KV_MLKEM_MSG_RD_STATUS);
    }
    if (status_seen != 0) {
        VPRINTF(ERROR, "Former KV_MLKEM_MSG_RD_STATUS offset reported 0x%x, expected 0\n", status_seen);
        errors++;
    }

    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_ENCAPS);
    wait_for_mlkem_intr();
    if (cptra_intr_rcv.abr_error != 0) {
        VPRINTF(ERROR, "Unexpected ABR error interrupt during ENCAPS\n");
        errors++;
    }

    mismatches = 0;
    for (uint32_t i = 0; i < MLKEM_CIPHERTEXT_SIZE; i++) {
        data = lsu_read_32(CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR + 4 * i);
        if (data != exp_ciphertext[i]) {
            if (mismatches < 4) {
                VPRINTF(ERROR, "Ciphertext[%d] = 0x%x, expected 0x%x\n", i, data, exp_ciphertext[i]);
            }
            mismatches++;
        }
    }
    if (mismatches != 0) {
        VPRINTF(ERROR, "Ciphertext mismatches: %d of %d dwords\n", mismatches, MLKEM_CIPHERTEXT_SIZE);
        errors++;
    }

    mismatches = 0;
    for (uint32_t i = 0; i < MLKEM_SHAREDKEY_SIZE; i++) {
        data = lsu_read_32(CLP_ABR_REG_MLKEM_SHARED_KEY_0 + 4 * i);
        if (data != exp_shared_key[i]) {
            VPRINTF(ERROR, "Shared key[%d] = 0x%x, expected 0x%x\n", i, data, exp_shared_key[i]);
            mismatches++;
        }
    }
    if (mismatches != 0) {
        errors++;
    }

    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    if (errors != 0) {
        VPRINTF(FATAL, "%d check(s) failed\n", errors);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "Reserved dest bit reads zero; ENCAPS used the firmware message and matches KAT\n");
    SEND_STDOUT_CTRL(0xff);
}

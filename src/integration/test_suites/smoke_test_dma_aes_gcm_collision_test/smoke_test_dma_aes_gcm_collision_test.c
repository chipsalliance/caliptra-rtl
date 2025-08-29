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
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "soc_ifc.h"
#include "aes.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t  fail      __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

enum tb_fifo_mode {
    RAND_DELAY_TOGGLE   = 0x8f // Toggle random delays on the axi_sub. Applies to both.
};



// Plaintext
// 7e35f75248c51b041841ac7be09aa140e531e290e36797a440cddb0fd43066a7f4002969492d416690970f967bb5d9f251ff87c4e38e17a487e4966e5878e8b41b3fd3da61349ecf17df38e45bde8f2015b3355f274d5e503af561d649a0a79407290afdd7af2a1cedb209ade52490610575e2917248a5ce01a374412caefaa92da90f14b245ba39d9fcfefeb7b8a14656eb4dff16c6fc82a04498b9166f65fe1e0c42837ff568f70fbce5611e4c5461e43607ad95d9ff64e23c373393a54846b663c1785ff0b77128a4f6bf9758ed00e0462d7289d49c4fc0b7823be75fb37e95df64d703db99e45d921813799246fe5366087d900e0f9ed84ae80e67b789325fd89b018af66b58168a4a8637a87afad37a232ea55d69cc29d40ca0028f10617fdb69c5f45b0a5d86ffef06cab63b4c43323ededa17ee6116207add152fe8088d9a4d85ab1ab168362968cb16416a5532f205322e388d446cc13df68af21ce3301bcd899a85799e0b3a637daf29331e7704d09a20a268e47b0647202b27f139ee3e810a975f771a953b3638da3c59570db5905e24ecf3b3f0b76104225332aa94453c46ec56d53bb458781eff67e4430e9f2129287e042054bc0571a63dfef46c741d6e3a2a0ede09d8a3e69253f7850a169486dafdea499ee2bdf81b000e789853ad9bda56a1c87238e0edf23a67b646ee0ac8e3cef131a44b84fce248dcea8beb275418c4b1556284984f649451d4bd44708bcd4c48397021434765fd0b36bdb706a003cc0aad821b415190a622ebb507dabde59ffa537d11c427214b49d8641605347e837b2993b004f0b4415d4cbd8f18c6295c440d138506a056f2610022a97ac3ce3b4a9d44165694f92f72aed655e3eb94c1ff34ae7be5e97db9411b7ed3cfdbab825ab8126428b217c43848f49ba79381a0d19880db958586f4d6e8ebf0ae9e083d3b6fd3a8583e89ec9880e4e467b3b2580a2e27ff19c5eae2b92aa23057d5eec694466b9ff64f839da070fdcf443a473f20d0baa9c856aabc0add201c0c3fd9000a92a9602d64b8c435371fe2eb6b1c64a7ec5fa28a37ebd4c7cf

// Ciphertext
// f5290487291760e64967921d65ebc5a707acc71f49b6a0b71b19498f7b543d7f648cabb48548f30818e88aa26491e4ef25637452da398bf9814e1b35cb572f4c7f90a88c81d9e3855f4ab6f9ad266fcfc92ddbebcc5bf75961827c001164be6160d29e75cddbb96fb8edd4d095135dcc85fb8b2e1c83a101af905fee39271efa91303ef556a1971a53123140b890ed191cba849df91206b7f752e8182f97eb87e2fd3917e7f3f3c05ea94611d8b029eaa9691eff3b83827512d02a96ef588f946e7fe46cf9f7bbd385d67d0f71d907457788f59fd1d7bab88a193f8d292cc9e420217133a01dd01d687f64da877e1cafb48a33038e8c921058263df12302bd7f22a24994512d63d7dfc6463a0f330c435da71ed05c1878adfab73e2e5e98d1d7cc2746cff06a72b4190d8d54ad6aefb5ffb71744b45bcbff6ec290a1bc9659e3c81184d73d49dcf335d2ce77719fed009c057a4e2a504d8d8f86a1cdacd653b11518d3679043d98608170cc625009b3205497d66627a34676679456633ee83fcab02579a42770768ef19c69425350044da5337aa4679fa88071e48e5068e3bde56319ca77ff2985a3d7d029b4a42e218a8877900ecaa27bb018ed0993a9f66167380886bd1f655d89e7ce9b2b2aaa3985509493c4d5d60c83cab17ed307d8b36e7333b15ddfac6bc0b388cb710f601015a9b6b1e7e9681ad864950faeed3a2c1433b3feb631f381163c5d71f41cfb7076ee3ebbb74534a79fae9455cbf6d03921a228e258cb035dfab1f6be234d4061634f0f15bd28ec5984b381d35098716519c71dbe4065bfcf5974204f1bc0f17122f49cfb65217873fefd9700bf551e668a8a7e798c3e3d3ecaa2fcd4626bf15aae5742922be2c2e1e11bbb1166998a2118a9eff61e03713a4ef322275980ddccde547b109dd3c0e9e13e416bec5f65e80e335d0b096dbc2caea1d157cd34b9df2ad4f8fec5323ba58feeaddca8f3e0548613e1ebd440443a9d235af244ad76bb74249fd064e16550a08e7264312afd0b3b5959990d21265cf563d7061b355475f680abcf307770ba697c20efd06330bf8

// Tag
// 8183ce840cd93b6cc6f2887c294a31e6
                                
void main(void) {
    // AES flow configuration
    aes_flow_t    aes_input     = {0};
    aes_op_e      op            = AES_ENC;
    aes_mode_e    mode          = AES_GCM;
    aes_key_len_e key_len;
    aes_endian_e  endian_mode;  // AES_LITTLE_ENDIAN or AES_BIG_ENDIAN

    // AES-256 test vectors
    static char key_str3[] = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    uint32_t   key[8];
    uint32_t   key_size;

    static char iv_str3[] = "cafebabefacedbaddecaf888";
    uint32_t   iv[4];
    uint32_t   iv_length;

    // uint32_t   plaintext[32];  // arbitrary length here
    uint32_t   plaintext_length;
    uint32_t   plaintext_long_len;

    // uint32_t   ciphertext[32];  // arbitrary length here
    uint32_t   ciphertext_length;

    static char aad_str3[] = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    uint32_t   aad[32];  // arbitrary length here
    uint32_t   aad_length;

    // String "596142b046c10e029d10b7d96a2d2607"
    static uint32_t tag[4]     = { 0xb0426159, 0x020ec146, 0xd9b7109d, 0x07262d6a };
    // String "8183ce840cd93b6cc6f2887c294a31e6"
    static uint32_t tag_long[4] = { 0x84ce8381, 0x6c3bd90c, 0x7c88f2c6, 0xe6314a29 };
    // uint32_t   tag[4];
    uint32_t   tag_length;
    // uint32_t   tag_long[4];
    uint32_t   tag_long_length;

    // d9313225d9313225d9313225d9313225
    static uint32_t plaintext[4] = { 0x253231d9, 0x253231d9, 0x253231d9, 0x253231d9};
    static uint32_t plaintext_long[192] = { 
        0x52f7357e, 0x041bc548, 0x7bac4118, 0x40a19ae0, 0x90e231e5, 0xa49767e3, 0x0fdbcd40, 0xa76630d4,
        0x692900f4, 0x66412d49, 0x960f9790, 0xf2d9b57b, 0xc487ff51, 0xa4178ee3, 0x6e96e487, 0xb4e87858,
        0xdad33f1b, 0xcf9e3461, 0xe438df17, 0x208fde5b, 0x5f35b315, 0x505e4d27, 0xd661f53a, 0x94a7a049,
        0xfd0a2907, 0x1c2aafd7, 0xad09b2ed, 0x619024e5, 0x91e27505, 0xcea54872, 0x4174a301, 0xa9faae2c,
        0x140fa92d, 0x39ba45b2, 0xfefefcd9, 0x46a1b8b7, 0xff4deb56, 0x82fcc616, 0xb99844a0, 0xfe656f16,
        0x83420c1e, 0xf768f57f, 0x61e5bc0f, 0x61544c1e, 0xad0736e4, 0x64ffd995, 0x33373ce2, 0x4648a593,
        0x78c163b6, 0x71b7f05f, 0xbff6a428, 0x00ed5897, 0x722d46e0, 0x4f9cd489, 0x3b82b7c0, 0x7eb35fe7,
        0xd764df95, 0xe499db03, 0x1318925d, 0xfe469279, 0x7d086653, 0x9e0f0e90, 0x0ee84ad8, 0x3289b767,
        0x019bd85f, 0x586bf68a, 0x864a8a16, 0xfa7aa837, 0x2e237ad3, 0xcc695da5, 0xa00cd429, 0x61108f02,
        0xc569db7f, 0x5d0a5bf4, 0x06efff86, 0x4c3bb6ca, 0xde3e3243, 0x61ee17da, 0xdd7a2016, 0x08e82f15,
        0x854d9a8d, 0x68b11aab, 0xcb682936, 0x556a4116, 0x3205f232, 0x448d382e, 0xf63dc16c, 0xe31cf28a,
        0x89cd1b30, 0x9e79859a, 0x7d633a0b, 0x1e3329af, 0x9ad00477, 0xe468a220, 0x2047067b, 0x39f1272b,
        0x0a813eee, 0x1a775f97, 0x38363b95, 0x57593cda, 0x5e90b50d, 0xb3f3ec24, 0x0461b7f0, 0xaa325322,
        0x463c4594, 0x3bd556ec, 0x1e7858b4, 0x43e467ff, 0x29219f0e, 0x20047e28, 0x7105bc54, 0xf4fe3da6,
        0x6e1d746c, 0xde0e2a3a, 0xe6a3d809, 0x85f75392, 0x8694160a, 0x49eafdda, 0xf8bde29e, 0x780e001b,
        0x9bad5398, 0xc8a156da, 0xede03872, 0xb6673af2, 0xc80aee46, 0x31f1cee3, 0xfc844ba4, 0xeadc48e2,
        0x5427eb8b, 0x55b1c418, 0x4f988462, 0xd4519464, 0x8b7044bd, 0x39484ccd, 0x47432170, 0x360bfd65,
        0xa006b7bd, 0xad0acc03, 0x51411b82, 0xeb22a690, 0xbdda07b5, 0x53fa9fe5, 0x27c4117d, 0xd8494b21,
        0x34051664, 0x297b837e, 0xf004b093, 0x4c5d41b4, 0xc6188fbd, 0x0d445c29, 0xa0068513, 0x0061f256,
        0xc37aa922, 0x9d4a3bce, 0x94561644, 0xae722ff9, 0xebe355d6, 0x34ffc194, 0xe9e57bae, 0x1b41b97d,
        0xdbcfd37e, 0xb85a82ab, 0xb2286412, 0x4838c417, 0x93a79bf4, 0x98d1a081, 0x8595db80, 0xe8d6f486,
        0x9eaef0eb, 0x6f3b3d08, 0x3e58a8d3, 0x8098ec89, 0xb367e4e4, 0x2e0a58b2, 0xc519ff27, 0x2ab9e2ea,
        0xd55730a2, 0x4694c6ee, 0x4ff69f6b, 0x70a09d83, 0x3a44cffd, 0xd0203f47, 0x56c8a9ba, 0xdd0abcaa,
        0x3f0c1c20, 0x920a00d9, 0x642d60a9, 0x3735c4b8, 0x6bebe21f, 0xeca7641c, 0x378aa25f, 0xcfc7d4eb
    };

    static uint32_t ciphertext[4] = { 0xf0c12d52, 0xc749e3b8, 0x430c1788, 0xc256405c };
    static uint32_t ciphertext_long[192] = {
        0x870429f5, 0xe6601729, 0x1d926749, 0xa7c5eb65, 0x1fc7ac07, 0xb7a0b649, 0x8f49191b, 0x7f3d547b,
        0xb4ab8c64, 0x08f34885, 0xa28ae818, 0xefe49164, 0x52746325, 0xf98b39da, 0x351b4e81, 0x4c2f57cb,
        0x8ca8907f, 0x85e3d981, 0xf9b64a5f, 0xcf6f26ad, 0xebdb2dc9, 0x59f75bcc, 0x007c8261, 0x61be6411,
        0x759ed260, 0x6fb9dbcd, 0xd0d4edb8, 0xcc5d1395, 0x2e8bfb85, 0x01a1831c, 0xee5f90af, 0xfa1e2739,
        0xf53e3091, 0x1a97a156, 0x40311253, 0x19ed90b8, 0x9d84ba1c, 0xb70612f9, 0x18e852f7, 0x87eb972f,
        0x1739fde2, 0xc0f3f3e7, 0x1146a95e, 0xea29b0d8, 0xff1e69a9, 0x7582833b, 0x962ad012, 0x948f58ef,
        0x6ce47f6e, 0xd3bbf7f9, 0x0f7dd685, 0x4507d971, 0x9ff58877, 0xb8bad7d1, 0x8d3f198a, 0xe4c92c29,
        0x33712120, 0x1dd01da0, 0xda647f68, 0xaf1c7e87, 0x03338ab4, 0x10928c8e, 0xf13d2658, 0x7fbd0223,
        0x9449a222, 0xd7632d51, 0x3a46c6df, 0x430c330f, 0xd01ea75d, 0xad78185c, 0x2e3eb7fa, 0xd7d1985e,
        0xcf4627cc, 0xb4726af0, 0x548d0d19, 0xb5ef6aad, 0x4417b7ff, 0xffcb5bb4, 0xa190c26e, 0xe35996bc,
        0xd78411c8, 0xf3dc493d, 0x77ced235, 0x00ed9f71, 0x4e7a059c, 0x8d4d502a, 0xcda1868f, 0xb153d6ac,
        0x67d31815, 0x86d94390, 0xc60c1708, 0x329b0025, 0x667d4905, 0x67347a62, 0x66457966, 0xfc83ee33,
        0x9a5702ab, 0x68077742, 0x94c619ef, 0x44003525, 0xaa3753da, 0x88fa7946, 0xe5481e07, 0xde3b8e06,
        0xa79c3156, 0x5a98f27f, 0x9b027d3d, 0x18e2424a, 0x007987a8, 0xbb27aaec, 0x99d08e01, 0x16669f3a,
        0x6b888073, 0xd855f6d1, 0xb2e97c9e, 0x98a3aab2, 0x3c490955, 0xc8605d4d, 0xed17ab3c, 0x368b7d30,
        0x153b33e7, 0xbcc6fadd, 0xb78c380b, 0x0101f610, 0x1e6b9b5a, 0xad81967e, 0xfa504986, 0xc1a2d3ee,
        0xeb3f3b43, 0x11381f63, 0x1fd7c563, 0x07b7cf41, 0xbbebe36e, 0x794a5374, 0x5c45e9fa, 0x92036dbf,
        0x258e221a, 0xdf35b08c, 0xe26b1fab, 0x1606d434, 0x5bf1f034, 0x98c58ed2, 0x351d384b, 0x51168709,
        0xe4db719c, 0xf5fc5b06, 0xf1044297, 0x12170fbc, 0xb6cf492f, 0x3f871752, 0x0b70d9ef, 0x68e651f5,
        0x98e7a7a8, 0xecd3e3c3, 0x46cd2faa, 0xaa15bf26, 0x222974e5, 0x1e2e2cbe, 0x16b1bb11, 0x11a29869,
        0x61ff9e8a, 0xa41337e0, 0x752232ef, 0xcddc0d98, 0x09b147e5, 0x9e0e3cdd, 0xbe16e413, 0x805ef6c5,
        0xb0d035e3, 0xcac2db96, 0x7c151dea, 0xf29d4bd3, 0xec8f4fad, 0x58ba2353, 0xcaddeafe, 0x48053e8f,
        0xbd1e3e61, 0xa9430444, 0x24af35d2, 0xb76bd74a, 0x06fd4942, 0x0a55164e, 0x4326e708, 0xb3d0af12,
        0x909995b5, 0xcf6512d2, 0x61703d56, 0x5f4755b3, 0xf3bc0a68, 0xa60b7707, 0xfd0ec297, 0xf80b3306
    };

    aes_key_t  aes_key = {0};

    // Set endianness mode
    endian_mode = AES_LITTLE_ENDIAN;

    VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA AES  !!\n----------------------------------\n");

    SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

    // read csr_read_mcause to check if we came from an interrupt
    // if so terminate the test
    uint32_t mcause = csr_read_mcause();
    if (mcause != 0) {
        VPRINTF(LOW, "NMI Detected: Came from interrupt! mcause=0x%08X\n", mcause);
        SEND_STDOUT_CTRL(0xFF);
        while(1);
    }

    // Convert hex strings to uint32 arrays
    hex_to_uint32_array(key_str3, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str3, iv, &iv_length);
    // hex_to_uint32_array(plaintext_str3, plaintext, &plaintext_length);
    // hex_to_uint32_array(ciphertext_str3, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str3, aad, &aad_length);
    // hex_to_uint32_array(tag_str3, tag, &tag_length);
    // hex_to_uint32_array(tag_long_str, tag_long, &tag_long_length);

    VPRINTF(LOW, "Tag address: 0x%08X\n", (uint32_t)tag);
    VPRINTF(LOW, "Tag: ");
    for (int i = 0; i < tag_length/4; i++) {
        VPRINTF(LOW, "%08X", tag[i]);
    }
    VPRINTF(LOW, "\n");

    // Setup AES key structure
    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    plaintext_length = 16;
    plaintext_long_len = 768; // 768 * 2 // = 1536 bytes

    // Configure AES input structure
    aes_input.key                        = aes_key;
    aes_input.text_len                   = plaintext_length;
    aes_input.plaintext                  = plaintext;
    aes_input.ciphertext                 = ciphertext;
    aes_input.aad_len                    = aad_length;
    aes_input.aad                        = aad;
    aes_input.tag                        = tag;
    aes_input.iv                         = iv;
    aes_input.data_src_mode              = AES_DATA_DMA;
    aes_input.dma_transfer_data.src_addr = AXI_SRAM_BASE_ADDR;
    aes_input.dma_transfer_data.dst_addr = AXI_SRAM_BASE_ADDR + (AXI_SRAM_SIZE_BYTES/2);

    // ===========================================================================
    // Sending image over to AXI SRAM for usage during DMA AES calculation
    // ===========================================================================
    // Use a FIXED transfer (only the final beat should be present at the target address)
    VPRINTF(LOW, "Sending image payload via AHB i/f to AXI SRAM\n");
    soc_ifc_axi_dma_send_ahb_payload(aes_input.dma_transfer_data.src_addr, 0, 
                                      aes_input.plaintext, aes_input.text_len, 0);

    // Execute AES flow
    aes_flow(op, mode, key_len, aes_input, endian_mode);
    
    // ===========================================================================
    // Running the long string test
    // ===========================================================================
    // Configure AES input structure
    aes_input.key                        = aes_key;
    aes_input.text_len                   = plaintext_long_len;
    aes_input.plaintext                  = plaintext_long;
    aes_input.ciphertext                 = ciphertext_long;
    aes_input.aad_len                    = aad_length;
    aes_input.aad                        = aad;
    aes_input.tag                        = tag_long;
    aes_input.iv                         = iv;
    aes_input.data_src_mode              = AES_DATA_DMA;
    aes_input.dma_transfer_data.src_addr = AXI_SRAM_BASE_ADDR;
    aes_input.dma_transfer_data.dst_addr = AXI_SRAM_BASE_ADDR + (AXI_SRAM_SIZE_BYTES/2);


    aes_input.aes_collision_err = TRUE;
    aes_input.aes_expect_err = TRUE;
    VPRINTF(LOW, "AES collision error injection enabled\n");

    // ===========================================================================
    // Sending image over to AXI SRAM for usage during DMA AES calculation
    // ===========================================================================
    // Use a FIXED transfer (only the final beat should be present at the target address)
    VPRINTF(LOW, "Sending image payload via AHB i/f to AXI SRAM\n");
    soc_ifc_axi_dma_send_ahb_payload(aes_input.dma_transfer_data.src_addr, 0, 
                                      aes_input.plaintext, aes_input.text_len, 0);

    
    // Execute AES flow
    VPRINTF(LOW, "Executing AES flow for long string test\n");
    aes_flow(op, mode, key_len, aes_input, endian_mode);
    VPRINTF(LOW, "AES flow complete\n");

    // Signal completion and wait
    SEND_STDOUT_CTRL(0xff);
    while(1);
}

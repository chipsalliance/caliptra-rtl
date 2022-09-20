// Separating these defines from 'defines.h' since that file is auto-generated
// when building the SweRV EL2 from the configuration script, and clobbers
// these manual additions.

#ifndef CALIPTRA_DEFINES_H
  #define CALIPTRA_DEFINES_H

#include "defines.h"


/* ---- Key Vault ---- */
#define KV_BASE_ADDR 0x10018000
#define KV_KEY_CTRL_ADDR 0x10018200
#define KV_PCR_CTRL_ADDR 0x10018220

#define KV_NUM_PCR                0x00000008
#define KV_NUM_DWORDS             0x00000010


/* ---- AES ---- */
#define AES_ADDR_NAME0            0x10000000
#define AES_ADDR_NAME1            0x10000004
#define AES_ADDR_VER0             0x10000008
#define AES_ADDR_VER1             0x1000000c
#define AES_ADDR_CNTRL            0x10000010
#define AES_ADDR_STATUS           0x10000018
#define AES_ADDR_KEY_START        0x10000040
#define AES_ADDR_KEY_END          0x1000005f
#define AES_ADDR_BLOCK_START      0x10000080
#define AES_ADDR_BLOCK_END        0x1000008f
#define AES_ADDR_RESULT_START     0x10000100
#define AES_ADDR_RESULT_END       0x1000010f
#define AES_ADDR_CONFIG           0x10000020
#define AES_ADDR_IV_START         0x10000110
#define AES_ADDR_IV_END           0x1000011f
#define AES_ADDR_KV_CTRL          0x10000200

#define AES_INIT                  0x0000000D
#define AES_NEXT                  0x0000000E
#define AES_VALID                 0x00000003


/* ---- HMAC ---- */
#define HMAC_ADDR_NAME            0x10010000
#define HMAC_ADDR_VER             0x10010008
#define HMAC_ADDR_CNTRL           0x10010010
#define HMAC_ADDR_STATUS          0x10010018
#define HMAC_ADDR_KEY_START       0x10010040
#define HMAC_ADDR_KEY_END         0x1001006c
#define HMAC_ADDR_BLOCK_START     0x10010080
#define HMAC_ADDR_BLOCK_END       0x100100fc
#define HMAC_ADDR_TAG_START       0x10010100
#define HMAC_ADDR_TAG_END         0x1001012c
#define HMAC_ADDR_KV_CTRL         0x10010200

#define HMAC_INIT                 0x0000000D
#define HMAC_NEXT                 0x0000000E
#define HMAC_VALID                0x00000003

#define HMAC_KEY_NUM_DWORDS       0x0000000C


/* ---- SHA512 ---- */
#define SHA512_ADDR_NAME            0x10020000
#define SHA512_ADDR_VER             0x10020008
#define SHA512_ADDR_CNTRL           0x10020010
#define SHA512_ADDR_STATUS          0x10020018
#define SHA512_ADDR_BLOCK_START     0x10020080
#define SHA512_ADDR_BLOCK_END       0x100200ff
#define SHA512_ADDR_DIGEST_START    0x10020100
#define SHA512_ADDR_DIGEST_END      0x1002013f

#define SHA512_INIT                 0x0000000D
#define SHA512_NEXT                 0x0000000E
#define SHA512_VALID                0x00000003


/* ---- Mailbox ---- */
#define STDOUT 0x3003001c
#define MBOX_CLEAR_SECRETS 0x30030020

#define MBOX_ADDR_BASE            0x30020000
#define MBOX_ADDR_LOCK            0x30020000
#define MBOX_ADDR_CMD             0x30020008
#define MBOX_ADDR_DLEN            0x3002000C
#define MBOX_ADDR_DATAIN          0x30020010
#define MBOX_ADDR_DATAOUT         0x30020014
#define MBOX_ADDR_EXECUTE         0x30020018

#define MBOX_DLEN_VAL             0x0000001C


#endif // CALIPTRA_DEFINES_H

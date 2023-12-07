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

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;
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
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
};

/* ECC test vector:
    MSG      = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504DB98843548C5F623EE115F73D4C62ABC06D303B5D90D9A175087290D
    PRIVKEY  = F274F69D163B0C9F1FC3EBF4292AD1C4EB3CEC1C5A7DDE6F80C14292934C2055E087748D0A169C772483ADEE5EE70E17
    PUBKEY_X = D79C6D972B34A1DFC916A7B6E0A99B6B5387B34DA2187607C1AD0A4D1A8C2E4172AB5FA5D9AB58FE45E43F56BBB66BA4
    PUBKEY_Y = 5A7363932B06B4F223BEF0B60A6390265112DBBD0AAE67FEF26B465BE935B48E451E68D16F1118F2B32B4C28608749ED
    SEED     = 8FA8541C82A392CA74F23ED1DBFD73541C5966391B97EA73D744B0E34B9DF59ED0158063E39C09A5A055371EDF7A5441
    NONCE    = 1B7EC5E548E8AAA92EC77097CA9551C9783CE682CA18FB1EDBD9F1E50BC382DB8AB39496C8EE423F8CA105CBBA7B6588
    Sign_R   = 871E6EA4DDC5432CDDAA60FD7F055472D3C4DD41A5BFB26709E88C311A97093599A7C8F55B3974C19E4F5A7BFC1DD2AC
    SIGN_S   = 3E5552DE6403350EE70AD74E4B854D2DC4126BBF9C153A5D7A07BD4B85D06E45F850920E898FB7D34F80796DAE29365C
    IV       = 3401CEFAE20A737649073AC1A351E32926DB9ED0DB6B1CFFAB0493DAAFB93DDDD83EDEA28A803D0D003B2633B9D0F1BF
*/

void main() {
    printf("----------------------------------------\n");
    printf(" Running ECC Smoke Test error_trigger !!\n");
    printf("----------------------------------------\n");

    uint32_t ecc_msg[] =           {0xC8F518D4,
                                    0xF3AA1BD4,
                                    0x6ED56C1C,
                                    0x3C9E16FB,
                                    0x800AF504,
                                    0xDB988435,
                                    0x48C5F623,
                                    0xEE115F73,
                                    0xD4C62ABC,
                                    0x06D303B5,
                                    0xD90D9A17,
                                    0x5087290D};
    
    uint32_t ecc_privkey[] =       {0xF274F69D,
                                    0x163B0C9F,
                                    0x1FC3EBF4,
                                    0x292AD1C4,
                                    0xEB3CEC1C,
                                    0x5A7DDE6F,
                                    0x80C14292,
                                    0x934C2055,
                                    0xE087748D,
                                    0x0A169C77,
                                    0x2483ADEE,
                                    0x5EE70E17};

    uint32_t ecc_pubkey_x[] =      {0xD79C6D97,
                                    0x2B34A1DF,
                                    0xC916A7B6,
                                    0xE0A99B6B,
                                    0x5387B34D,
                                    0xA2187607,
                                    0xC1AD0A4D,
                                    0x1A8C2E41,
                                    0x72AB5FA5,
                                    0xD9AB58FE,
                                    0x45E43F56,
                                    0xBBB66BA4};

    uint32_t ecc_pubkey_y[] =      {0x5A736393,
                                    0x2B06B4F2,
                                    0x23BEF0B6,
                                    0x0A639026,
                                    0x5112DBBD,
                                    0x0AAE67FE,
                                    0xF26B465B,
                                    0xE935B48E,
                                    0x451E68D1,
                                    0x6F1118F2,
                                    0xB32B4C28,
                                    0x608749ED};

    uint32_t ecc_seed[] =          {0x8FA8541C,
                                    0x82A392CA,
                                    0x74F23ED1,
                                    0xDBFD7354,
                                    0x1C596639,
                                    0x1B97EA73,
                                    0xD744B0E3,
                                    0x4B9DF59E,
                                    0xD0158063,
                                    0xE39C09A5,
                                    0xA055371E,
                                    0xDF7A5441};

    uint32_t ecc_nonce[] =         {0x1B7EC5E5,
                                    0x48E8AAA9,
                                    0x2EC77097,
                                    0xCA9551C9,
                                    0x783CE682,
                                    0xCA18FB1E,
                                    0xDBD9F1E5,
                                    0x0BC382DB,
                                    0x8AB39496,
                                    0xC8EE423F,
                                    0x8CA105CB,
                                    0xBA7B6588};

    uint32_t ecc_sign_r[] =        {0x871E6EA4,
                                    0xDDC5432C,
                                    0xDDAA60FD,
                                    0x7F055472,
                                    0xD3C4DD41,
                                    0xA5BFB267,
                                    0x09E88C31,
                                    0x1A970935,
                                    0x99A7C8F5,
                                    0x5B3974C1,
                                    0x9E4F5A7B,
                                    0xFC1DD2AC};

    uint32_t ecc_sign_s[] =        {0x3E5552DE,
                                    0x6403350E,
                                    0xE70AD74E,
                                    0x4B854D2D,
                                    0xC4126BBF,
                                    0x9C153A5D,
                                    0x7A07BD4B,
                                    0x85D06E45,
                                    0xF850920E,
                                    0x898FB7D3,
                                    0x4F80796D,
                                    0xAE29365C};

    
    uint32_t ecc_iv[] =            {0x3401CEFA,
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
                                    0xB9D0F1BF};

    uint32_t value_greater_q[]=    {0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xc7634d81,
                                    0xf4372ddf,
                                    0x5b1a0db2,  //0x581a0db2,
                                    0x48b0a77a,
                                    0xecec196a,
                                    0xccc52973};

    uint32_t value_greater_p[]=    {0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xffffffff,
                                    0xfffffffe,
                                    0xffffffff,
                                    0x0000c000,  //0x00000000
                                    0x00000000,
                                    0xffffffff};
    //Call interrupt init
    init_interrupts();

    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t privkey_inject_cmd;
   

    if(rst_count == 0) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST OUT OF RANGE PRIVEKEY ZERO\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) {
            *reg_ptr++ = 0;
        }

        // Enable ECC SIGNING core
        printf("\nECC SIGNING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING);
        
        // wait for ECC SIGNING process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC privkey_input_outofrange 0 error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }
    else if(rst_count == 1) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST OUT OF RANGE PRIVEKEY GREATER q\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) {
            *reg_ptr++ = value_greater_q[offset++];;
        }

        // Enable ECC SIGNING core
        printf("\nECC SIGNING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING);
        
        // wait for ECC SIGNING process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC privkey_input_outofrange 1 error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }  
    else if(rst_count == 2) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST OUT OF RANGE PUBKEY\n");
        // Program ECC PUBKEY_X
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
            *reg_ptr++ = value_greater_p[offset++];
        }

        // Program ECC PUBKEY_Y
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
            *reg_ptr++ = value_greater_p[offset++];
        }

        // Enable ECC VERIFYING core
        printf("\nECC VERIFYING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_VERIFYING);
        
        // wait for ECC SIGNING process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC pubkey_input_outofrange error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }  
    else if(rst_count == 3) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST INVALID PUBKEY\n");
        // Program ECC PUBKEY_X
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
            *reg_ptr++ = ecc_pubkey_y[offset++];
        }

        // Program ECC PUBKEY_Y
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
            *reg_ptr++ = ecc_pubkey_x[offset++];
        }

        // Program ECC SIGN_R
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
            *reg_ptr++ = ecc_sign_r[offset++];
        }

        // Program ECC SIGN_S
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
            *reg_ptr++ = ecc_sign_s[offset++];
        }

        // Enable ECC VERIFYING core
        printf("\nECC VERIFYING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_VERIFYING);
        
        // wait for ECC SIGNING process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC pubkey_input_invalid error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }   
    else if(rst_count == 4) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST INVALID OUTPUT SIGN_R\n");
        // Program ECC PRIVKEY
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) {
            *reg_ptr++ = ecc_privkey[offset++];
        }

        // Program ECC MSG
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_MSG_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_MSG_11) {
            *reg_ptr++ = ecc_msg[offset++];
        }

        // Program ECC IV
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        //Inject invalid zero sign_r
        printf("%c",0x98);

        // Enable ECC SIGNING core
        printf("\nECC SIGNING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING);
        
        // wait for ECC SIGNING process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC r_output_outofrange error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }   
    else if(rst_count == 5) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST OUT OF RANGE INPUT R/S\n");
        // Program ECC SIGN_R
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
            *reg_ptr++ = value_greater_q[offset++];
        }

        // Program ECC SIGN_S
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
            *reg_ptr++ = 0;
        }

        // Enable ECC VERIFYING core
        printf("\nECC VERIFYING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_VERIFYING);
        
        // wait for ECC SIGNING process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC r/s_input_outofrange error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }   
    else if(rst_count == 6) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST PCR WITH INVALID OUTPUT SIGN_R\n");
        
        // Program ECC IV
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        //Inject invalid zero sign_r
        printf("%c",0x98);

        //inject seed to kv key reg (in RTL)
        printf("Inject PRIVKEY into KV slot 7\n");
        privkey_inject_cmd = 0x88 + 0x7;
        printf("%c", privkey_inject_cmd);

        printf("Inject MSG into SHA512 digest\n");
        printf("%c", 0x90);

        // Enable ECC PCR SIGNING core
        printf("\nECC PCR SIGNING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | 
                ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
    
        
        // wait for ECC PCR SIGNING process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC PCR r_output_outofrange error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }  
    else if(rst_count == 7) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST PCR WITH INVALID INPUT COMMAND\n");
        
        // Program ECC IV
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        //inject seed to kv key reg (in RTL)
        printf("Inject PRIVKEY into KV slot 7\n");
        privkey_inject_cmd = 0x88 + 0x7;
        printf("%c", privkey_inject_cmd);

        printf("Inject MSG into SHA512 digest\n");
        printf("%c", 0x90);

        // Enable ECC PCR KEYGEN core
        printf("\nECC PCR KEYGEN\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN | 
                ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
    
        
        // wait for ECC KEYGEN process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC PCR invalid command error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }
    else if(rst_count == 8) {
        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        printf("\n TEST PCR WITH INVALID INPUT COMMAND\n");
        
        // Program ECC IV
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        //inject seed to kv key reg (in RTL)
        printf("Inject PRIVKEY into KV slot 7\n");
        privkey_inject_cmd = 0x88 + 0x7;
        printf("%c", privkey_inject_cmd);

        printf("Inject MSG into SHA512 digest\n");
        printf("%c", 0x90);

        // Enable ECC PCR VERIFYING core
        printf("\nECC PCR VERIFYING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_VERIFYING | 
                ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
    
        
        // wait for ECC VERIFYING process to be done
        wait_for_ecc_intr();
        if ((cptra_intr_rcv.ecc_error == 0)){
            printf("\nECC PCR invalid command error is not detected.\n");
            printf("%c", 0x1);
            while(1);
        }

        ecc_zeroize();
    }        
    
    printf("%c",0xff); //End the test
    
}



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
#include "caliptra_defines.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define SHA_LBLOCK      16
#define SHA512_CBLOCK   (SHA_LBLOCK * 8) // 128
# define SHA512_DIGEST_LENGTH    64
#define SHA_LONG64 uint64_t

# ifndef PULL64
#  define B(x,j)    (((SHA_LONG64)(*(((const unsigned char *)(&x))+j)))<<((7-j)*8))
#  define PULL64(x) (B(x,0)|B(x,1)|B(x,2)|B(x,3)|B(x,4)|B(x,5)|B(x,6)|B(x,7))
# endif

# ifndef ROTR
#  define ROTR(x,s)       (((x)>>s) | (x)<<(64-s))
# endif

# ifndef Sigma0
#  define Sigma0(x)       (ROTR((x),28) ^ ROTR((x),34) ^ ROTR((x),39))
# endif

# ifndef Sigma1
#  define Sigma1(x)       (ROTR((x),14) ^ ROTR((x),18) ^ ROTR((x),41))
# endif

# ifndef sigma0
#  define sigma0(x)       (ROTR((x),1)  ^ ROTR((x),8)  ^ ((x)>>7))
# endif

# ifndef sigma1
#  define sigma1(x)       (ROTR((x),19) ^ ROTR((x),61) ^ ((x)>>6))
# endif

# ifndef Ch
#  define Ch(x,y,z)       (((x) & (y)) ^ ((~(x)) & (z)))
# endif

# ifndef Maj
#  define Maj(x,y,z)      (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
# endif

# define U64(C)     C##ULL

static const SHA_LONG64 K512[80] = {
    U64(0x428a2f98d728ae22), U64(0x7137449123ef65cd),
    U64(0xb5c0fbcfec4d3b2f), U64(0xe9b5dba58189dbbc),
    U64(0x3956c25bf348b538), U64(0x59f111f1b605d019),
    U64(0x923f82a4af194f9b), U64(0xab1c5ed5da6d8118),
    U64(0xd807aa98a3030242), U64(0x12835b0145706fbe),
    U64(0x243185be4ee4b28c), U64(0x550c7dc3d5ffb4e2),
    U64(0x72be5d74f27b896f), U64(0x80deb1fe3b1696b1),
    U64(0x9bdc06a725c71235), U64(0xc19bf174cf692694),
    U64(0xe49b69c19ef14ad2), U64(0xefbe4786384f25e3),
    U64(0x0fc19dc68b8cd5b5), U64(0x240ca1cc77ac9c65),
    U64(0x2de92c6f592b0275), U64(0x4a7484aa6ea6e483),
    U64(0x5cb0a9dcbd41fbd4), U64(0x76f988da831153b5),
    U64(0x983e5152ee66dfab), U64(0xa831c66d2db43210),
    U64(0xb00327c898fb213f), U64(0xbf597fc7beef0ee4),
    U64(0xc6e00bf33da88fc2), U64(0xd5a79147930aa725),
    U64(0x06ca6351e003826f), U64(0x142929670a0e6e70),
    U64(0x27b70a8546d22ffc), U64(0x2e1b21385c26c926),
    U64(0x4d2c6dfc5ac42aed), U64(0x53380d139d95b3df),
    U64(0x650a73548baf63de), U64(0x766a0abb3c77b2a8),
    U64(0x81c2c92e47edaee6), U64(0x92722c851482353b),
    U64(0xa2bfe8a14cf10364), U64(0xa81a664bbc423001),
    U64(0xc24b8b70d0f89791), U64(0xc76c51a30654be30),
    U64(0xd192e819d6ef5218), U64(0xd69906245565a910),
    U64(0xf40e35855771202a), U64(0x106aa07032bbd1b8),
    U64(0x19a4c116b8d2d0c8), U64(0x1e376c085141ab53),
    U64(0x2748774cdf8eeb99), U64(0x34b0bcb5e19b48a8),
    U64(0x391c0cb3c5c95a63), U64(0x4ed8aa4ae3418acb),
    U64(0x5b9cca4f7763e373), U64(0x682e6ff3d6b2b8a3),
    U64(0x748f82ee5defb2fc), U64(0x78a5636f43172f60),
    U64(0x84c87814a1f0ab72), U64(0x8cc702081a6439ec),
    U64(0x90befffa23631e28), U64(0xa4506cebde82bde9),
    U64(0xbef9a3f7b2c67915), U64(0xc67178f2e372532b),
    U64(0xca273eceea26619c), U64(0xd186b8c721c0c207),
    U64(0xeada7dd6cde0eb1e), U64(0xf57d4f7fee6ed178),
    U64(0x06f067aa72176fba), U64(0x0a637dc5a2c898a6),
    U64(0x113f9804bef90dae), U64(0x1b710b35131c471b),
    U64(0x28db77f523047d84), U64(0x32caab7b40c72493),
    U64(0x3c9ebe0a15c9bebc), U64(0x431d67c49c100d4c),
    U64(0x4cc5d4becb3e42b6), U64(0x597f299cfc657e2a),
    U64(0x5fcb6fab3ad6faec), U64(0x6c44198c4a475817)
};

#  define ROUND_00_15(i,a,b,c,d,e,f,g,h)        do {    \
        T1 += h + Sigma1(e) + Ch(e,f,g) + K512[i];      \
        h = Sigma0(a) + Maj(a,b,c);                     \
        d += T1;        h += T1;                        } while (0)

#  define ROUND_16_80(i,j,a,b,c,d,e,f,g,h,X)    do {    \
        s0 = X[(j+1)&0x0f];     s0 = sigma0(s0);        \
        s1 = X[(j+14)&0x0f];    s1 = sigma1(s1);        \
        T1 = X[(j)&0x0f] += s0 + s1 + X[(j+9)&0x0f];    \
        ROUND_00_15(i+j,a,b,c,d,e,f,g,h);               } while (0)

typedef struct SHA512state_st {
    SHA_LONG64 h[8];
    SHA_LONG64 Nl, Nh;
    union {
        SHA_LONG64 d[SHA_LBLOCK];
        unsigned char p[SHA512_CBLOCK];
    } u;
    unsigned int num, md_len;
} SHA512_CTX;

volatile char*   const mbox_stdout  = (char*)   STDOUT;

void SHA512_Init(SHA512_CTX* c)
{
    c->h[0] = 0x6a09e667f3bcc908;
    c->h[1] = 0xbb67ae8584caa73b;
    c->h[2] = 0x3c6ef372fe94f82b;
    c->h[3] = 0xa54ff53a5f1d36f1;
    c->h[4] = 0x510e527fade682d1;
    c->h[5] = 0x9b05688c2b3e6c1f;
    c->h[6] = 0x1f83d9abfb41bd6b;
    c->h[7] = 0x5be0cd19137e2179;

    c->Nl = 0;
    c->Nh = 0;
    c->num = 0;
    c->md_len = SHA512_DIGEST_LENGTH;
    return;
}

static void sha512_block_data_order(SHA512_CTX* ctx, const void* in, size_t num)
{
    const SHA_LONG64 *W = (SHA_LONG64 *) in;
    SHA_LONG64 a, b, c, d, e, f, g, h, s0, s1, T1;
    SHA_LONG64 X[16];
    int i;

    const char* const print_str = "Inside sha512_block_data_order: num,i=\n";
    char unsigned hw_ii = 0;
    short  num_ii;
    char   num_digit;

    while (num--) {

        a = ctx->h[0];
        b = ctx->h[1];
        c = ctx->h[2];
        d = ctx->h[3];
        e = ctx->h[4];
        f = ctx->h[5];
        g = ctx->h[6];
        h = ctx->h[7];

        for (hw_ii = 0; print_str[hw_ii] != 0; hw_ii++) {
            *mbox_stdout = print_str[hw_ii];
        }
        // Poor man's sprintf (print the num,i line)
        for (num_ii = sizeof(size_t)*8-4; num_ii >= 0; num_ii-=4) {
            num_digit = (num >> num_ii) & 0xf;
            if (num_digit > 9) {
                num_digit += 0x37; // Convert to ASCII A-F
            } else {
                num_digit += 0x30; // Convert to ASCII 0-9
            }
            *mbox_stdout = num_digit; // Print starting with left-most digits
        };
        *mbox_stdout=',';
        *mbox_stdout='0';
        *mbox_stdout='\n';


        T1 = X[0] = PULL64(W[0]);
        ROUND_00_15(0, a, b, c, d, e, f, g, h);
        T1 = X[1] = PULL64(W[1]);
        ROUND_00_15(1, h, a, b, c, d, e, f, g);
        T1 = X[2] = PULL64(W[2]);
        ROUND_00_15(2, g, h, a, b, c, d, e, f);
        T1 = X[3] = PULL64(W[3]);
        ROUND_00_15(3, f, g, h, a, b, c, d, e);
        T1 = X[4] = PULL64(W[4]);
        ROUND_00_15(4, e, f, g, h, a, b, c, d);
        T1 = X[5] = PULL64(W[5]);
        ROUND_00_15(5, d, e, f, g, h, a, b, c);
        T1 = X[6] = PULL64(W[6]);
        ROUND_00_15(6, c, d, e, f, g, h, a, b);
        T1 = X[7] = PULL64(W[7]);
        ROUND_00_15(7, b, c, d, e, f, g, h, a);
        T1 = X[8] = PULL64(W[8]);
        ROUND_00_15(8, a, b, c, d, e, f, g, h);
        T1 = X[9] = PULL64(W[9]);
        ROUND_00_15(9, h, a, b, c, d, e, f, g);
        T1 = X[10] = PULL64(W[10]);
        ROUND_00_15(10, g, h, a, b, c, d, e, f);
        T1 = X[11] = PULL64(W[11]);
        ROUND_00_15(11, f, g, h, a, b, c, d, e);
        T1 = X[12] = PULL64(W[12]);
        ROUND_00_15(12, e, f, g, h, a, b, c, d);
        T1 = X[13] = PULL64(W[13]);
        ROUND_00_15(13, d, e, f, g, h, a, b, c);
        T1 = X[14] = PULL64(W[14]);
        ROUND_00_15(14, c, d, e, f, g, h, a, b);
        T1 = X[15] = PULL64(W[15]);
        ROUND_00_15(15, b, c, d, e, f, g, h, a);


        for (i = 16; i < 80; i += 16) {

            *mbox_stdout = 'i';
            *mbox_stdout = '=';
            // Poor man's sprintf (print the [i] line)
            for (num_ii = sizeof(size_t)*8-4; num_ii >= 0; num_ii-=4) {
                num_digit = (i >> num_ii) & 0xf;
                if (num_digit > 9) {
                    num_digit += 0x37; // Convert to ASCII A-F
                } else {
                    num_digit += 0x30; // Convert to ASCII 0-9
                }
                *mbox_stdout = num_digit; // Print starting with left-most digits
            }
            *mbox_stdout='\n';

            ROUND_16_80(i, 0, a, b, c, d, e, f, g, h, X);
            ROUND_16_80(i, 1, h, a, b, c, d, e, f, g, X);
            ROUND_16_80(i, 2, g, h, a, b, c, d, e, f, X);
            ROUND_16_80(i, 3, f, g, h, a, b, c, d, e, X);
            ROUND_16_80(i, 4, e, f, g, h, a, b, c, d, X);
            ROUND_16_80(i, 5, d, e, f, g, h, a, b, c, X);
            ROUND_16_80(i, 6, c, d, e, f, g, h, a, b, X);
            ROUND_16_80(i, 7, b, c, d, e, f, g, h, a, X);
            ROUND_16_80(i, 8, a, b, c, d, e, f, g, h, X);
            ROUND_16_80(i, 9, h, a, b, c, d, e, f, g, X);
            ROUND_16_80(i, 10, g, h, a, b, c, d, e, f, X);
            ROUND_16_80(i, 11, f, g, h, a, b, c, d, e, X);
            ROUND_16_80(i, 12, e, f, g, h, a, b, c, d, X);
            ROUND_16_80(i, 13, d, e, f, g, h, a, b, c, X);
            ROUND_16_80(i, 14, c, d, e, f, g, h, a, b, X);
            ROUND_16_80(i, 15, b, c, d, e, f, g, h, a, X);
        }

        ctx->h[0] += a;
        ctx->h[1] += b;
        ctx->h[2] += c;
        ctx->h[3] += d;
        ctx->h[4] += e;
        ctx->h[5] += f;
        ctx->h[6] += g;
        ctx->h[7] += h;

        W += SHA_LBLOCK;
    }
}

int SHA512_Update(SHA512_CTX *c, const void *_data, size_t len)
{
    SHA_LONG64 l;
    unsigned char *p = c->u.p;
    const unsigned char *data = (const unsigned char *)_data;

    // if (len == 0)
    //     return -1;

    l = (c->Nl + (((SHA_LONG64) len) << 3)) & U64(0xffffffffffffffff);
    if (l < c->Nl)
        c->Nh++;
    if (sizeof(len) >= 8)
        c->Nh += (((SHA_LONG64) len) >> 61);
    c->Nl = l;

    if (c->num != 0) {
        size_t n = sizeof(c->u) - c->num;

        if (len < n) {
            memcpy(p + c->num, data, len), c->num += (unsigned int)len;
            return 0;
        } else {
            memcpy(p + c->num, data, n), c->num = 0;
            len -= n, data += n;
            sha512_block_data_order(c, p, 1);
        }
    }

    if (len >= sizeof(c->u)) {
#ifndef SHA512_BLOCK_CAN_MANAGE_UNALIGNED_DATA
        if ((size_t)data % sizeof(c->u.d[0]) != 0)
            while (len >= sizeof(c->u))
                memcpy(p, data, sizeof(c->u)),
                sha512_block_data_order(c, p, 1),
                len -= sizeof(c->u), data += sizeof(c->u);
        else
#endif
            sha512_block_data_order(c, data, len / sizeof(c->u)),
            data += len, len %= sizeof(c->u), data -= len;
    }

    if (len != 0)
        memcpy(p, data, len), c->num = (int)len;

    return 0;
}

void SHA512_Final(unsigned char* md, SHA512_CTX* c)
{
    unsigned char* p = (unsigned char *)c->u.p;
    size_t n = c->num;

    p[n] = 0x80;                /* There always is a room for one */
    n++;
    if (n > (sizeof(c->u) - 16)) {
        memset(p + n, 0, sizeof(c->u) - n);
        n = 0;
        sha512_block_data_order(c, p, 1);
    }

    memset(p + n, 0, sizeof(c->u) - 16 - n);

    p[sizeof(c->u) - 1] = (unsigned char)(c->Nl);
    p[sizeof(c->u) - 2] = (unsigned char)(c->Nl >> 8);
    p[sizeof(c->u) - 3] = (unsigned char)(c->Nl >> 16);
    p[sizeof(c->u) - 4] = (unsigned char)(c->Nl >> 24);
    p[sizeof(c->u) - 5] = (unsigned char)(c->Nl >> 32);
    p[sizeof(c->u) - 6] = (unsigned char)(c->Nl >> 40);
    p[sizeof(c->u) - 7] = (unsigned char)(c->Nl >> 48);
    p[sizeof(c->u) - 8] = (unsigned char)(c->Nl >> 56);
    p[sizeof(c->u) - 9] = (unsigned char)(c->Nh);
    p[sizeof(c->u) - 10] = (unsigned char)(c->Nh >> 8);
    p[sizeof(c->u) - 11] = (unsigned char)(c->Nh >> 16);
    p[sizeof(c->u) - 12] = (unsigned char)(c->Nh >> 24);
    p[sizeof(c->u) - 13] = (unsigned char)(c->Nh >> 32);
    p[sizeof(c->u) - 14] = (unsigned char)(c->Nh >> 40);
    p[sizeof(c->u) - 15] = (unsigned char)(c->Nh >> 48);
    p[sizeof(c->u) - 16] = (unsigned char)(c->Nh >> 56);


    sha512_block_data_order(c, p, 1);

    switch (c->md_len) {

    case SHA512_DIGEST_LENGTH:
        for (n = 0; n < SHA512_DIGEST_LENGTH / 8; n++) {
            SHA_LONG64 t = c->h[n];

            *(md++) = (unsigned char)(t >> 56);
            *(md++) = (unsigned char)(t >> 48);
            *(md++) = (unsigned char)(t >> 40);
            *(md++) = (unsigned char)(t >> 32);
            *(md++) = (unsigned char)(t >> 24);
            *(md++) = (unsigned char)(t >> 16);
            *(md++) = (unsigned char)(t >> 8);
            *(md++) = (unsigned char)(t);
        }
        break;
        /* ... as well as make sure md_len is not abused. */
    default:
        return;
    }

    return;
}

unsigned long read_cycles(void) 
{
    unsigned long cycles;
    asm volatile("rdcycle %0": "=r"(cycles));
    return cycles;
}

#define DATA_SZE_128KB  (128 * 1024) // 128 KB
#define DATA_SIZE_12KB  (12 * 1024) // 12 KB
#define DATA_SIZE_8KB  (8 * 1024) // 8 KB
#define DATA_SIZE_4KB  (4 * 1024) // 4 KB
#define DATA_SIZE_1KB  (1 * 1024) // 1 KB
#define DATA_SIZE_256B  256 // 256 Bytes

void main()
{
    SHA512_CTX context;
    unsigned char md[SHA512_DIGEST_LENGTH] = {0};
    char unsigned hw_ii = 0;

    const char* const str_init   = "Enter SHA512_Init\n";
    const char* const str_update = "Enter SHA512_Update\n";
    const char* const str_final  = "Enter SHA512_Final\n";
    const char* const str_memcpy = "Enter memcpy\n";
    const char* const str_done   = "'Main' completed\n";

    while (str_init[hw_ii] != 0) {
        *mbox_stdout = str_init[hw_ii++];
    }
    hw_ii = 0;
    SHA512_Init(&context);
    while (str_update[hw_ii] != 0) {
        *mbox_stdout = str_update[hw_ii++];
    }
    hw_ii = 0;
    const unsigned int size = DATA_SIZE_8KB;
    //char* data = (char *) malloc(size);
    char data[size];
    //int result = 0;
    // double avgCycles = 0;
    // unsigned long cycle_start_read, cycle_end_read;
    // int iter;

#if 0
    result = SHA512_Update(&context, data, size);
    if (result != 0)
    {
        //printf("SHA512_Update failed, result: %d", result);
        goto Exit; 
    }

    for (iter = 0; iter < 1; iter++)
    {
        cycle_start_read = read_cycles();
        SHA512_Final(md, &context);
        cycle_end_read = read_cycles();

        avgCycles = avgCycles + (cycle_end_read - cycle_start_read);
    }
#endif

    SHA512_Update(&context, data, size);
    //cycle_start_read = read_cycles();
    while (str_final[hw_ii] != 0) {
        *mbox_stdout = str_final[hw_ii++];
    }
    hw_ii = 0;
    SHA512_Final(md, &context);
    //cycle_end_read = read_cycles();

    //avgCycles = avgCycles + (cycle_end_read - cycle_start_read);

    __uint32_t dummy = 0xDEADBEEF;

    char* DCCM = (char *)(0xf0040000);
    while (str_memcpy[hw_ii] != 0) {
        *mbox_stdout = str_memcpy[hw_ii++];
    }
    hw_ii = 0;
    memcpy(DCCM, &dummy, sizeof(dummy));

    //printf("Avg. cycle count for 128 KB SHA512 hash: %lf", avgCycles/1000);
    //char* ICCM = (char *)(0xee000000);
    //*((float *)(ICCM)) = avgCycles/1000;
    //memcpy(ICCM, &avgCycles, sizeof(avgCycles));



    //for (int idx = 0; idx < SHA512_DIGEST_LENGTH; idx++)
    //{
    //    printf("%02x", md[idx]);
    //}


Exit:
    return;
}

// Run program: Ctrl + F5 or Debug > Start Without Debugging menu
// Debug program: F5 or Debug > Start Debugging menu

// Tips for Getting Started: 
//   1. Use the Solution Explorer window to add/manage files
//   2. Use the Team Explorer window to connect to source control
//   3. Use the Output window to see build output and other messages
//   4. Use the Error List window to view errors
//   5. Go to Project > Add New Item to create new code files, or Project > Add Existing Item to add existing code files to the project
//   6. In the future, to open this project again, go to File > Open > Project and select the .sln file

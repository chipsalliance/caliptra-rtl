/*
 *  Example ECDSA program
 *
 *  Copyright The Mbed TLS Contributors
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  Licensed under the Apache License, Version 2.0 (the "License"); you may
 *  not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
//======================================================================
//
// ecdsa_secp384r1.c
// --------
// this file has dependencies to mbedtls libraries, and needs to be placed 
// in mbedtls/programs/pkey pkey directory of mbedtls to be run
//
//
//======================================================================

#include "mbedtls/build_info.h"

#include "mbedtls/platform.h"

#if defined(MBEDTLS_ECDSA_C) && \
    defined(MBEDTLS_ENTROPY_C) && defined(MBEDTLS_CTR_DRBG_C)
#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/ecdsa.h"
#include "mbedtls/sha512.h"
#include "mbedtls/hmac_drbg.h"

#include <string.h>
#endif

/*
 * Uncomment to show key and signature details
 */
#define VERBOSE
#define MBEDTLS_SHA384_C
/*
 * Uncomment to force use of a specific curve
 */
#define ECPARAMS    MBEDTLS_ECP_DP_SECP384R1  MBEDTLS_ECDSA_DETERMINISTIC

#if !defined(ECPARAMS)
#define ECPARAMS    mbedtls_ecp_curve_list()->grp_id
#endif

#if !defined(MBEDTLS_ECDSA_C) || !defined(MBEDTLS_SHA384_C) || \
    !defined(MBEDTLS_ENTROPY_C) || !defined(MBEDTLS_CTR_DRBG_C)
int main( void )
{
    mbedtls_printf("MBEDTLS_ECDSA_C and/or MBEDTLS_SHA384_C and/or "
           "MBEDTLS_ENTROPY_C and/or MBEDTLS_CTR_DRBG_C not defined\n");
    mbedtls_exit( 0 );
}
#else
#if defined(VERBOSE)
static void dump_buf( const char *title, unsigned char *buf, size_t len )
{
    size_t i;

    mbedtls_printf( "%s", title );
    for( i = 0; i < len; i++ )
        mbedtls_printf("%c%c", "0123456789ABCDEF" [buf[i] / 16],
                       "0123456789ABCDEF" [buf[i] % 16] );
    mbedtls_printf( "\n" );
    fflush( stdout );
}

static void print_1_uchar(FILE *stream, unsigned char uch) {
    fputc(uch,  stream);
}

static void print_1_array(FILE *stream, const void *buf, size_t len) {
    const unsigned char *s = buf;
    unsigned char uch;
    size_t i;
    //fputs(title,  stream);
    for(i = 0; i < len; i++ ) {
        uch = s[i];
        print_1_uchar(stream, "0123456789ABCDEF" [uch / 16]);
        print_1_uchar(stream, "0123456789ABCDEF" [uch % 16]);
    }
    print_1_uchar(stream,'\n');
    fflush( stdout );
}

static void dump_pubkey( FILE *stream, const char *title, mbedtls_ecdsa_context *key )
{
    unsigned char buf[300];
    size_t len;

    if( mbedtls_ecp_point_write_binary( &key->MBEDTLS_PRIVATE(grp), &key->MBEDTLS_PRIVATE(Q),
                MBEDTLS_ECP_PF_UNCOMPRESSED, &len, buf, sizeof buf ) != 0 )
    {
        mbedtls_printf("internal error\n");
        return;
    }

    //dump_buf( title, buf, len );
    size_t len_c = (len - 1)/2;
    print_1_array(stream, buf + 1, len_c); // "pubkey_x ", 
    print_1_array(stream, buf + 1+ len_c, len_c); //"pubkey_y ", 
}

static void dump_privkey( FILE *stream, const char *title, mbedtls_ecdsa_context *key )
{
    unsigned char buf[300];
    size_t len;

    mbedtls_ecp_group *grp = &key->MBEDTLS_PRIVATE(grp);

    len = mbedtls_mpi_size(  &grp->P );
    mbedtls_mpi_write_binary( &key->MBEDTLS_PRIVATE(d), buf , len );

    //dump_buf( title, buf, len );
    print_1_array(stream, buf, len); //"privkey ",
}

static int extract_sig(unsigned char *sig_r, unsigned char *sig_s, unsigned char *buf, size_t len, size_t len_c )
{
    memset( sig_r, 0, len_c );
    memset( sig_s, 0, len_c );

    size_t r_size = buf[3]; // removing prefix "306602" from r
    size_t s_size = buf[4+r_size+1]; // removing prefix "02" from r

    size_t r_sig_start = 0;
    size_t sig_r_start = 0;
    if (r_size < len_c)
        r_sig_start = len_c - r_size;
    else
        sig_r_start = r_size - len_c;
    
    size_t s_sig_start = 0;
    size_t sig_s_start = 0;
    if (s_size < len_c)
        s_sig_start = len_c - s_size;
    else
        sig_s_start = s_size - len_c;
    
    memcpy(sig_r + r_sig_start, buf + 4 + sig_r_start, r_size);
    memcpy(sig_s + s_sig_start, buf + 4 + r_size + 2 + sig_s_start, s_size);

    if ( (4 + r_size + 2 + s_size ) == len )
        return 0;
    else
        return -1;
}



/*

static void dump_hmacdrbg_seed( const char *title, mbedtls_ctr_drbg_context *ctx )
{
    unsigned char buf[300];
    size_t len;


    len = ctx->private_entropy_len;
    mbedtls_ctr_drbg_context *ctx = (mbedtls_ctr_drbg_context *) p_rng;
    mbedtls_mpi_write_binary( &ctx->private_p_entropy, buf , len );

    dump_buf( title, buf, len );
}
*/
#else
#define dump_buf( a, b, c )
#define dump_pubkey( a, b )
#endif


int main( int argc, char *argv[] )
{
    //mbedtls_printf("Caliptra testvector generator for ECDSA secp384r1");
    int ret = 1;
    int exit_code = MBEDTLS_EXIT_FAILURE;
    mbedtls_ecdsa_context ctx_sign, ctx_verify;
    mbedtls_entropy_context entropy;
    mbedtls_ctr_drbg_context ctr_drbg;
    unsigned char message[48];
    size_t message_len = sizeof(message);
    unsigned char hash[48];
    unsigned char sig[MBEDTLS_ECDSA_MAX_LEN];
    unsigned char sig_r[MBEDTLS_ECDSA_MAX_LEN] = {0x00};
    unsigned char sig_s[MBEDTLS_ECDSA_MAX_LEN];
    size_t sig_len;
    const char *pers = "ecdsa";
    ((void) argv);
    mbedtls_mpi random_message;
    unsigned char IV[48];
    mbedtls_mpi random_IV;
    size_t IV_len = sizeof(IV);
    
    mbedtls_mpi random_seed;
    mbedtls_mpi random_nonce;
    const mbedtls_md_info_t *md_info;
    unsigned char seed_buf[48];
    size_t seed_buf_len  = sizeof(seed_buf);
    unsigned char nonce_buf[48];
    size_t nonce_buf_len  = sizeof(nonce_buf);
    mbedtls_hmac_drbg_context rng_ctx;
    mbedtls_hmac_drbg_context *p_rng = &rng_ctx;

    mbedtls_ecdsa_init( &ctx_sign );
    mbedtls_ecdsa_init( &ctx_verify );
    mbedtls_ctr_drbg_init( &ctr_drbg );
    

    memset( sig, 0, sizeof( sig ) );
    
    if( argc != 1 )
    {
        mbedtls_printf( "usage: ecdsa\n" );

#if defined(_WIN32)
        mbedtls_printf( "\n" );
#endif

        goto exit;
    }

    /*
     * Generate two files for storing the test vectors
     */
    FILE *fptr;
    fptr = fopen("secp384_testvector.hex", "w");

    if (fptr == NULL) {
        printf("Failed to create the file.\n");
    }

    FILE *fptr_all;
    fptr_all = fopen("secp384_testvector_all.hex", "a");
  
    if (fptr_all == NULL) {
        printf("Failed to create the all file.\n");
    }


    /*
     * Seeding the random number generator
     */
    fflush( stdout );
    mbedtls_entropy_init( &entropy );
    if( ( ret = mbedtls_ctr_drbg_seed( &ctr_drbg, mbedtls_entropy_func, &entropy,
                               (const unsigned char *) pers,
                               strlen( pers ) ) ) != 0 )
    {
        mbedtls_printf( " failed\n  ! mbedtls_ctr_drbg_seed returned %d\n", ret );
        goto exit;
    }

    ret = mbedtls_ecp_group_load( &ctx_sign.private_grp, ECPARAMS );
    if( ret != 0 )
        return( ret );

    const mbedtls_ecp_group *grp =  &ctx_sign.private_grp;
    
    /*
     * Generate a random seed
     */
    mbedtls_mpi_init( &random_seed);
    ret = mbedtls_mpi_random( &random_seed, 1, &grp->N, mbedtls_ctr_drbg_random, &ctr_drbg );
    if( ret != 0 )
        return( ret );
    mbedtls_mpi_write_binary( &random_seed, seed_buf , seed_buf_len );
    //dump_buf( "  + Seed: ", seed_buf, seed_buf_len );
    
    /*
     * Generate a random nonce
     */
    mbedtls_mpi_init( &random_nonce);
    ret = mbedtls_mpi_random( &random_nonce, 1, &grp->N, mbedtls_ctr_drbg_random, &ctr_drbg );
    if( ret != 0 )
        return( ret );
    mbedtls_mpi_write_binary( &random_nonce, nonce_buf , nonce_buf_len );
    //dump_buf( "  + Nonce: ", nonce_buf, nonce_buf_len );


    /*
     * Generate a key pair for signing
     */
    mbedtls_hmac_drbg_init( &rng_ctx );
    if( ( md_info = mbedtls_md_info_from_type( MBEDTLS_MD_SHA384 ) ) == NULL )
        return( MBEDTLS_ERR_ECP_BAD_INPUT_DATA );

    unsigned char data[2 * MBEDTLS_ECP_MAX_BYTES];
    size_t grp_len = ( grp->nbits + 7 ) / 8;
    mbedtls_mpi_write_binary( &random_seed, data, seed_buf_len );
    mbedtls_mpi_write_binary( &random_nonce, data + seed_buf_len, nonce_buf_len );
    ret = mbedtls_hmac_drbg_seed_buf(p_rng, md_info, data, seed_buf_len + nonce_buf_len);
    if (ret != 0) {
        mbedtls_printf("Failed to seed HMAC DRBG\n");
        goto exit;
    }

    if( ( ret = mbedtls_ecdsa_genkey( &ctx_sign, ECPARAMS,
                              mbedtls_hmac_drbg_random, p_rng ) ) != 0 )
    {
        mbedtls_printf( " failed\n  ! mbedtls_ecdsa_genkey returned %d\n", ret );
        goto exit;
    }

    //mbedtls_printf( " ok (key size: %d bits)\n", (int) ctx_sign.MBEDTLS_PRIVATE(grp).pbits );
    

    /*
     * Generate a random message
     */
    mbedtls_mpi_init( &random_message);
    ret = mbedtls_mpi_random( &random_message, 1, &grp->N, mbedtls_ctr_drbg_random, &ctr_drbg );
    if( ret != 0 )
        return( ret );
    mbedtls_mpi_write_binary( &random_message, message , message_len );

    /*
     * Compute message hash
     */

    if( ( ret = mbedtls_sha512( message, sizeof( message ), hash, 1 ) ) != 0 )
    {
        mbedtls_printf( " failed\n  ! mbedtls_sha384 returned %d\n", ret );
        goto exit;
    }
    //mbedtls_printf( " ok\n" );
    //dump_buf( "  + message: ", message, sizeof( message ) );
    //dump_buf( "  + Hash: ", hash, sizeof( hash ) );



    /*
     * Sign message hash
     */

    if( ( ret = mbedtls_ecdsa_write_signature( &ctx_sign, MBEDTLS_MD_SHA384,
                                       hash, sizeof( hash ),
                                       sig, sizeof( sig ), &sig_len,
                                       mbedtls_ctr_drbg_random, &ctr_drbg ) ) != 0 )
    {
        mbedtls_printf( " failed\n  ! mbedtls_ecdsa_write_signature returned %d\n", ret );
        goto exit;
    }

    size_t len_c;
    len_c = (int) ctx_sign.MBEDTLS_PRIVATE(grp).pbits / 8;

    if( ( ret = extract_sig(sig_r, sig_s, sig, sig_len, len_c) ) != 0 )
    {
        mbedtls_printf( " failed\n  ! extract_sig returned %d\n", ret );
        goto exit;
    }
    

    /*
     * Generate a random IV
     */
    mbedtls_mpi_init( &random_IV);
    ret = mbedtls_mpi_random( &random_IV, 1, &grp->N, mbedtls_ctr_drbg_random, &ctr_drbg );
    if( ret != 0 )
        return( ret );
    mbedtls_mpi_write_binary( &random_IV, IV , IV_len );

    /*
     * Transfer public information to verifying context
     *
     * We could use the same context for verification and signatures, but we
     * chose to use a new one in order to make it clear that the verifying
     * context only needs the public key (Q), and not the private key (d).
     */
    //mbedtls_printf( "  . Preparing verification context..." );
    fflush( stdout );

    if( ( ret = mbedtls_ecp_group_copy( &ctx_verify.MBEDTLS_PRIVATE(grp), &ctx_sign.MBEDTLS_PRIVATE(grp) ) ) != 0 )
    {
        mbedtls_printf( " failed\n  ! mbedtls_ecp_group_copy returned %d\n", ret );
        goto exit;
    }

    if( ( ret = mbedtls_ecp_copy( &ctx_verify.MBEDTLS_PRIVATE(Q), &ctx_sign.MBEDTLS_PRIVATE(Q) ) ) != 0 )
    {
        mbedtls_printf( " failed\n  ! mbedtls_ecp_copy returned %d\n", ret );
        goto exit;
    }

    /*
     * Verify signature
     */
    //mbedtls_printf( " ok\n  . Verifying signature..." );
    fflush( stdout );

    if( ( ret = mbedtls_ecdsa_read_signature( &ctx_verify,
                                      hash, sizeof( hash ),
                                      sig, sig_len ) ) != 0 )
    {
        mbedtls_printf( " failed\n  ! mbedtls_ecdsa_read_signature returned %d\n", ret );
        goto exit;
    }

    //mbedtls_printf( " ok\n" );

    /*
     * store the hashed_msg, private key, public key, seed, nonce to files
     */

    //"hashed_msg " 
    print_1_array(fptr, hash, sizeof( hash )); //"msg ", 
    print_1_array(fptr_all, hash, sizeof( hash )); //"msg ", 
    //"private key "
    dump_privkey(fptr, "  + Private key:  ", &ctx_sign );
    dump_privkey(fptr_all, "  + Private key:  ", &ctx_sign );
    //"public key "
    dump_pubkey(fptr, "  + Public key:  ", &ctx_sign );
    dump_pubkey(fptr_all, "  + Public key:  ", &ctx_sign );
    //"seed "
    print_1_array(fptr, seed_buf, seed_buf_len);
    print_1_array(fptr_all, seed_buf, seed_buf_len);
    //"nonce "
    print_1_array(fptr, nonce_buf, nonce_buf_len); 
    print_1_array(fptr_all, nonce_buf, nonce_buf_len);
    //"sign r"
    print_1_array(fptr, sig_r, len_c); 
    print_1_array(fptr_all, sig_r, len_c);
    //"sign s"
    print_1_array(fptr, sig_s, len_c); 
    print_1_array(fptr_all, sig_s, len_c); //"sign s" ,
    //"IV "
    print_1_array(fptr, IV, IV_len);
    print_1_array(fptr_all, IV, IV_len);

    print_1_uchar(fptr_all,'\n'); 


    exit_code = MBEDTLS_EXIT_SUCCESS;

exit:

    mbedtls_ecdsa_free( &ctx_verify );
    mbedtls_ecdsa_free( &ctx_sign );
    mbedtls_ctr_drbg_free( &ctr_drbg );
    mbedtls_entropy_free( &entropy );

    mbedtls_exit( exit_code );
}
#endif /* MBEDTLS_ECDSA_C && MBEDTLS_ENTROPY_C && MBEDTLS_CTR_DRBG_C &&
          ECPARAMS */

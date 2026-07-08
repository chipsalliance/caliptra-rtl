//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This file contains defines and typedefs to be compiled for use in
// the simulation running on the emulator when using Veloce.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
                                                                               

typedef enum bit[1:0] {ecc_reset_test = 2'b00, ecc_normal_test = 2'b01, ecc_otf_reset_test = 2'b10} ecc_in_test_transactions;
typedef enum bit[1:0] {key_gen = 2'b00, key_sign = 2'b01, key_verify = 2'b10, ecdh_sharedkey = 2'b11 } ecc_in_op_transactions;

// pragma uvmf custom additional begin
// Curve axis: P-384 (default) and P-256. Matches ECC_CTRL.CURVE_SEL field.
typedef enum bit {ecc_curve_p384 = 1'b0, ecc_curve_p256 = 1'b1} ecc_in_curve_e;

// Error-injection axis. ERR_NONE => legal transaction; all other values
// drive one of the 5 new error gates in ecc_dsa_ctrl.sv (curve/rand_k/kv).
typedef enum bit [2:0] {
    ERR_NONE          = 3'd0,
    ERR_PCR_P256      = 3'd1,  // PCR_SIGN + CURVE_SEL=P256
    ERR_RAND_K_PCR    = 3'd2,  // PCR_SIGN + RAND_K_EN
    ERR_RAND_K_KEYGEN = 3'd3,  // RAND_K_EN + KEYGEN
    ERR_RAND_K_VERIFY = 3'd4,  // RAND_K_EN + VERIFY
    ERR_RAND_K_SHARED = 3'd5,  // RAND_K_EN + SHARED_KEY
    ERR_KV_P256       = 3'd6,  // KV path + CURVE_SEL=P256
    ERR_KV_RAND_K     = 3'd7   // KV path + RAND_K_EN
} ecc_in_err_mode_e;
// pragma uvmf custom additional end


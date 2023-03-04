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
typedef enum bit[1:0] {key_gen = 2'b00, key_sign = 2'b01, key_verify = 2'b10 } ecc_in_op_transactions;

// pragma uvmf custom additional begin
// pragma uvmf custom additional end


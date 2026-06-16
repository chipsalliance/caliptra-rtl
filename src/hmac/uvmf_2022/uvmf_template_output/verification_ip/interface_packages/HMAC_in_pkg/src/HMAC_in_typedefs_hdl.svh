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
                                                                               

typedef enum bit [2:0] {reset_op = 3'b000, hmac384_op = 3'b001, hmac512_op = 3'b010, otf_reset_op = 3'b011, last_alone_op = 3'b100} hmac_in_op_transactions;

// pragma uvmf custom additional begin
// pragma uvmf custom additional end


// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle state encoding definition.
//
// DO NOT EDIT THIS FILE DIRECTLY.
// It has been generated with
// $ ./util/design/gen-lc-state-enc.py --seed 10167336684108184581
//
package lc_ctrl_state_pkg;

  import caliptra_prim_util_pkg::vbits;

  ///////////////////////////////
  // General size declarations //
  ///////////////////////////////

  parameter int LcValueWidth = 16;

  parameter int NumLcStateValues = 20;
  parameter int LcStateWidth = NumLcStateValues * LcValueWidth;
  parameter int NumLcStates = 21;
  parameter int DecLcStateWidth = vbits(NumLcStates);
  // Redundant version used in the CSRs.
  parameter int DecLcStateNumRep = 32/DecLcStateWidth;
  parameter int ExtDecLcStateWidth = DecLcStateNumRep*DecLcStateWidth;

  parameter int NumLcCountValues = 24;
  parameter int LcCountWidth = NumLcCountValues * LcValueWidth;
  parameter int NumLcCountStates = 25;
  parameter int DecLcCountWidth = vbits(NumLcCountStates);

  // This state is not stored in OTP, but inferred from the locked
  // status of the secret partitions. Hence, only the decoded ID state
  // is declared here for exposure through the CSR interface.
  parameter int NumLcIdStates = 2;
  parameter int DecLcIdStateWidth = vbits(NumLcIdStates+1);
  // Redundant version used in the CSRs.
  parameter int DecLcIdStateNumRep = 32/DecLcIdStateWidth;
  parameter int ExtDecLcIdStateWidth = DecLcIdStateNumRep*DecLcIdStateWidth;

  /////////////////////////////////////////////
  // Life cycle manufacturing state encoding //
  /////////////////////////////////////////////

  // These values have been generated such that they are incrementally writeable with respect
  // to the ECC polynomial specified. The values are used to define the life cycle manufacturing
  // state and transition counter encoding in lc_ctrl_pkg.sv.
  //
  // The values are unique and have the following statistics (considering all 16
  // data and 6 ECC bits):
  //
  // - Minimum Hamming weight: 8
  // - Maximum Hamming weight: 16
  // - Minimum Hamming distance from any other value: 6
  // - Maximum Hamming distance from any other value: 20
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: --
  //  6: ||| (5.85%)
  //  7: --
  //  8: ||||||||||| (17.40%)
  //  9: --
  // 10: |||||||||||||||||||| (29.60%)
  // 11: --
  // 12: ||||||||||||||||||| (29.21%)
  // 13: --
  // 14: ||||||||| (13.51%)
  // 15: --
  // 16: || (4.02%)
  // 17: --
  // 18:  (0.37%)
  // 19: --
  // 20:  (0.05%)
  // 21: --
  // 22: --
  //
  //
  // Note that the ECC bits are not defined in this package as they will be calculated by
  // the OTP ECC logic at runtime.

  // SEC_CM: MANUF.STATE.SPARSE
  // The A/B values are used for the encoded LC state.
  parameter logic [15:0] A0 = 16'b1000011000111000; // ECC: 6'b110000
  parameter logic [15:0] B0 = 16'b1110011001111001; // ECC: 6'b111111

  parameter logic [15:0] A1 = 16'b1100011000100110; // ECC: 6'b101001
  parameter logic [15:0] B1 = 16'b1101111101101110; // ECC: 6'b101011

  parameter logic [15:0] A2 = 16'b0010000111101100; // ECC: 6'b110010
  parameter logic [15:0] B2 = 16'b0111011111101101; // ECC: 6'b110110

  parameter logic [15:0] A3 = 16'b0001100111101000; // ECC: 6'b000100
  parameter logic [15:0] B3 = 16'b1101101111101100; // ECC: 6'b001101

  parameter logic [15:0] A4 = 16'b1001011001100100; // ECC: 6'b000001
  parameter logic [15:0] B4 = 16'b1101111001110100; // ECC: 6'b101101

  parameter logic [15:0] A5 = 16'b0001011000010110; // ECC: 6'b111001
  parameter logic [15:0] B5 = 16'b1011011001110111; // ECC: 6'b111101

  parameter logic [15:0] A6 = 16'b0101001001010010; // ECC: 6'b001111
  parameter logic [15:0] B6 = 16'b1101111111110010; // ECC: 6'b001111

  parameter logic [15:0] A7 = 16'b0010001001011111; // ECC: 6'b011000
  parameter logic [15:0] B7 = 16'b0011101011111111; // ECC: 6'b011101

  parameter logic [15:0] A8 = 16'b0000001110111001; // ECC: 6'b001000
  parameter logic [15:0] B8 = 16'b1100001110111111; // ECC: 6'b101010

  parameter logic [15:0] A9 = 16'b1100100101111000; // ECC: 6'b010010
  parameter logic [15:0] B9 = 16'b1111101101111001; // ECC: 6'b011110

  parameter logic [15:0] A10 = 16'b0010000110110111; // ECC: 6'b010001
  parameter logic [15:0] B10 = 16'b1011010111111111; // ECC: 6'b010101

  parameter logic [15:0] A11 = 16'b1011000100000111; // ECC: 6'b011001
  parameter logic [15:0] B11 = 16'b1111110110000111; // ECC: 6'b011111

  parameter logic [15:0] A12 = 16'b0011100000010000; // ECC: 6'b111001
  parameter logic [15:0] B12 = 16'b1111100100110000; // ECC: 6'b111111

  parameter logic [15:0] A13 = 16'b0011000010101011; // ECC: 6'b100110
  parameter logic [15:0] B13 = 16'b1011010011111011; // ECC: 6'b111110

  parameter logic [15:0] A14 = 16'b0011110100100000; // ECC: 6'b011000
  parameter logic [15:0] B14 = 16'b0011111101101011; // ECC: 6'b011100

  parameter logic [15:0] A15 = 16'b1010101100010010; // ECC: 6'b111000
  parameter logic [15:0] B15 = 16'b1111111110011010; // ECC: 6'b111010

  parameter logic [15:0] A16 = 16'b0100011010010100; // ECC: 6'b110110
  parameter logic [15:0] B16 = 16'b0101111110010111; // ECC: 6'b111110

  parameter logic [15:0] A17 = 16'b1011111110000101; // ECC: 6'b000000
  parameter logic [15:0] B17 = 16'b1011111111010111; // ECC: 6'b000111

  parameter logic [15:0] A18 = 16'b1110010000010111; // ECC: 6'b010100
  parameter logic [15:0] B18 = 16'b1111110010111111; // ECC: 6'b010110

  parameter logic [15:0] A19 = 16'b0100100101011010; // ECC: 6'b001000
  parameter logic [15:0] B19 = 16'b1110100111111111; // ECC: 6'b001101


  // SEC_CM: TRANSITION.CTR.SPARSE
  // The C/D values are used for the encoded LC transition counter.
  parameter logic [15:0] C0 = 16'b0000110000011011; // ECC: 6'b110110
  parameter logic [15:0] D0 = 16'b0011111000011111; // ECC: 6'b111111

  parameter logic [15:0] C1 = 16'b0111001100010100; // ECC: 6'b011001
  parameter logic [15:0] D1 = 16'b1111101101110110; // ECC: 6'b111001

  parameter logic [15:0] C2 = 16'b0001101110100010; // ECC: 6'b100011
  parameter logic [15:0] D2 = 16'b0011111111100011; // ECC: 6'b110111

  parameter logic [15:0] C3 = 16'b0000110101000010; // ECC: 6'b111101
  parameter logic [15:0] D3 = 16'b1100110111010110; // ECC: 6'b111111

  parameter logic [15:0] C4 = 16'b0001111111010001; // ECC: 6'b000010
  parameter logic [15:0] D4 = 16'b0001111111111001; // ECC: 6'b101111

  parameter logic [15:0] C5 = 16'b0010010000110000; // ECC: 6'b111111
  parameter logic [15:0] D5 = 16'b0111011100110101; // ECC: 6'b111111

  parameter logic [15:0] C6 = 16'b0010111010001111; // ECC: 6'b001000
  parameter logic [15:0] D6 = 16'b1011111010111111; // ECC: 6'b101100

  parameter logic [15:0] C7 = 16'b0100010000111101; // ECC: 6'b011010
  parameter logic [15:0] D7 = 16'b0101110011111101; // ECC: 6'b111110

  parameter logic [15:0] C8 = 16'b1110000000101100; // ECC: 6'b111001
  parameter logic [15:0] D8 = 16'b1110010110111101; // ECC: 6'b111101

  parameter logic [15:0] C9 = 16'b0010011100101110; // ECC: 6'b010001
  parameter logic [15:0] D9 = 16'b1011011110101111; // ECC: 6'b111001

  parameter logic [15:0] C10 = 16'b0010110011101110; // ECC: 6'b000100
  parameter logic [15:0] D10 = 16'b1010111011111110; // ECC: 6'b110110

  parameter logic [15:0] C11 = 16'b1100000100010011; // ECC: 6'b000011
  parameter logic [15:0] D11 = 16'b1110000110011011; // ECC: 6'b111011

  parameter logic [15:0] C12 = 16'b1000110110101101; // ECC: 6'b000010
  parameter logic [15:0] D12 = 16'b1001111110111101; // ECC: 6'b010111

  parameter logic [15:0] C13 = 16'b0000011111001011; // ECC: 6'b001010
  parameter logic [15:0] D13 = 16'b1001111111001111; // ECC: 6'b111010

  parameter logic [15:0] C14 = 16'b1101001001001010; // ECC: 6'b110100
  parameter logic [15:0] D14 = 16'b1101001011101111; // ECC: 6'b110111

  parameter logic [15:0] C15 = 16'b0001100011110101; // ECC: 6'b100010
  parameter logic [15:0] D15 = 16'b0011110011110111; // ECC: 6'b111011

  parameter logic [15:0] C16 = 16'b1000001110100011; // ECC: 6'b010110
  parameter logic [15:0] D16 = 16'b1100111111101111; // ECC: 6'b010110

  parameter logic [15:0] C17 = 16'b0100110101010001; // ECC: 6'b100110
  parameter logic [15:0] D17 = 16'b1111110101010011; // ECC: 6'b110111

  parameter logic [15:0] C18 = 16'b1010010000101010; // ECC: 6'b100001
  parameter logic [15:0] D18 = 16'b1010011111101110; // ECC: 6'b100011

  parameter logic [15:0] C19 = 16'b0001111001110000; // ECC: 6'b101010
  parameter logic [15:0] D19 = 16'b0111111111110011; // ECC: 6'b101010

  parameter logic [15:0] C20 = 16'b0010101001111110; // ECC: 6'b100000
  parameter logic [15:0] D20 = 16'b0110101111111110; // ECC: 6'b110101

  parameter logic [15:0] C21 = 16'b1001000011110000; // ECC: 6'b000011
  parameter logic [15:0] D21 = 16'b1001001011111101; // ECC: 6'b001111

  parameter logic [15:0] C22 = 16'b0101101010000001; // ECC: 6'b110110
  parameter logic [15:0] D22 = 16'b1111101010010101; // ECC: 6'b111111

  parameter logic [15:0] C23 = 16'b1101000100101110; // ECC: 6'b110000
  parameter logic [15:0] D23 = 16'b1111100110101110; // ECC: 6'b111110


  parameter logic [15:0] ZRO = 16'h0;

  ////////////////////////
  // Derived enum types //
  ////////////////////////

  // Use lc_state_t and lc_cnt_t in interfaces as very wide enumerations ( > 64 bits )
  // are not supported for virtual interfaces by Excelium yet
  // https://github.com/lowRISC/opentitan/issues/8884 (Cadence issue: cds_46570160)
  // The enumeration types lc_state_e and lc_cnt_e are still ok in other circumstances

  typedef logic [LcStateWidth-1:0] lc_state_t;
  typedef enum lc_state_t {
    LcStRaw           = {ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO},
    LcStTestUnlocked0 = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  A6,  A5,  A4,  A3,  A2,  A1,  B0},
    LcStTestLocked0   = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  A6,  A5,  A4,  A3,  A2,  B1,  B0},
    LcStTestUnlocked1 = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  A6,  A5,  A4,  A3,  B2,  B1,  B0},
    LcStTestLocked1   = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  A6,  A5,  A4,  B3,  B2,  B1,  B0},
    LcStTestUnlocked2 = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  A6,  A5,  B4,  B3,  B2,  B1,  B0},
    LcStTestLocked2   = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  A6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestUnlocked3 = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestLocked3   = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestUnlocked4 = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestLocked4   = {A19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestUnlocked5 = {A19, A18, A17, A16, A15, A14, A13, A12, A11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestLocked5   = {A19, A18, A17, A16, A15, A14, A13, A12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestUnlocked6 = {A19, A18, A17, A16, A15, A14, A13, B12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestLocked6   = {A19, A18, A17, A16, A15, A14, B13, B12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStTestUnlocked7 = {A19, A18, A17, A16, A15, B14, B13, B12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStDev           = {A19, A18, A17, A16, B15, B14, B13, B12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStProd          = {A19, A18, A17, B16, A15, B14, B13, B12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStProdEnd       = {A19, A18, B17, A16, A15, B14, B13, B12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStRma           = {B19, B18, A17, B16, B15, B14, B13, B12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0},
    LcStScrap         = {B19, B18, B17, B16, B15, B14, B13, B12, B11, B10,  B9,  B8,  B7,  B6,  B5,  B4,  B3,  B2,  B1,  B0}
  } lc_state_e;

  typedef logic [LcCountWidth-1:0] lc_cnt_t;
  typedef enum lc_cnt_t {
    LcCnt0  = {ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO},
    LcCnt1  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  C4,  C3,  C2,  C1,  D0},
    LcCnt2  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  C4,  C3,  C2,  D1,  D0},
    LcCnt3  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  C4,  C3,  D2,  D1,  D0},
    LcCnt4  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  C4,  D3,  D2,  D1,  D0},
    LcCnt5  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  D4,  D3,  D2,  D1,  D0},
    LcCnt6  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt7  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt8  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt9  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt10 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt11 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt12 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt13 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt14 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt15 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt16 = {C23, C22, C21, C20, C19, C18, C17, C16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt17 = {C23, C22, C21, C20, C19, C18, C17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt18 = {C23, C22, C21, C20, C19, C18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt19 = {C23, C22, C21, C20, C19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt20 = {C23, C22, C21, C20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt21 = {C23, C22, C21, D20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt22 = {C23, C22, D21, D20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt23 = {C23, D22, D21, D20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt24 = {D23, D22, D21, D20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0}
  } lc_cnt_e;

  // Decoded life cycle state, used to interface with CSRs and TAP.
  typedef enum logic [DecLcStateWidth-1:0] {
    DecLcStRaw = 0,
    DecLcStTestUnlocked0 = 1,
    DecLcStTestLocked0 = 2,
    DecLcStTestUnlocked1 = 3,
    DecLcStTestLocked1 = 4,
    DecLcStTestUnlocked2 = 5,
    DecLcStTestLocked2 = 6,
    DecLcStTestUnlocked3 = 7,
    DecLcStTestLocked3 = 8,
    DecLcStTestUnlocked4 = 9,
    DecLcStTestLocked4 = 10,
    DecLcStTestUnlocked5 = 11,
    DecLcStTestLocked5 = 12,
    DecLcStTestUnlocked6 = 13,
    DecLcStTestLocked6 = 14,
    DecLcStTestUnlocked7 = 15,
    DecLcStDev = 16,
    DecLcStProd = 17,
    DecLcStProdEnd = 18,
    DecLcStRma = 19,
    DecLcStScrap = 20,
    DecLcStPostTrans = 21,
    DecLcStEscalate = 22,
    DecLcStInvalid = 23
  } dec_lc_state_e;

  typedef dec_lc_state_e [DecLcStateNumRep-1:0] ext_dec_lc_state_t;

  typedef enum logic [DecLcIdStateWidth-1:0] {
    DecLcIdBlank,
    DecLcIdPersonalized,
    DecLcIdInvalid
  } dec_lc_id_state_e;

  typedef logic [DecLcCountWidth-1:0] dec_lc_cnt_t;


  ///////////////////////////////////////////
  // Hashed RAW unlock and all-zero tokens //
  ///////////////////////////////////////////

  parameter int LcTokenWidth = 128;
  typedef logic [LcTokenWidth-1:0] lc_token_t;

  parameter lc_token_t AllZeroToken = {
    128'h0
  };
  // [anjpar]: Renaming to *Default as we are not running topgen
  //parameter lc_token_t RndCnstRawUnlockToken = {
  parameter lc_token_t RndCnstRawUnlockTokenDefault = {
    128'h1C8BE2FF12790AE2E6D6A68151CBD084
  };
  parameter lc_token_t AllZeroTokenHashed = {
    128'h3852305BAECF5FF1D5C1D25F6DB9058D
  };
  parameter lc_token_t RndCnstRawUnlockTokenHashed = {
    128'hDEC8CCA47526BC0793AF7BB7560DD5A2
  };

endpackage : lc_ctrl_state_pkg

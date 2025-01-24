// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED decoder generated by util/design/secded_gen.py

module caliptra_prim_secded_72_64_dec (
  input        [71:0] data_i,
  output logic [63:0] data_o,
  output logic [7:0] syndrome_o,
  output logic [1:0] err_o
);

  always_comb begin : p_encode
    // Syndrome calculation
    syndrome_o[0] = ^(data_i & 72'h01B9000000001FFFFF);
    syndrome_o[1] = ^(data_i & 72'h025E00000FFFE0003F);
    syndrome_o[2] = ^(data_i & 72'h0467003FF003E007C1);
    syndrome_o[3] = ^(data_i & 72'h08CD0FC0F03C207842);
    syndrome_o[4] = ^(data_i & 72'h10B671C711C4438884);
    syndrome_o[5] = ^(data_i & 72'h20B5B65926488C9108);
    syndrome_o[6] = ^(data_i & 72'h40CBDAAA4A91152210);
    syndrome_o[7] = ^(data_i & 72'h807AED348D221A4420);

    // Corrected output calculation
    data_o[0] = (syndrome_o == 8'h7) ^ data_i[0];
    data_o[1] = (syndrome_o == 8'hb) ^ data_i[1];
    data_o[2] = (syndrome_o == 8'h13) ^ data_i[2];
    data_o[3] = (syndrome_o == 8'h23) ^ data_i[3];
    data_o[4] = (syndrome_o == 8'h43) ^ data_i[4];
    data_o[5] = (syndrome_o == 8'h83) ^ data_i[5];
    data_o[6] = (syndrome_o == 8'hd) ^ data_i[6];
    data_o[7] = (syndrome_o == 8'h15) ^ data_i[7];
    data_o[8] = (syndrome_o == 8'h25) ^ data_i[8];
    data_o[9] = (syndrome_o == 8'h45) ^ data_i[9];
    data_o[10] = (syndrome_o == 8'h85) ^ data_i[10];
    data_o[11] = (syndrome_o == 8'h19) ^ data_i[11];
    data_o[12] = (syndrome_o == 8'h29) ^ data_i[12];
    data_o[13] = (syndrome_o == 8'h49) ^ data_i[13];
    data_o[14] = (syndrome_o == 8'h89) ^ data_i[14];
    data_o[15] = (syndrome_o == 8'h31) ^ data_i[15];
    data_o[16] = (syndrome_o == 8'h51) ^ data_i[16];
    data_o[17] = (syndrome_o == 8'h91) ^ data_i[17];
    data_o[18] = (syndrome_o == 8'h61) ^ data_i[18];
    data_o[19] = (syndrome_o == 8'ha1) ^ data_i[19];
    data_o[20] = (syndrome_o == 8'hc1) ^ data_i[20];
    data_o[21] = (syndrome_o == 8'he) ^ data_i[21];
    data_o[22] = (syndrome_o == 8'h16) ^ data_i[22];
    data_o[23] = (syndrome_o == 8'h26) ^ data_i[23];
    data_o[24] = (syndrome_o == 8'h46) ^ data_i[24];
    data_o[25] = (syndrome_o == 8'h86) ^ data_i[25];
    data_o[26] = (syndrome_o == 8'h1a) ^ data_i[26];
    data_o[27] = (syndrome_o == 8'h2a) ^ data_i[27];
    data_o[28] = (syndrome_o == 8'h4a) ^ data_i[28];
    data_o[29] = (syndrome_o == 8'h8a) ^ data_i[29];
    data_o[30] = (syndrome_o == 8'h32) ^ data_i[30];
    data_o[31] = (syndrome_o == 8'h52) ^ data_i[31];
    data_o[32] = (syndrome_o == 8'h92) ^ data_i[32];
    data_o[33] = (syndrome_o == 8'h62) ^ data_i[33];
    data_o[34] = (syndrome_o == 8'ha2) ^ data_i[34];
    data_o[35] = (syndrome_o == 8'hc2) ^ data_i[35];
    data_o[36] = (syndrome_o == 8'h1c) ^ data_i[36];
    data_o[37] = (syndrome_o == 8'h2c) ^ data_i[37];
    data_o[38] = (syndrome_o == 8'h4c) ^ data_i[38];
    data_o[39] = (syndrome_o == 8'h8c) ^ data_i[39];
    data_o[40] = (syndrome_o == 8'h34) ^ data_i[40];
    data_o[41] = (syndrome_o == 8'h54) ^ data_i[41];
    data_o[42] = (syndrome_o == 8'h94) ^ data_i[42];
    data_o[43] = (syndrome_o == 8'h64) ^ data_i[43];
    data_o[44] = (syndrome_o == 8'ha4) ^ data_i[44];
    data_o[45] = (syndrome_o == 8'hc4) ^ data_i[45];
    data_o[46] = (syndrome_o == 8'h38) ^ data_i[46];
    data_o[47] = (syndrome_o == 8'h58) ^ data_i[47];
    data_o[48] = (syndrome_o == 8'h98) ^ data_i[48];
    data_o[49] = (syndrome_o == 8'h68) ^ data_i[49];
    data_o[50] = (syndrome_o == 8'ha8) ^ data_i[50];
    data_o[51] = (syndrome_o == 8'hc8) ^ data_i[51];
    data_o[52] = (syndrome_o == 8'h70) ^ data_i[52];
    data_o[53] = (syndrome_o == 8'hb0) ^ data_i[53];
    data_o[54] = (syndrome_o == 8'hd0) ^ data_i[54];
    data_o[55] = (syndrome_o == 8'he0) ^ data_i[55];
    data_o[56] = (syndrome_o == 8'h6d) ^ data_i[56];
    data_o[57] = (syndrome_o == 8'hd6) ^ data_i[57];
    data_o[58] = (syndrome_o == 8'h3e) ^ data_i[58];
    data_o[59] = (syndrome_o == 8'hcb) ^ data_i[59];
    data_o[60] = (syndrome_o == 8'hb3) ^ data_i[60];
    data_o[61] = (syndrome_o == 8'hb5) ^ data_i[61];
    data_o[62] = (syndrome_o == 8'hce) ^ data_i[62];
    data_o[63] = (syndrome_o == 8'h79) ^ data_i[63];

    // err_o calc. bit0: single error, bit1: double error
    err_o[0] = ^syndrome_o;
    err_o[1] = ~err_o[0] & (|syndrome_o);
  end
endmodule : caliptra_prim_secded_72_64_dec

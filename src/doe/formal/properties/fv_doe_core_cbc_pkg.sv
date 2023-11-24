// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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

package doe_core_cbc_pkg;

// AES S-box
parameter [7:0] fv_sbox[0:255] = '{
  8'h63, 8'h7C, 8'h77, 8'h7B, 8'hF2, 8'h6B, 8'h6F, 8'hC5, 8'h30, 8'h01, 8'h67, 8'h2B, 8'hFE, 8'hD7, 8'hAB, 8'h76,
  8'hCA, 8'h82, 8'hC9, 8'h7D, 8'hFA, 8'h59, 8'h47, 8'hF0, 8'hAD, 8'hD4, 8'hA2, 8'hAF, 8'h9C, 8'hA4, 8'h72, 8'hC0,
  8'hB7, 8'hFD, 8'h93, 8'h26, 8'h36, 8'h3F, 8'hF7, 8'hCC, 8'h34, 8'hA5, 8'hE5, 8'hF1, 8'h71, 8'hD8, 8'h31, 8'h15,
  8'h04, 8'hC7, 8'h23, 8'hC3, 8'h18, 8'h96, 8'h05, 8'h9A, 8'h07, 8'h12, 8'h80, 8'hE2, 8'hEB, 8'h27, 8'hB2, 8'h75,
  8'h09, 8'h83, 8'h2C, 8'h1A, 8'h1B, 8'h6E, 8'h5A, 8'hA0, 8'h52, 8'h3B, 8'hD6, 8'hB3, 8'h29, 8'hE3, 8'h2F, 8'h84,
  8'h53, 8'hD1, 8'h00, 8'hED, 8'h20, 8'hFC, 8'hB1, 8'h5B, 8'h6A, 8'hCB, 8'hBE, 8'h39, 8'h4A, 8'h4C, 8'h58, 8'hCF,
  8'hD0, 8'hEF, 8'hAA, 8'hFB, 8'h43, 8'h4D, 8'h33, 8'h85, 8'h45, 8'hF9, 8'h02, 8'h7F, 8'h50, 8'h3C, 8'h9F, 8'hA8,
  8'h51, 8'hA3, 8'h40, 8'h8F, 8'h92, 8'h9D, 8'h38, 8'hF5, 8'hBC, 8'hB6, 8'hDA, 8'h21, 8'h10, 8'hFF, 8'hF3, 8'hD2,
  8'hCD, 8'h0C, 8'h13, 8'hEC, 8'h5F, 8'h97, 8'h44, 8'h17, 8'hC4, 8'hA7, 8'h7E, 8'h3D, 8'h64, 8'h5D, 8'h19, 8'h73,
  8'h60, 8'h81, 8'h4F, 8'hDC, 8'h22, 8'h2A, 8'h90, 8'h88, 8'h46, 8'hEE, 8'hB8, 8'h14, 8'hDE, 8'h5E, 8'h0B, 8'hDB,
  8'hE0, 8'h32, 8'h3A, 8'h0A, 8'h49, 8'h06, 8'h24, 8'h5C, 8'hC2, 8'hD3, 8'hAC, 8'h62, 8'h91, 8'h95, 8'hE4, 8'h79,
  8'hE7, 8'hC8, 8'h37, 8'h6D, 8'h8D, 8'hD5, 8'h4E, 8'hA9, 8'h6C, 8'h56, 8'hF4, 8'hEA, 8'h65, 8'h7A, 8'hAE, 8'h08,
  8'hBA, 8'h78, 8'h25, 8'h2E, 8'h1C, 8'hA6, 8'hB4, 8'hC6, 8'hE8, 8'hDD, 8'h74, 8'h1F, 8'h4B, 8'hBD, 8'h8B, 8'h8A,
  8'h70, 8'h3E, 8'hB5, 8'h66, 8'h48, 8'h03, 8'hF6, 8'h0E, 8'h61, 8'h35, 8'h57, 8'hB9, 8'h86, 8'hC1, 8'h1D, 8'h9E,
  8'hE1, 8'hF8, 8'h98, 8'h11, 8'h69, 8'hD9, 8'h8E, 8'h94, 8'h9B, 8'h1E, 8'h87, 8'hE9, 8'hCE, 8'h55, 8'h28, 8'hDF,
  8'h8C, 8'hA1, 8'h89, 8'h0D, 8'hBF, 8'hE6, 8'h42, 8'h68, 8'h41, 8'h99, 8'h2D, 8'h0F, 8'hB0, 8'h54, 8'hBB, 8'h16
};

// AES Inverse S-box
parameter [7:0] fv_inv_sbox[0:255] = '{
  8'h52, 8'h09, 8'h6A, 8'hD5, 8'h30, 8'h36, 8'hA5, 8'h38, 8'hBF, 8'h40, 8'hA3, 8'h9E, 8'h81, 8'hF3, 8'hD7, 8'hFB,
  8'h7C, 8'hE3, 8'h39, 8'h82, 8'h9B, 8'h2F, 8'hFF, 8'h87, 8'h34, 8'h8E, 8'h43, 8'h44, 8'hC4, 8'hDE, 8'hE9, 8'hCB,
  8'h54, 8'h7B, 8'h94, 8'h32, 8'hA6, 8'hC2, 8'h23, 8'h3D, 8'hEE, 8'h4C, 8'h95, 8'h0B, 8'h42, 8'hFA, 8'hC3, 8'h4E,
  8'h08, 8'h2E, 8'hA1, 8'h66, 8'h28, 8'hD9, 8'h24, 8'hB2, 8'h76, 8'h5B, 8'hA2, 8'h49, 8'h6D, 8'h8B, 8'hD1, 8'h25,
  8'h72, 8'hF8, 8'hF6, 8'h64, 8'h86, 8'h68, 8'h98, 8'h16, 8'hD4, 8'hA4, 8'h5C, 8'hCC, 8'h5D, 8'h65, 8'hB6, 8'h92,
  8'h6C, 8'h70, 8'h48, 8'h50, 8'hFD, 8'hED, 8'hB9, 8'hDA, 8'h5E, 8'h15, 8'h46, 8'h57, 8'hA7, 8'h8D, 8'h9D, 8'h84,
  8'h90, 8'hD8, 8'hAB, 8'h00, 8'h8C, 8'hBC, 8'hD3, 8'h0A, 8'hF7, 8'hE4, 8'h58, 8'h05, 8'hB8, 8'hB3, 8'h45, 8'h06,
  8'hD0, 8'h2C, 8'h1E, 8'h8F, 8'hCA, 8'h3F, 8'h0F, 8'h02, 8'hC1, 8'hAF, 8'hBD, 8'h03, 8'h01, 8'h13, 8'h8A, 8'h6B,
  8'h3A, 8'h91, 8'h11, 8'h41, 8'h4F, 8'h67, 8'hDC, 8'hEA, 8'h97, 8'hF2, 8'hCF, 8'hCE, 8'hF0, 8'hB4, 8'hE6, 8'h73,
  8'h96, 8'hAC, 8'h74, 8'h22, 8'hE7, 8'hAD, 8'h35, 8'h85, 8'hE2, 8'hF9, 8'h37, 8'hE8, 8'h1C, 8'h75, 8'hDF, 8'h6E,
  8'h47, 8'hF1, 8'h1A, 8'h71, 8'h1D, 8'h29, 8'hC5, 8'h89, 8'h6F, 8'hB7, 8'h62, 8'h0E, 8'hAA, 8'h18, 8'hBE, 8'h1B,
  8'hFC, 8'h56, 8'h3E, 8'h4B, 8'hC6, 8'hD2, 8'h79, 8'h20, 8'h9A, 8'hDB, 8'hC0, 8'hFE, 8'h78, 8'hCD, 8'h5A, 8'hF4,
  8'h1F, 8'hDD, 8'hA8, 8'h33, 8'h88, 8'h07, 8'hC7, 8'h31, 8'hB1, 8'h12, 8'h10, 8'h59, 8'h27, 8'h80, 8'hEC, 8'h5F,
  8'h60, 8'h51, 8'h7F, 8'hA9, 8'h19, 8'hB5, 8'h4A, 8'h0D, 8'h2D, 8'hE5, 8'h7A, 8'h9F, 8'h93, 8'hC9, 8'h9C, 8'hEF,
  8'hA0, 8'hE0, 8'h3B, 8'h4D, 8'hAE, 8'h2A, 8'hF5, 8'hB0, 8'hC8, 8'hEB, 8'hBB, 8'h3C, 8'h83, 8'h53, 8'h99, 8'h61,
  8'h17, 8'h2B, 8'h04, 8'h7E, 8'hBA, 8'h77, 8'hD6, 8'h26, 8'hE1, 8'h69, 8'h14, 8'h63, 8'h55, 8'h21, 8'h0C, 8'h7D
};

// Rcon values for key schedule
parameter [31:0] fv_rcon[0:15] = '{ 
32'h00000000, 32'h01000000, 32'h02000000, 32'h04000000, 
32'h08000000, 32'h10000000, 32'h20000000, 32'h40000000, 
32'h80000000, 32'h1B000000, 32'h36000000, 32'h6C000000, 
32'hD8000000, 32'hAB000000, 32'h4D000000, 32'h9A000000
};

// GF_2 for MixColumns
parameter [7:0] fv_gf2[0:255] = '{
  8'h00, 8'h02, 8'h04, 8'h06, 8'h08, 8'h0A, 8'h0C, 8'h0E, 8'h10, 8'h12, 8'h14, 8'h16, 8'h18, 8'h1A, 8'h1C, 8'h1E,
  8'h20, 8'h22, 8'h24, 8'h26, 8'h28, 8'h2A, 8'h2C, 8'h2E, 8'h30, 8'h32, 8'h34, 8'h36, 8'h38, 8'h3A, 8'h3C, 8'h3E,
  8'h40, 8'h42, 8'h44, 8'h46, 8'h48, 8'h4a, 8'h4c, 8'h4e, 8'h50, 8'h52, 8'h54, 8'h56, 8'h58, 8'h5a, 8'h5c, 8'h5e,
  8'h60, 8'h62, 8'h64, 8'h66, 8'h68, 8'h6a, 8'h6c, 8'h6e, 8'h70, 8'h72, 8'h74, 8'h76, 8'h78, 8'h7a, 8'h7c, 8'h7e,	
  8'h80, 8'h82, 8'h84, 8'h86, 8'h88, 8'h8a, 8'h8c, 8'h8e, 8'h90, 8'h92, 8'h94, 8'h96, 8'h98, 8'h9a, 8'h9c, 8'h9e,
  8'ha0, 8'ha2, 8'ha4, 8'ha6, 8'ha8, 8'haa, 8'hac, 8'hae, 8'hb0, 8'hb2, 8'hb4, 8'hb6, 8'hb8, 8'hba, 8'hbc, 8'hbe,
  8'hc0, 8'hc2, 8'hc4, 8'hc6, 8'hc8, 8'hca, 8'hcc, 8'hce, 8'hd0, 8'hd2, 8'hd4, 8'hd6, 8'hd8, 8'hda, 8'hdc, 8'hde,
  8'he0, 8'he2, 8'he4, 8'he6, 8'he8, 8'hea, 8'hec, 8'hee, 8'hf0, 8'hf2, 8'hf4, 8'hf6, 8'hf8, 8'hfa, 8'hfc, 8'hfe,
  8'h1b, 8'h19, 8'h1f, 8'h1d, 8'h13, 8'h11, 8'h17, 8'h15, 8'h0b, 8'h09, 8'h0f, 8'h0d, 8'h03, 8'h01, 8'h07, 8'h05,
  8'h3b, 8'h39, 8'h3f, 8'h3d, 8'h33, 8'h31, 8'h37, 8'h35, 8'h2b, 8'h29, 8'h2f, 8'h2d, 8'h23, 8'h21, 8'h27, 8'h25,
  8'h5b, 8'h59, 8'h5f, 8'h5d, 8'h53, 8'h51, 8'h57, 8'h55, 8'h4b, 8'h49, 8'h4f, 8'h4d, 8'h43, 8'h41, 8'h47, 8'h45,
  8'h7b, 8'h79, 8'h7f, 8'h7d, 8'h73, 8'h71, 8'h77, 8'h75, 8'h6b, 8'h69, 8'h6f, 8'h6d, 8'h63, 8'h61, 8'h67, 8'h65,
  8'h9b, 8'h99, 8'h9f, 8'h9d, 8'h93, 8'h91, 8'h97, 8'h95, 8'h8b, 8'h89, 8'h8f, 8'h8d, 8'h83, 8'h81, 8'h87, 8'h85,
  8'hbb, 8'hb9, 8'hbf, 8'hbd, 8'hb3, 8'hb1, 8'hb7, 8'hb5, 8'hab, 8'ha9, 8'haf, 8'had, 8'ha3, 8'ha1, 8'ha7, 8'ha5,
  8'hdb, 8'hd9, 8'hdf, 8'hdd, 8'hd3, 8'hd1, 8'hd7, 8'hd5, 8'hcb, 8'hc9, 8'hcf, 8'hcd, 8'hc3, 8'hc1, 8'hc7, 8'hc5,
  8'hfb, 8'hf9, 8'hff, 8'hfd, 8'hf3, 8'hf1, 8'hf7, 8'hf5, 8'heb, 8'he9, 8'hef, 8'hed, 8'he3, 8'he1, 8'he7, 8'he5
};

// GF_3 for MixColumns
parameter [7:0] fv_gf3[0:255] = '{
  8'h00, 8'h03, 8'h06, 8'h05, 8'h0C, 8'h0f, 8'h0A, 8'h09, 8'h18, 8'h1b, 8'h1E, 8'h1d, 8'h14, 8'h17, 8'h12, 8'h11,
  8'h30, 8'h33, 8'h36, 8'h35, 8'h3C, 8'h3f, 8'h3A, 8'h39, 8'h28, 8'h2b, 8'h2E, 8'h2d, 8'h24, 8'h27, 8'h22, 8'h21,
  8'h60, 8'h63, 8'h66, 8'h65, 8'h6c, 8'h6f, 8'h6a, 8'h69, 8'h78, 8'h7b, 8'h7e, 8'h7d, 8'h74, 8'h77, 8'h72, 8'h71,
  8'h50, 8'h53, 8'h56, 8'h55, 8'h5c, 8'h5f, 8'h5a, 8'h59, 8'h48, 8'h4b, 8'h4e, 8'h4d, 8'h44, 8'h47, 8'h42, 8'h41,
  8'hc0, 8'hc3, 8'hc6, 8'hc5, 8'hcc, 8'hcf, 8'hca, 8'hc9, 8'hd8, 8'hdb, 8'hde, 8'hdd, 8'hd4, 8'hd7, 8'hd2, 8'hd1,
  8'hf0, 8'hf3, 8'hf6, 8'hf5, 8'hfc, 8'hff, 8'hfa, 8'hf9, 8'he8, 8'heb, 8'hee, 8'hed, 8'he4, 8'he7, 8'he2, 8'he1,
  8'ha0, 8'ha3, 8'ha6, 8'ha5, 8'hac, 8'haf, 8'haa, 8'ha9, 8'hb8, 8'hbb, 8'hbe, 8'hbd, 8'hb4, 8'hb7, 8'hb2, 8'hb1,
  8'h90, 8'h93, 8'h96, 8'h95, 8'h9c, 8'h9f, 8'h9a, 8'h99, 8'h88, 8'h8b, 8'h8e, 8'h8d, 8'h84, 8'h87, 8'h82, 8'h81,	
  8'h9b, 8'h98, 8'h9d, 8'h9e, 8'h97, 8'h94, 8'h91, 8'h92, 8'h83, 8'h80, 8'h85, 8'h86, 8'h8f, 8'h8c, 8'h89, 8'h8a,
  8'hab, 8'ha8, 8'had, 8'hae, 8'ha7, 8'ha4, 8'ha1, 8'ha2, 8'hb3, 8'hb0, 8'hb5, 8'hb6, 8'hbf, 8'hbc, 8'hb9, 8'hba,
  8'hfb, 8'hf8, 8'hfd, 8'hfe, 8'hf7, 8'hf4, 8'hf1, 8'hf2, 8'he3, 8'he0, 8'he5, 8'he6, 8'hef, 8'hec, 8'he9, 8'hea,	
  8'hcb, 8'hc8, 8'hcd, 8'hce, 8'hc7, 8'hc4, 8'hc1, 8'hc2, 8'hd3, 8'hd0, 8'hd5, 8'hd6, 8'hdf, 8'hdc, 8'hd9, 8'hda,	
  8'h5b, 8'h58, 8'h5d, 8'h5e, 8'h57, 8'h54, 8'h51, 8'h52, 8'h43, 8'h40, 8'h45, 8'h46, 8'h4f, 8'h4c, 8'h49, 8'h4a,
  8'h6b, 8'h68, 8'h6d, 8'h6e, 8'h67, 8'h64, 8'h61, 8'h62, 8'h73, 8'h70, 8'h75, 8'h76, 8'h7f, 8'h7c, 8'h79, 8'h7a,	
  8'h3b, 8'h38, 8'h3d, 8'h3E, 8'h37, 8'h34, 8'h31, 8'h32, 8'h23, 8'h20, 8'h25, 8'h26, 8'h2f, 8'h2C, 8'h29, 8'h2A,
  8'h0b, 8'h08, 8'h0d, 8'h0E, 8'h07, 8'h04, 8'h01, 8'h02, 8'h13, 8'h10, 8'h15, 8'h16, 8'h1f, 8'h1C, 8'h19, 8'h1A
};

// GF_9 for MixColumns
parameter [7:0] fv_gf9[0:255] = '{
  8'h00, 8'h09, 8'h12, 8'h1b, 8'h24, 8'h2d, 8'h36, 8'h3f, 8'h48, 8'h41, 8'h5a, 8'h53, 8'h6c, 8'h65, 8'h7e, 8'h77,
  8'h90, 8'h99, 8'h82, 8'h8b, 8'hb4, 8'hbd, 8'ha6, 8'haf, 8'hd8, 8'hd1, 8'hca, 8'hc3, 8'hfc, 8'hf5, 8'hee, 8'he7,
  8'h3b, 8'h32, 8'h29, 8'h20, 8'h1f, 8'h16, 8'h0d, 8'h04, 8'h73, 8'h7a, 8'h61, 8'h68, 8'h57, 8'h5e, 8'h45, 8'h4c,
  8'hab, 8'ha2, 8'hb9, 8'hb0, 8'h8f, 8'h86, 8'h9d, 8'h94, 8'he3, 8'hea, 8'hf1, 8'hf8, 8'hc7, 8'hce, 8'hd5, 8'hdc,
  8'h76, 8'h7f, 8'h64, 8'h6d, 8'h52, 8'h5b, 8'h40, 8'h49, 8'h3E, 8'h37, 8'h2C, 8'h25, 8'h1A, 8'h13, 8'h08, 8'h01,
  8'he6, 8'hef, 8'hf4, 8'hfd, 8'hc2, 8'hcb, 8'hd0, 8'hd9, 8'hae, 8'ha7, 8'hbc, 8'hb5, 8'h8a, 8'h83, 8'h98, 8'h91,
  8'h4d, 8'h44, 8'h5f, 8'h56, 8'h69, 8'h60, 8'h7b, 8'h72, 8'h05, 8'h0C, 8'h17, 8'h1E, 8'h21, 8'h28, 8'h33, 8'h3A,
  8'hdd, 8'hd4, 8'hcf, 8'hc6, 8'hf9, 8'hf0, 8'heb, 8'he2, 8'h95, 8'h9c, 8'h87, 8'h8e, 8'hb1, 8'hb8, 8'ha3, 8'haa,	
  8'hec, 8'he5, 8'hfe, 8'hf7, 8'hc8, 8'hc1, 8'hda, 8'hd3, 8'ha4, 8'had, 8'hb6, 8'hbf, 8'h80, 8'h89, 8'h92, 8'h9b,	
  8'h7c, 8'h75, 8'h6e, 8'h67, 8'h58, 8'h51, 8'h4a, 8'h43, 8'h34, 8'h3d, 8'h26, 8'h2f, 8'h10, 8'h19, 8'h02, 8'h0b,
  8'hd7, 8'hde, 8'hc5, 8'hcc, 8'hf3, 8'hfa, 8'he1, 8'he8, 8'h9f, 8'h96, 8'h8d, 8'h84, 8'hbb, 8'hb2, 8'ha9, 8'ha0,
  8'h47, 8'h4e, 8'h55, 8'h5c, 8'h63, 8'h6a, 8'h71, 8'h78, 8'h0f, 8'h06, 8'h1d, 8'h14, 8'h2b, 8'h22, 8'h39, 8'h30,
  8'h9a, 8'h93, 8'h88, 8'h81, 8'hbe, 8'hb7, 8'hac, 8'ha5, 8'hd2, 8'hdb, 8'hc0, 8'hc9, 8'hf6, 8'hff, 8'he4, 8'hed,
  8'h0A, 8'h03, 8'h18, 8'h11, 8'h2E, 8'h27, 8'h3C, 8'h35, 8'h42, 8'h4b, 8'h50, 8'h59, 8'h66, 8'h6f, 8'h74, 8'h7d,	
  8'ha1, 8'ha8, 8'hb3, 8'hba, 8'h85, 8'h8c, 8'h97, 8'h9e, 8'he9, 8'he0, 8'hfb, 8'hf2, 8'hcd, 8'hc4, 8'hdf, 8'hd6,
  8'h31, 8'h38, 8'h23, 8'h2A, 8'h15, 8'h1C, 8'h07, 8'h0E, 8'h79, 8'h70, 8'h6b, 8'h62, 8'h5d, 8'h54, 8'h4f, 8'h46
};

// GF_B for MixColumns
parameter [7:0] fv_gfB[0:255] = '{
  8'h00, 8'h0b, 8'h16, 8'h1d, 8'h2C, 8'h27, 8'h3A, 8'h31, 8'h58, 8'h53, 8'h4e, 8'h45, 8'h74, 8'h7f, 8'h62, 8'h69,
  8'hb0, 8'hbb, 8'ha6, 8'had, 8'h9c, 8'h97, 8'h8a, 8'h81, 8'he8, 8'he3, 8'hfe, 8'hf5, 8'hc4, 8'hcf, 8'hd2, 8'hd9,
  8'h7b, 8'h70, 8'h6d, 8'h66, 8'h57, 8'h5c, 8'h41, 8'h4a, 8'h23, 8'h28, 8'h35, 8'h3E, 8'h0f, 8'h04, 8'h19, 8'h12,
  8'hcb, 8'hc0, 8'hdd, 8'hd6, 8'he7, 8'hec, 8'hf1, 8'hfa, 8'h93, 8'h98, 8'h85, 8'h8e, 8'hbf, 8'hb4, 8'ha9, 8'ha2,
  8'hf6, 8'hfd, 8'he0, 8'heb, 8'hda, 8'hd1, 8'hcc, 8'hc7, 8'hae, 8'ha5, 8'hb8, 8'hb3, 8'h82, 8'h89, 8'h94, 8'h9f,
  8'h46, 8'h4d, 8'h50, 8'h5b, 8'h6a, 8'h61, 8'h7c, 8'h77, 8'h1E, 8'h15, 8'h08, 8'h03, 8'h32, 8'h39, 8'h24, 8'h2f,
  8'h8d, 8'h86, 8'h9b, 8'h90, 8'ha1, 8'haa, 8'hb7, 8'hbc, 8'hd5, 8'hde, 8'hc3, 8'hc8, 8'hf9, 8'hf2, 8'hef, 8'he4,
  8'h3d, 8'h36, 8'h2b, 8'h20, 8'h11, 8'h1A, 8'h07, 8'h0C, 8'h65, 8'h6e, 8'h73, 8'h78, 8'h49, 8'h42, 8'h5f, 8'h54,
  8'hf7, 8'hfc, 8'he1, 8'hea, 8'hdb, 8'hd0, 8'hcd, 8'hc6, 8'haf, 8'ha4, 8'hb9, 8'hb2, 8'h83, 8'h88, 8'h95, 8'h9e,
  8'h47, 8'h4c, 8'h51, 8'h5a, 8'h6b, 8'h60, 8'h7d, 8'h76, 8'h1f, 8'h14, 8'h09, 8'h02, 8'h33, 8'h38, 8'h25, 8'h2E,
  8'h8c, 8'h87, 8'h9a, 8'h91, 8'ha0, 8'hab, 8'hb6, 8'hbd, 8'hd4, 8'hdf, 8'hc2, 8'hc9, 8'hf8, 8'hf3, 8'hee, 8'he5,
  8'h3C, 8'h37, 8'h2A, 8'h21, 8'h10, 8'h1b, 8'h06, 8'h0d, 8'h64, 8'h6f, 8'h72, 8'h79, 8'h48, 8'h43, 8'h5e, 8'h55,
  8'h01, 8'h0A, 8'h17, 8'h1C, 8'h2d, 8'h26, 8'h3b, 8'h30, 8'h59, 8'h52, 8'h4f, 8'h44, 8'h75, 8'h7e, 8'h63, 8'h68,
  8'hb1, 8'hba, 8'ha7, 8'hac, 8'h9d, 8'h96, 8'h8b, 8'h80, 8'he9, 8'he2, 8'hff, 8'hf4, 8'hc5, 8'hce, 8'hd3, 8'hd8,
  8'h7a, 8'h71, 8'h6c, 8'h67, 8'h56, 8'h5d, 8'h40, 8'h4b, 8'h22, 8'h29, 8'h34, 8'h3f, 8'h0E, 8'h05, 8'h18, 8'h13,
  8'hca, 8'hc1, 8'hdc, 8'hd7, 8'he6, 8'hed, 8'hf0, 8'hfb, 8'h92, 8'h99, 8'h84, 8'h8f, 8'hbe, 8'hb5, 8'ha8, 8'ha3
};

// GF_D for MixColumns
parameter [7:0] fv_gfD[0:255] = '{
  8'h00, 8'h0d, 8'h1A, 8'h17, 8'h34, 8'h39, 8'h2E, 8'h23, 8'h68, 8'h65, 8'h72, 8'h7f, 8'h5c, 8'h51, 8'h46, 8'h4b,
  8'hd0, 8'hdd, 8'hca, 8'hc7, 8'he4, 8'he9, 8'hfe, 8'hf3, 8'hb8, 8'hb5, 8'ha2, 8'haf, 8'h8c, 8'h81, 8'h96, 8'h9b,
  8'hbb, 8'hb6, 8'ha1, 8'hac, 8'h8f, 8'h82, 8'h95, 8'h98, 8'hd3, 8'hde, 8'hc9, 8'hc4, 8'he7, 8'hea, 8'hfd, 8'hf0,
  8'h6b, 8'h66, 8'h71, 8'h7c, 8'h5f, 8'h52, 8'h45, 8'h48, 8'h03, 8'h0E, 8'h19, 8'h14, 8'h37, 8'h3A, 8'h2d, 8'h20,
  8'h6d, 8'h60, 8'h77, 8'h7a, 8'h59, 8'h54, 8'h43, 8'h4e, 8'h05, 8'h08, 8'h1f, 8'h12, 8'h31, 8'h3C, 8'h2b, 8'h26,
  8'hbd, 8'hb0, 8'ha7, 8'haa, 8'h89, 8'h84, 8'h93, 8'h9e, 8'hd5, 8'hd8, 8'hcf, 8'hc2, 8'he1, 8'hec, 8'hfb, 8'hf6,
  8'hd6, 8'hdb, 8'hcc, 8'hc1, 8'he2, 8'hef, 8'hf8, 8'hf5, 8'hbe, 8'hb3, 8'ha4, 8'ha9, 8'h8a, 8'h87, 8'h90, 8'h9d,
  8'h06, 8'h0b, 8'h1C, 8'h11, 8'h32, 8'h3f, 8'h28, 8'h25, 8'h6e, 8'h63, 8'h74, 8'h79, 8'h5a, 8'h57, 8'h40, 8'h4d,
  8'hda, 8'hd7, 8'hc0, 8'hcd, 8'hee, 8'he3, 8'hf4, 8'hf9, 8'hb2, 8'hbf, 8'ha8, 8'ha5, 8'h86, 8'h8b, 8'h9c, 8'h91,
  8'h0A, 8'h07, 8'h10, 8'h1d, 8'h3E, 8'h33, 8'h24, 8'h29, 8'h62, 8'h6f, 8'h78, 8'h75, 8'h56, 8'h5b, 8'h4c, 8'h41,
  8'h61, 8'h6c, 8'h7b, 8'h76, 8'h55, 8'h58, 8'h4f, 8'h42, 8'h09, 8'h04, 8'h13, 8'h1E, 8'h3d, 8'h30, 8'h27, 8'h2A,
  8'hb1, 8'hbc, 8'hab, 8'ha6, 8'h85, 8'h88, 8'h9f, 8'h92, 8'hd9, 8'hd4, 8'hc3, 8'hce, 8'hed, 8'he0, 8'hf7, 8'hfa,
  8'hb7, 8'hba, 8'had, 8'ha0, 8'h83, 8'h8e, 8'h99, 8'h94, 8'hdf, 8'hd2, 8'hc5, 8'hc8, 8'heb, 8'he6, 8'hf1, 8'hfc,
  8'h67, 8'h6a, 8'h7d, 8'h70, 8'h53, 8'h5e, 8'h49, 8'h44, 8'h0f, 8'h02, 8'h15, 8'h18, 8'h3b, 8'h36, 8'h21, 8'h2C,
  8'h0C, 8'h01, 8'h16, 8'h1b, 8'h38, 8'h35, 8'h22, 8'h2f, 8'h64, 8'h69, 8'h7e, 8'h73, 8'h50, 8'h5d, 8'h4a, 8'h47,
  8'hdc, 8'hd1, 8'hc6, 8'hcb, 8'he8, 8'he5, 8'hf2, 8'hff, 8'hb4, 8'hb9, 8'hae, 8'ha3, 8'h80, 8'h8d, 8'h9a, 8'h97
};

// GF_E for MixColumns
parameter [7:0] fv_gfE[0:255] = '{
  8'h00, 8'h0E, 8'h1C, 8'h12, 8'h38, 8'h36, 8'h24, 8'h2A, 8'h70, 8'h7e, 8'h6c, 8'h62, 8'h48, 8'h46, 8'h54, 8'h5a,
  8'he0, 8'hee, 8'hfc, 8'hf2, 8'hd8, 8'hd6, 8'hc4, 8'hca, 8'h90, 8'h9e, 8'h8c, 8'h82, 8'ha8, 8'ha6, 8'hb4, 8'hba,
  8'hdb, 8'hd5, 8'hc7, 8'hc9, 8'he3, 8'hed, 8'hff, 8'hf1, 8'hab, 8'ha5, 8'hb7, 8'hb9, 8'h93, 8'h9d, 8'h8f, 8'h81,
  8'h3b, 8'h35, 8'h27, 8'h29, 8'h03, 8'h0d, 8'h1f, 8'h11, 8'h4b, 8'h45, 8'h57, 8'h59, 8'h73, 8'h7d, 8'h6f, 8'h61,
  8'had, 8'ha3, 8'hb1, 8'hbf, 8'h95, 8'h9b, 8'h89, 8'h87, 8'hdd, 8'hd3, 8'hc1, 8'hcf, 8'he5, 8'heb, 8'hf9, 8'hf7,
  8'h4d, 8'h43, 8'h51, 8'h5f, 8'h75, 8'h7b, 8'h69, 8'h67, 8'h3d, 8'h33, 8'h21, 8'h2f, 8'h05, 8'h0b, 8'h19, 8'h17,
  8'h76, 8'h78, 8'h6a, 8'h64, 8'h4e, 8'h40, 8'h52, 8'h5c, 8'h06, 8'h08, 8'h1A, 8'h14, 8'h3E, 8'h30, 8'h22, 8'h2C,
  8'h96, 8'h98, 8'h8a, 8'h84, 8'hae, 8'ha0, 8'hb2, 8'hbc, 8'he6, 8'he8, 8'hfa, 8'hf4, 8'hde, 8'hd0, 8'hc2, 8'hcc,
  8'h41, 8'h4f, 8'h5d, 8'h53, 8'h79, 8'h77, 8'h65, 8'h6b, 8'h31, 8'h3f, 8'h2d, 8'h23, 8'h09, 8'h07, 8'h15, 8'h1b,
  8'ha1, 8'haf, 8'hbd, 8'hb3, 8'h99, 8'h97, 8'h85, 8'h8b, 8'hd1, 8'hdf, 8'hcd, 8'hc3, 8'he9, 8'he7, 8'hf5, 8'hfb,
  8'h9a, 8'h94, 8'h86, 8'h88, 8'ha2, 8'hac, 8'hbe, 8'hb0, 8'hea, 8'he4, 8'hf6, 8'hf8, 8'hd2, 8'hdc, 8'hce, 8'hc0,
  8'h7a, 8'h74, 8'h66, 8'h68, 8'h42, 8'h4c, 8'h5e, 8'h50, 8'h0A, 8'h04, 8'h16, 8'h18, 8'h32, 8'h3C, 8'h2E, 8'h20,
  8'hec, 8'he2, 8'hf0, 8'hfe, 8'hd4, 8'hda, 8'hc8, 8'hc6, 8'h9c, 8'h92, 8'h80, 8'h8e, 8'ha4, 8'haa, 8'hb8, 8'hb6,
  8'h0C, 8'h02, 8'h10, 8'h1E, 8'h34, 8'h3A, 8'h28, 8'h26, 8'h7c, 8'h72, 8'h60, 8'h6e, 8'h44, 8'h4a, 8'h58, 8'h56,
  8'h37, 8'h39, 8'h2b, 8'h25, 8'h0f, 8'h01, 8'h13, 8'h1d, 8'h47, 8'h49, 8'h5b, 8'h55, 8'h7f, 8'h71, 8'h63, 8'h6d,
  8'hd7, 8'hd9, 8'hcb, 8'hc5, 8'hef, 8'he1, 8'hf3, 8'hfd, 8'ha7, 8'ha9, 8'hbb, 8'hb5, 8'h9f, 8'h91, 8'h83, 8'h8d
};

//Get SBOX value of a word
function logic[31:0] get_sbox(input logic [31:0] index_word);
  logic [7:0] int_byte[0:3];
  logic [31:0] sbox_value;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = fv_sbox[index_word[i*8 +: 8]];

  sbox_value = {int_byte[0],int_byte[1],int_byte[2],int_byte[3]};

  return sbox_value;
endfunction

//Get Inverse SBOX value of a word
function logic[31:0] get_invsbox(input logic [31:0] index_word);
  logic [7:0] int_byte[0:3];
  logic [31:0] invsbox_value;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = fv_inv_sbox[index_word[i*8 +: 8]];

  invsbox_value = {int_byte[0],int_byte[1],int_byte[2],int_byte[3]};

  return invsbox_value;
endfunction

//Rotation of a word
function logic[31:0] get_rotate_word(input logic [31:0] index_word);
  logic [31:0] rotate_word;
  rotate_word = {index_word[23:0], index_word[31:24]};
  return rotate_word;
endfunction

//Get Rcon value
function logic[31:0] get_rcon(input logic [3:0] index);
  return fv_rcon[index];
endfunction

//Compute Keyexpansion for 128bit configuration
function logic [127 : 0] compute_key_expansion_128(input logic [127 : 0] fv_key_int, input logic [3 : 0] fv_round_int);
  logic [31:0] temp;
  logic [31:0] w[0:43];
  logic [127:0] fv_round_key[0:10];

  // The first four words are the original key
  for (int i = 0; i < 4; i++)
      w[3-i] = fv_key_int[i*32 +: 32];

  // Compute all words of roundkeys - total of 44 words for 11 keys
  for (int i = 4; i < 44; i++) begin
    temp = w[i-1];
    if (i % 4 == 0) begin
      temp = get_rotate_word(temp);
      temp = get_sbox(temp);
      temp = temp ^ get_rcon(i/4);
    end
    w[i] = w[i-4] ^ temp;
  end

  //Assign the round keys
  for (int i = 0; i < 11; i++)
      fv_round_key[i] = {w[i*4], w[i*4+1], w[i*4+2], w[i*4+3]};

  return  fv_round_key[fv_round_int];
endfunction

//Compute Keyexpansion for 256bit configuration
function logic [127 : 0] compute_key_expansion_256(input logic [255 : 0] fv_key_int, input logic [3 : 0] fv_round_int);
  logic [31:0] temp;
  logic [31:0] w[0:59];
  logic [127:0] fv_round_key[0:14];

  // The first eight words are the original key
  for (int i = 0; i < 8; i++)
      w[7-i] = fv_key_int[i*32 +: 32];

  // Compute all words of roundkeys - total of 60 words for 15 keys
  for (int i = 8; i < 60; i++) begin
    temp = w[i-1];
    if (i % 8 == 0) begin
      temp = get_rotate_word(temp);
      temp = get_sbox(temp);
      temp = temp ^ get_rcon(i/8);
      w[i] = w[i-8] ^ temp;
    end
    else if ((i - (i/8)*8) == 4) begin
      temp = get_sbox(temp);
      w[i] = w[i-8] ^ temp;
    end
    else begin
      w[i] = w[i-8] ^ w[i-1];
    end
  end

  //Assign the round keys
  for (int i = 0; i < 15; i++)
      fv_round_key[i] = {w[i*4], w[i*4+1], w[i*4+2], w[i*4+3]};

  return  fv_round_key[fv_round_int];
endfunction


//Compute MixColumns of the word
function logic[31:0] compute_mixcolums(input logic [31:0] index_word);
  logic [7:0] int_byte[0:3];
  logic [7:0] mixcolumn_byte[0:3];
  logic [31:0] mixcolumn_value;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = index_word[i*8 +: 8];

  mixcolumn_byte[0] = fv_gf2[int_byte[0]] ^ fv_gf3[int_byte[1]] ^ int_byte[2] ^ int_byte[3];
  mixcolumn_byte[1] = int_byte[0] ^ fv_gf2[int_byte[1]] ^ fv_gf3[int_byte[2]] ^ int_byte[3];
  mixcolumn_byte[2] = int_byte[0] ^ int_byte[1] ^ fv_gf2[int_byte[2]] ^ fv_gf3[int_byte[3]];
  mixcolumn_byte[3] = fv_gf3[int_byte[0]] ^ int_byte[1] ^ int_byte[2] ^ fv_gf2[int_byte[3]];

  mixcolumn_value = {mixcolumn_byte[0],mixcolumn_byte[1],mixcolumn_byte[2],mixcolumn_byte[3]};

  return mixcolumn_value;
endfunction

//Compute Inverse MixColumns of the word
function logic[31:0] compute_invmixcolums(input logic [31:0] index_word);
  logic [7:0] int_byte[0:3];
  logic [7:0] invmixcolumn_byte[0:3];
  logic [31:0] invmixcolumn_value;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = index_word[i*8 +: 8];

  invmixcolumn_byte[0] = fv_gfE[int_byte[0]] ^ fv_gfB[int_byte[1]] ^ fv_gfD[int_byte[2]] ^ fv_gf9[int_byte[3]];
  invmixcolumn_byte[1] = fv_gf9[int_byte[0]] ^ fv_gfE[int_byte[1]] ^ fv_gfB[int_byte[2]] ^ fv_gfD[int_byte[3]];
  invmixcolumn_byte[2] = fv_gfD[int_byte[0]] ^ fv_gf9[int_byte[1]] ^ fv_gfE[int_byte[2]] ^ fv_gfB[int_byte[3]];
  invmixcolumn_byte[3] = fv_gfB[int_byte[0]] ^ fv_gfD[int_byte[1]] ^ fv_gf9[int_byte[2]] ^ fv_gfE[int_byte[3]];

  invmixcolumn_value = {invmixcolumn_byte[0],invmixcolumn_byte[1],invmixcolumn_byte[2],invmixcolumn_byte[3]};

  return invmixcolumn_value;
endfunction

//Compute MixColumns of the msg
function logic[127:0] compute_mixcolums_msg(input logic [127:0] index_msg);
  logic [31:0] int_word[0:3], mix_word[0:3];
  logic [127:0] mixcolumn_msg;

  for (int i = 0; i < 4; i++)
    int_word[3-i] = index_msg[i*32 +: 32];

  //Column 0
  mix_word[0] = compute_mixcolums(int_word[0]);

  //Column 1
  mix_word[1] = compute_mixcolums(int_word[1]);

  //Column 2
  mix_word[2] = compute_mixcolums(int_word[2]);

  //Column 3
  mix_word[3] = compute_mixcolums(int_word[3]);

  mixcolumn_msg = {mix_word[0],mix_word[1],mix_word[2],mix_word[3]}; 

  return mixcolumn_msg;
endfunction

//Compute Inverse MixColumns of the msg
function logic[127:0] compute_invmixcolums_msg(input logic [127:0] index_msg);
  logic [31:0] int_word[0:3], invmix_word[0:3];
  logic [127:0] invmixcolumn_msg;

  for (int i = 0; i < 4; i++)
    int_word[3-i] = index_msg[i*32 +: 32];

  //Column 0
  invmix_word[0] = compute_invmixcolums(int_word[0]);

  //Column 1
  invmix_word[1] = compute_invmixcolums(int_word[1]);

  //Column 2
  invmix_word[2] = compute_invmixcolums(int_word[2]);

  //Column 3
  invmix_word[3] = compute_invmixcolums(int_word[3]);

  invmixcolumn_msg = {invmix_word[0],invmix_word[1],invmix_word[2],invmix_word[3]}; 

  return invmixcolumn_msg;
endfunction

//Compute AddRoundKey of index_msg with the key
function logic[127:0] compute_add_round_key(input logic [127:0] index_msg, input logic [127:0] index_key);
  return (index_msg ^ index_key);
endfunction

//Compute Shift row1
function logic [31 : 0] compute_shiftrow1(input logic [31 : 0] index_word);
  logic [7:0] int_byte[0:3];
  logic [31:0] shift_word;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = index_word[i*8 +: 8];
  
  shift_word = {int_byte[1],int_byte[2],int_byte[3],int_byte[0]};

  return shift_word;
endfunction

//Compute Inverse Shift row1
function logic [31 : 0] compute_invshiftrow1(input logic [31 : 0] index_word);
  logic [7:0] int_byte[0:3];
  logic [31:0] invshift_word;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = index_word[i*8 +: 8];
  
  invshift_word = {int_byte[3],int_byte[0],int_byte[1],int_byte[2]};

  return invshift_word;
endfunction

//Compute Shift row2
function logic [31 : 0] compute_shiftrow2(input logic [31 : 0] index_word);
  logic [7:0] int_byte[0:3];
  logic [31:0] shift_word;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = index_word[i*8 +: 8];
  
  shift_word = {int_byte[2],int_byte[3],int_byte[0],int_byte[1]};

  return shift_word;
endfunction

//Compute Inverse Shift row2
function logic [31 : 0] compute_invshiftrow2(input logic [31 : 0] index_word);
  logic [7:0] int_byte[0:3];
  logic [31:0] invshift_word;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = index_word[i*8 +: 8];
  
  invshift_word = {int_byte[2],int_byte[3],int_byte[0],int_byte[1]};

  return invshift_word;
endfunction

//Compute Shift row3
function logic [31 : 0] compute_shiftrow3(input logic [31 : 0] index_word);
  logic [7:0] int_byte[0:3];
  logic [31:0] shift_word;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = index_word[i*8 +: 8];
  
  shift_word = {int_byte[3],int_byte[0],int_byte[1],int_byte[2]};

  return shift_word;
endfunction

//Compute Inverse Shift row3
function logic [31 : 0] compute_invshiftrow3(input logic [31 : 0] index_word);
  logic [7:0] int_byte[0:3];
  logic [31:0] invshift_word;

  for (int i = 0; i < 4; i++)
    int_byte[3-i] = index_word[i*8 +: 8];
  
  invshift_word = {int_byte[1],int_byte[2],int_byte[3],int_byte[0]};

  return invshift_word;
endfunction

//Compute Shift rows
function logic [127 : 0] compute_shiftrow(input logic [127 : 0] index_msg);
  logic [31:0] int_word[0:3];
  logic [31:0] shift_word[0:3];
  logic [127:0] shift_msg;

  for (int i = 0; i < 4; i++)
    int_word[3-i] = index_msg[i*32 +: 32];

  //Row 0
  shift_word[0] = {int_word[0][31:24],int_word[1][31:24],int_word[2][31:24],int_word[3][31:24]};

  //Row 1
  shift_word[1] = {int_word[0][23:16],int_word[1][23:16],int_word[2][23:16],int_word[3][23:16]};
  shift_word[1] = compute_shiftrow1(shift_word[1]);

  //Row 2
  shift_word[2] = {int_word[0][15:8],int_word[1][15:8],int_word[2][15:8],int_word[3][15:8]};
  shift_word[2] = compute_shiftrow2(shift_word[2]);

  //Row 3
  shift_word[3] = {int_word[0][7:0],int_word[1][7:0],int_word[2][7:0],int_word[3][7:0]};
  shift_word[3] = compute_shiftrow3(shift_word[3]);

  //sent as a updated msg
  int_word[0] = {shift_word[0][31:24],shift_word[1][31:24],shift_word[2][31:24],shift_word[3][31:24]};
  int_word[1] = {shift_word[0][23:16],shift_word[1][23:16],shift_word[2][23:16],shift_word[3][23:16]};
  int_word[2] = {shift_word[0][15:8],shift_word[1][15:8],shift_word[2][15:8],shift_word[3][15:8]};
  int_word[3] = {shift_word[0][7:0],shift_word[1][7:0],shift_word[2][7:0],shift_word[3][7:0]};
  
  shift_msg = {int_word[0],int_word[1],int_word[2],int_word[3]}; 

  return shift_msg;
endfunction

//Compute Inverse Shift rows
function logic [127 : 0] compute_invshiftrow(input logic [127 : 0] index_msg);
  logic [31:0] int_word[0:3];
  logic [31:0] invshift_word[0:3];
  logic [127:0] invshift_msg;

  for (int i = 0; i < 4; i++)
    int_word[3-i] = index_msg[i*32 +: 32];

  //Row 0
  invshift_word[0] = {int_word[0][31:24],int_word[1][31:24],int_word[2][31:24],int_word[3][31:24]};

  //Row 1
  invshift_word[1] = {int_word[0][23:16],int_word[1][23:16],int_word[2][23:16],int_word[3][23:16]};
  invshift_word[1] = compute_invshiftrow1(invshift_word[1]);

  //Row 2
  invshift_word[2] = {int_word[0][15:8],int_word[1][15:8],int_word[2][15:8],int_word[3][15:8]};
  invshift_word[2] = compute_invshiftrow2(invshift_word[2]);

  //Row 3
  invshift_word[3] = {int_word[0][7:0],int_word[1][7:0],int_word[2][7:0],int_word[3][7:0]};
  invshift_word[3] = compute_invshiftrow3(invshift_word[3]);

  //sent as a updated msg
  int_word[0] = {invshift_word[0][31:24],invshift_word[1][31:24],invshift_word[2][31:24],invshift_word[3][31:24]};
  int_word[1] = {invshift_word[0][23:16],invshift_word[1][23:16],invshift_word[2][23:16],invshift_word[3][23:16]};
  int_word[2] = {invshift_word[0][15:8],invshift_word[1][15:8],invshift_word[2][15:8],invshift_word[3][15:8]};
  int_word[3] = {invshift_word[0][7:0],invshift_word[1][7:0],invshift_word[2][7:0],invshift_word[3][7:0]};
  
  invshift_msg = {int_word[0],int_word[1],int_word[2],int_word[3]}; 

  return invshift_msg;
endfunction

endpackage

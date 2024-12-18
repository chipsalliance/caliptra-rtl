// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "caliptra_prim_assert.sv"

/**
 * Data integrity encoder for bus integrity scheme
 */

module caliptra_tlul_data_integ_enc import caliptra_tlul_pkg::*; (
  // TL-UL interface
  input        [DataMaxWidth-1:0]               data_i,
  output logic [DataMaxWidth+DataIntgWidth-1:0] data_intg_o
);

  caliptra_prim_secded_inv_39_32_enc u_data_gen (
    .data_i,
    .data_o(data_intg_o)
  );

endmodule : caliptra_tlul_data_integ_enc

// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// key manager package
//

package keymgr_pkg;

  parameter int KeyWidth = 256;
  parameter int Shares = 2; // number of key shares

  // Key connection to various symmetric modules
  typedef struct packed {
    logic valid;
    logic [Shares-1:0][KeyWidth-1:0] key;
  } hw_key_req_t;

endpackage : keymgr_pkg

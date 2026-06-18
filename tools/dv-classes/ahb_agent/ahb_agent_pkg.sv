// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ahb_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  typedef enum bit [1:0] {
    TransIdle = 0,
    TransBusy = 1,
    TransNonSequential = 2,
    TransSequential = 3
  } trans_e;

  typedef enum bit [2:0] {
    BurstSingle = 0,
    BurstIncr   = 1,
    BurstWrap4  = 2,
    BurstIncr4  = 3,
    BurstWrap8  = 4,
    BurstIncr8  = 5,
    BurstWrap16 = 6,
    BurstIncr16 = 7
  } burst_e;

  `include "ahb_status_item.svh"
  `include "ahb_txn_request_item.svh"
  `include "ahb_txn_response_item.svh"

  `include "ahb_mgr_driver.svh"
endpackage

// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Package partition metadata.
//
// DO NOT EDIT THIS FILE DIRECTLY.
// It has been generated with ./util/design/gen-otp-mmap.py

package otp_ctrl_part_pkg;

  import prim_util_pkg::vbits;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;

  ////////////////////////////////////
  // Scrambling Constants and Types //
  ////////////////////////////////////

  parameter int NumScrmblKeys = 3;
  parameter int NumDigestSets = 4;

  parameter int ScrmblKeySelWidth = vbits(NumScrmblKeys);
  parameter int DigestSetSelWidth = vbits(NumDigestSets);
  parameter int ConstSelWidth = (ScrmblKeySelWidth > DigestSetSelWidth) ?
                                ScrmblKeySelWidth :
                                DigestSetSelWidth;

  typedef enum logic [ConstSelWidth-1:0] {
    StandardMode,
    ChainedMode
  } digest_mode_e;

  typedef logic [NumScrmblKeys-1:0][ScrmblKeyWidth-1:0] key_array_t;
  typedef logic [NumDigestSets-1:0][ScrmblKeyWidth-1:0] digest_const_array_t;
  typedef logic [NumDigestSets-1:0][ScrmblBlockWidth-1:0] digest_iv_array_t;

  typedef enum logic [ConstSelWidth-1:0] {
    Secret0Key,
    Secret1Key,
    Secret2Key
  } key_sel_e;

  typedef enum logic [ConstSelWidth-1:0] {
    CnstyDigest,
    FlashDataKey,
    FlashAddrKey,
    SramDataKey
  } digest_sel_e;

  // SEC_CM: SECRET.MEM.SCRAMBLE
  parameter key_array_t RndCnstKey = {
    128'h85A9E830BC059BA9286D6E2856A05CC3,
    128'hEFFA6D736C5EFF49AE7B70F9C46E5A62,
    128'h3BA121C5E097DDEB7768B4C666E9C3DA
  };

  // SEC_CM: PART.MEM.DIGEST
  // Note: digest set 0 is used for computing the partition digests. Constants at
  // higher indices are used to compute the scrambling keys.
  parameter digest_const_array_t RndCnstDigestConst = {
    128'h4A22D4B78FE0266FBEE3958332F2939B,
    128'hD60822E1FAEC5C7290C7F21F6224F027,
    128'h277195FC471E4B26B6641214B61D1B43,
    128'hE95F517CB98955B4D5A89AA9109294A
  };

  parameter digest_iv_array_t RndCnstDigestIV = {
    64'hF98C48B1F9377284,
    64'hB7474D640F8A7F5,
    64'hE048B657396B4B83,
    64'hBEAD91D5FA4E0915
  };


  /////////////////////////////////////
  // Typedefs for Partition Metadata //
  /////////////////////////////////////

  typedef enum logic [1:0] {
    Unbuffered,
    Buffered,
    LifeCycle
  } part_variant_e;

  typedef struct packed {
    part_variant_e variant;
    // Offset and size within the OTP array, in Bytes.
    logic [OtpByteAddrWidth-1:0] offset;
    logic [OtpByteAddrWidth-1:0] size;
    // Key index to use for scrambling.
    key_sel_e key_sel;
    // Attributes
    logic secret;           // Whether the partition is secret (and hence scrambled)
    logic sw_digest;        // Whether the partition has a software digest
    logic hw_digest;        // Whether the partition has a hardware digest
    logic write_lock;       // Whether the partition is write lockable (via digest)
    logic read_lock;        // Whether the partition is read lockable (via digest)
    logic integrity;        // Whether the partition is integrity protected
    logic iskeymgr_creator; // Whether the partition has any creator key material
    logic iskeymgr_owner;   // Whether the partition has any owner key material
  } part_info_t;

  parameter part_info_t PartInfoDefault = '{
      variant:          Unbuffered,
      offset:           '0,
      size:             OtpByteAddrWidth'('hFF),
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b0,
      write_lock:       1'b0,
      read_lock:        1'b0,
      integrity:        1'b0,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0
  };

  ////////////////////////
  // Partition Metadata //
  ////////////////////////

  localparam part_info_t PartInfo [NumPart] = '{
    // VENDOR_TEST
    '{
      variant:          Unbuffered,
      offset:           12'd0,
      size:             64,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b0,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0
    },
    // NON_SECRET_FUSES
    '{
      variant:          Unbuffered,
      offset:           12'd64,
      size:             3792,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0
    },
    // SECRET0
    '{
      variant:          Buffered,
      offset:           12'd3856,
      size:             56,
      key_sel:          Secret0Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0
    },
    // SECRET1
    '{
      variant:          Buffered,
      offset:           12'd3912,
      size:             40,
      key_sel:          Secret1Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0
    },
    // SECRET2
    '{
      variant:          Buffered,
      offset:           12'd3952,
      size:             56,
      key_sel:          Secret2Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0
    },
    // LIFE_CYCLE
    '{
      variant:          LifeCycle,
      offset:           12'd4008,
      size:             88,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b0,
      write_lock:       1'b0,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0
    }
  };

  typedef enum {
    VendorTestIdx,
    NonSecretFusesIdx,
    Secret0Idx,
    Secret1Idx,
    Secret2Idx,
    LifeCycleIdx,
    // These are not "real partitions", but in terms of implementation it is convenient to
    // add these at the end of certain arrays.
    DaiIdx,
    LciIdx,
    KdiIdx,
    // Number of agents is the last idx+1.
    NumAgentsIdx
  } part_idx_e;

  parameter int NumAgents = int'(NumAgentsIdx);

  // Breakout types for easier access of individual items.
  typedef struct packed {
    // This reuses the same encoding as the life cycle signals for indicating valid status.
    lc_ctrl_pkg::lc_tx_t valid;
  } otp_broadcast_t;

  // default value for intermodule
  parameter otp_broadcast_t OTP_BROADCAST_DEFAULT = '{
    valid: lc_ctrl_pkg::Off,
  };


  // OTP invalid partition default for buffered partitions.
  parameter logic [32767:0] PartInvDefault = 32768'({
    704'({
      320'h55D0320379A0D260426D99D374E699CAE00E9680BD9B70291C752824C7DDC89694CD3DED94B57819,
      384'hDBC827839FE2DCC27E17D06B5D4E0DDDDBB9844327F20FB5D396D1CE085BDC31105733EAA3880C5A234729143F97B62A
    }),
    448'({
      64'hD3D58610F4851667,
      384'h0
    }),
    320'({
      64'h5E58D0AA97A0F8F6,
      256'h0
    }),
    448'({
      64'h2C0DBDDEDF7A854D,
      384'h0
    }),
    30336'({
      64'hD0BAC511D08ECE0E,
      28704'h0, // unallocated space
      32'h0,
      128'h0,
      768'h63B9485A3856C417CF7A50A9A91EF7F7B3A5B4421F462370FFF698183664DC7EDF3888886BD10DC67ABB319BDA0529AE40119A3C6E63CDF358840E458E4029A6B5AC1F53D00A08C3B28B5C0FEE5F4C02711D135F59A50322B6711DB6F5D40A37,
      384'h0,
      32'h0,
      32'h0,
      32'h0,
      128'h0,
      32'h0
    }),
    512'({
      64'h2A4D8B51F5D41C8A,
      448'h0
    })});

  ///////////////////////////////////////////////
  // Parameterized Assignment Helper Functions //
  ///////////////////////////////////////////////

  function automatic otp_ctrl_core_hw2reg_t named_reg_assign(
      logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest);
    otp_ctrl_core_hw2reg_t hw2reg;
    logic unused_sigs;
    unused_sigs = ^part_digest;
    hw2reg = '0;
    hw2reg.vendor_test_digest = part_digest[VendorTestIdx];
    hw2reg.non_secret_fuses_digest = part_digest[NonSecretFusesIdx];
    hw2reg.secret0_digest = part_digest[Secret0Idx];
    hw2reg.secret1_digest = part_digest[Secret1Idx];
    hw2reg.secret2_digest = part_digest[Secret2Idx];
    return hw2reg;
  endfunction : named_reg_assign

  function automatic part_access_t [NumPart-1:0] named_part_access_pre(
      otp_ctrl_core_reg2hw_t reg2hw);
    part_access_t [NumPart-1:0] part_access_pre;
    logic unused_sigs;
    unused_sigs = ^reg2hw;
    // Default (this will be overridden by partition-internal settings).
    part_access_pre = {{32'(2*NumPart)}{prim_mubi_pkg::MuBi8False}};
    // Note: these could be made a MuBi CSRs in the future.
    // The main thing that is missing right now is proper support for W0C.
    // VENDOR_TEST
    if (!reg2hw.vendor_test_read_lock) begin
      part_access_pre[VendorTestIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // NON_SECRET_FUSES
    if (!reg2hw.non_secret_fuses_read_lock) begin
      part_access_pre[NonSecretFusesIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    return part_access_pre;
  endfunction : named_part_access_pre

  function automatic otp_broadcast_t named_broadcast_assign(
      logic [NumPart-1:0] part_init_done,
      logic [$bits(PartInvDefault)/8-1:0][7:0] part_buf_data);
    otp_broadcast_t otp_broadcast;
    logic valid, unused;
    unused = 1'b0;
    valid = 1'b1;
    // VENDOR_TEST
    unused ^= ^{part_init_done[VendorTestIdx],
                part_buf_data[VendorTestOffset +: VendorTestSize]};
    // NON_SECRET_FUSES
    unused ^= ^{part_init_done[NonSecretFusesIdx],
                part_buf_data[NonSecretFusesOffset +: NonSecretFusesSize]};
    // SECRET0
    unused ^= ^{part_init_done[Secret0Idx],
                part_buf_data[Secret0Offset +: Secret0Size]};
    // SECRET1
    unused ^= ^{part_init_done[Secret1Idx],
                part_buf_data[Secret1Offset +: Secret1Size]};
    // SECRET2
    unused ^= ^{part_init_done[Secret2Idx],
                part_buf_data[Secret2Offset +: Secret2Size]};
    // LIFE_CYCLE
    unused ^= ^{part_init_done[LifeCycleIdx],
                part_buf_data[LifeCycleOffset +: LifeCycleSize]};
    otp_broadcast.valid = lc_ctrl_pkg::lc_tx_bool_to_lc_tx(valid);
    return otp_broadcast;
  endfunction : named_broadcast_assign

  function automatic otp_keymgr_key_t named_keymgr_key_assign(
      logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest,
      logic [$bits(PartInvDefault)/8-1:0][7:0] part_buf_data,
      lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en);
    otp_keymgr_key_t otp_keymgr_key;
    logic valid, unused;
    unused = 1'b0;
    // For now we use a fixed struct type here so that the
    // interface to the keymgr remains stable. The type contains
    // a superset of all options, so we have to initialize it to '0 here.
    otp_keymgr_key = '0;
    // VENDOR_TEST
    unused ^= ^{part_digest[VendorTestIdx],
                part_buf_data[VendorTestOffset +: VendorTestSize]};
    // NON_SECRET_FUSES
    unused ^= ^{part_digest[NonSecretFusesIdx],
                part_buf_data[NonSecretFusesOffset +: NonSecretFusesSize]};
    // SECRET0
    unused ^= ^{part_digest[Secret0Idx],
                part_buf_data[Secret0Offset +: Secret0Size]};
    // SECRET1
    unused ^= ^{part_digest[Secret1Idx],
                part_buf_data[Secret1Offset +: Secret1Size]};
    // SECRET2
    unused ^= ^{part_digest[Secret2Idx],
                part_buf_data[Secret2Offset +: Secret2Size]};
    // LIFE_CYCLE
    unused ^= ^{part_digest[LifeCycleIdx],
                part_buf_data[LifeCycleOffset +: LifeCycleSize]};
    unused ^= valid;
    return otp_keymgr_key;
  endfunction : named_keymgr_key_assign

endpackage : otp_ctrl_part_pkg

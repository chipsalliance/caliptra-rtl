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
//======================================================================



// Declarations for internal signal probing  
logic [31:0] fuse_uds_seed [0:11]; 
logic [31:0] fuse_field_entropy [0:7]; 
logic [31:0] fuse_key_manifest_pk_hash [0:11]; 
logic [3:0]  fuse_key_manifest_pk_hash_mask[0:7]; 
logic [31:0] fuse_fmc_key_manifest_svn; 
logic [31:0] fuse_runtime_svn [0:3]; 
logic        fuse_anti_rollback_disable; 
logic [31:0] fuse_idevid_cert_attr [0:23]; 
logic [31:0] fuse_idevid_manuf_hsm_id [0:3]; 
logic [31:0] fuse_lms_revocation; 
logic [31:0] fuse_mldsa_revocation; 


`FORLOOP_COMB( 12 ) fuse_uds_seed[j]                  = `REG_HIER_PFX.fuse_uds_seed[j].seed.value;
`FORLOOP_COMB( 8 )  fuse_field_entropy[j]             = `REG_HIER_PFX.fuse_field_entropy[j].seed.value;
`FORLOOP_COMB( 12 ) fuse_key_manifest_pk_hash[j]      = `REG_HIER_PFX.fuse_key_manifest_pk_hash[j].hash.value;
`FORLOOP_COMB( 8 )  fuse_key_manifest_pk_hash_mask[j] = `REG_HIER_PFX.fuse_key_manifest_pk_hash_mask[j].mask.value;
  //always_comb       fuse_key_manifest_pk_hash_mask    = `REG_HIER_PFX.fuse_key_manifest_pk_hash_mask.mask.value;
  always_comb       fuse_fmc_key_manifest_svn         = `REG_HIER_PFX.fuse_fmc_key_manifest_svn.svn.value;
`FORLOOP_COMB( 4 )  fuse_runtime_svn[j]               = `REG_HIER_PFX.fuse_runtime_svn[j].svn.value;
  always_comb       fuse_anti_rollback_disable        = `REG_HIER_PFX.fuse_anti_rollback_disable.dis.value;
`FORLOOP_COMB( 24 ) fuse_idevid_cert_attr[j]          = `REG_HIER_PFX.fuse_idevid_cert_attr[j].cert.value;
`FORLOOP_COMB( 4 )  fuse_idevid_manuf_hsm_id[j]       = `REG_HIER_PFX.fuse_idevid_manuf_hsm_id[j].hsm_id.value;
  always_comb       fuse_lms_revocation               = `REG_HIER_PFX.fuse_lms_revocation.lms_revocation.value;
  always_comb       fuse_mldsa_revocation             = `REG_HIER_PFX.fuse_mldsa_revocation.mldsa_revocation.value;


//----------------------------------------------------------------
// fuse_reg_axi_user_test()
// 
// Checks fuse permission tests depending on PAUSER bit status 
//----------------------------------------------------------------
task fuse_reg_axi_user_test;
  // Fuse Register AXI-USER Test 

  automatic word_addr_t addr; 
  automatic int tid = 0; // optional to increment UNLESS multiple writes to same address 
  automatic strq_t fuse_regnames;  // ordered list of fuse register names
  automatic dwordq_t fuse_regdata;  // corresponding data to fuse register names
  automatic dword_t valid_axi_user;  
  automatic logic lock_status;
  automatic WordTransaction wrtrans, rdtrans;
  automatic string rname;
  automatic dword_t fuse_regval_actual;  

  begin
    $display("-----------------------------------\n");
    $display("Executing task fuse_reg_axi_user_test"); 
    $display("-----------------------------------\n");

    $display("Current security state = 0b%03b", security_state);
    tc_ctr = tc_ctr + 1;

    wrtrans = new();
    rdtrans = new();

    fuse_regnames = get_fuse_regnames_minus_ss_straps(); 

    /*
    foreach (fuse_regnames[ix]) begin
      $display("CUrrent fuse: %s", fuse_regnames[ix]);
      $display(fuse_regnames[ix] == "SS_DBG_MANUF_SERVICE_REG_RSP");
      if ((fuse_regnames[ix] == "SS_DBG_MANUF_SERVICE_REG_REQ") || // Writeable by SOC
          (fuse_regnames[ix] == "SS_DBG_MANUF_SERVICE_REG_RSP") || // Writeable by Caliptra
          (fuse_regnames[ix] == "SS_DEBUG_INTENT")) begin //writeable only by TAP
        $display("Found %s", fuse_regnames[ix]);
        fuse_regnames.delete(ix);  // Writeable only when SS_DBG_INTENT = 1
        continue; 
      end
    end 

    // SS_DBG_MANUF_SERVICE_REG_RSP is not getting deleted in the above loop. 
    // Deleting it explicitly for now
    del_from_strq(fuse_regnames, "SS_DBG_MANUF_SERVICE_REG_RSP"); // SS_DBG_MANUF_SERVICE_REG_RSP

    foreach (fuse_regnames[ix]) begin
      if ((fuse_regnames[ix] == "SS_GENERIC_FW_EXEC_CTRL") || 
          (fuse_regnames[ix] == "SS_SOC_DBG_UNLOCK_LEVEL") ||
          (fuse_regnames[ix] == "CPTRA_CAP_LOCK") ||
          (fuse_regnames[ix] == "CPTRA_FW_CAPABILITIES") ||
          (fuse_regnames[ix] == "CPTRA_HW_CAPABILITIES")) begin
        fuse_regnames.delete(ix);  // SOC read-only
        continue; 
      end
    end
      */

    init_sim();
    reset_dut();

    wait (ready_for_fuses); 

    //------------------------------------------------------------------------------------------- 
    print_banner("1a. Default axi user and unlocked. AXI write to registers, check values");
    tphase = "1a";

    write_regs(SET_AXI, fuse_regnames, tid, 3);  // effect changes & 
    repeat (5) @(posedge clk_tb);
    read_regs(GET_AXI, fuse_regnames, tid, 3);  // expect same values on read

    //------------------------------------------------------------------------------------------- 
    print_banner("1b. With unlocked non-default axi_user, repeat 1a");
    tphase = "1b";

    // NOTE. simulate_caliptra_boot() is necessary for noncore_rst_b to be deasserted
    //simulate_caliptra_boot();
    //wait (cptra_noncore_rst_b_tb == 1'b1);

    // Set axi_user valid to non-default
    wrtrans.update_byname("CPTRA_FUSE_VALID_AXI_USER", 0, tid); 
    wrtrans.randomize();
    valid_axi_user = wrtrans.data;
    write_reg_trans(SET_AXI, wrtrans);
    repeat (3) @(posedge clk_tb);
    rdtrans.update_byname("CPTRA_FUSE_VALID_AXI_USER", 0, tid); 
    read_reg_trans(GET_AXI, rdtrans);
    $display ("Pauser value programmed = 0x%08x", rdtrans.data); 
    assert (rdtrans.data == valid_axi_user) else begin
      $display("TB ERROR. fuse_pauser_valid modfication failed"); 
      error_ctr += 1;
    end 

    write_regs(SET_AXI, fuse_regnames, tid, 3);  // effect changes & 
    repeat (5) @(posedge clk_tb);
    read_regs(GET_AXI, fuse_regnames, tid, 3);  // expect same values on read

    //------------------------------------------------------------------------------------------- 
    print_banner("1c. Lock axi_user with non-default value. repeat 1a but read with and w/o valid axi_user"); 
    tphase = "1c";

    set_fuse_axi_user_lock(1'b1, tid, lock_status);
    if (lock_status == 1'b0) begin
      $display("TB ERROR. Setting fuse_pauser_lock failed!"); 
      error_ctr += 1;
    end

    $display ("TB INFO. Storing last modified fuse register values with valid pauser writes"); 
    foreach (fuse_regnames[i]) begin   // store last-modified values
      rname = fuse_regnames[i];
      fuse_regval_actual = get_fuse_regval(rname);
      fuse_regdata.push_back(fuse_regval_actual);
      $display ("TB INFO. For %-30s storing last modified value 0x%08x", rname, fuse_regval_actual);
    end 

    write_regs(SET_AXI, fuse_regnames, tid, 3, FAIL);  // should be ineffectual 
    repeat (5) @(posedge clk_tb);

    // Read twice, with and without valid pauser
    foreach (fuse_regnames[i]) begin
      rname = fuse_regnames[i];
      rdtrans.update_byname(rname,  0, tid); 
      fuse_regval_actual = get_fuse_regval(rname);
      read_reg_chk_inrange(GET_AXI, rname, tid, '0, '0, FAIL);  // get 0's on default pauser, and AXI read error
      repeat (3) @(posedge clk_tb);
      read_reg_trans(GET_AXI, rdtrans, valid_axi_user); // expect older (stored) values
      repeat (3) @(posedge clk_tb);

      if (str_startswith(rname, "FUSE_UDS_SEED") || str_startswith(rname, "FUSE_FIELD_ENTROPY")) 
        assert (rdtrans.data == '0) else error_ctr += 1;
        continue;

      if (rdtrans.data != fuse_regval_actual) begin
        $display("TB ERROR. Mismatch on AXI read w/valid axi_user for reg %-30s (0x%08x). Read value = 0x%08x | expected probed = 0x%08x", 
          rname, rdtrans.addr, rdtrans.data, fuse_regval_actual) ;
        error_ctr += 1;
      end
      @(posedge clk_tb);
    end


    //------------------------------------------------------------------------------------------- 
    print_banner("1d. With matching locked non-default axi_user, repeat 1a"); 
    tphase = "1d";

    // Programming a non-default valid_axi_user and locking it requires waiting for cptra_noncore_rst_b 
    // to be deasserted after a reset, ie, Caliptra boot. 
    //  
    // At the same time ready_for_fuses drops low followed by cptra_noncore_rst_b goingh high, ergo 
    // writes to fuse regs no longer work (for any pauser value) until a warm reset occurs. 
    // HOWEVER, a warm reset also resets the valid_axi_user register. 
    // 
    // The net result (a bug) is that fuse registers can ONLY be written using a default pauser value; 
    // fuse registers can be read out though using any programmed and locked valid_axi_user.  
   
    sb.del_all();  

    foreach (fuse_regnames[i]) begin
      rname = fuse_regnames[i];
      wrtrans.update_byname(rname, 0, tid);
      wrtrans.randomize();
      rdtrans.update_byname(rname, 0, tid);

      write_reg_trans(SET_AXI, wrtrans, valid_axi_user); 
      @(posedge clk_tb);
      read_reg_trans(GET_AXI, rdtrans, valid_axi_user); 
      repeat (3) @(posedge clk_tb);

      if (str_startswith(rname, "FUSE_UDS_SEED") || str_startswith(rname, "FUSE_FIELD_ENTROPY")) 
        continue;

      if (rdtrans.data != (get_mask(rname) & wrtrans.data)) begin
        $display("TB ERROR. Mismatch on AXI write and read w/valid axi_user for reg %-30s (0x%08x). Read value = 0x%08x | expected value = 0x%08x", 
          rname, rdtrans.addr, rdtrans.data, get_mask(rname) & wrtrans.data); 
        error_ctr += 1;
      end

      repeat (3) @(posedge clk_tb);
    end 


    //------------------------------------------------------------------------------------------- 
    print_banner("2a. for completeness try to unlock axi user by writing"); 
    tphase = "2a";

    set_fuse_axi_user_lock(1'b0, tid, lock_status);
    assert (lock_status == 1'b1) else begin
      $display("TB ERROR. Resetting of fuse_axi_user_lock via AXI was allowed!"); 
      error_ctr += 1;
    end


    //------------------------------------------------------------------------------------------- 
    print_banner("2b. then attempt to unlock axi user by warm resetting"); 
    tphase = "2b";

    warm_reset_dut(); 
    warm_reset_exp_data();
    sb.del_all();

    simulate_caliptra_boot();
    wait (cptra_noncore_rst_b_tb == 1'b1);

    // if (cptra_noncore_rst_b_tb == 1'b0) begin
    //   $display("TB. WARNING Non core reset is not deasserted. Waiting 1000 cycles");
    //   repeat (1000) @(posedge clk_tb);
    //   $display("TB. DEBUG if status of cptra_noncore_rst_b_tb = 1'b%b", cptra_noncore_rst_b_tb); 
    // end

    read_reg_chk_inrange(GET_AXI, "CPTRA_FUSE_AXI_USER_LOCK", tid, 'd1, 'd1); 
    @(posedge clk_tb);


    //------------------------------------------------------------------------------------------- 
    print_banner("2c. finally unlock axi user by cold reseting"); 
    tphase = "2c";

    reset_dut(); // expect to be clearing CPTRA_FUSE_WR_DONE effect 
    reset_exp_data();
    // simulate_caliptra_boot();
    sb.del_all();

    simulate_caliptra_boot();
    $display("Wait for cptra_noncore_rst_b_tb == 1");
    wait (cptra_noncore_rst_b_tb == 1'b1);

    // if (cptra_noncore_rst_b_tb == 1'b0) begin
    //   $display("TB. WARNING Non core reset is not deasserted. Waiting 1000 cycles");
    //   repeat (1000) @(posedge clk_tb);
    //   $display("TB. DEBUG if status of cptra_noncore_rst_b_tb = 1'b%b", cptra_noncore_rst_b_tb); 
    // end

    read_reg_chk_inrange(GET_AXI, "CPTRA_FUSE_AXI_USER_LOCK", tid, '0, '0); 
    @(posedge clk_tb);


    error_ctr += sb.err_count;
    //$display("End of fuse_reg_axi_user_test. Error count = %d", error_ctr);

  end

endtask // fuse_reg_pauser_test



//----------------------------------------------------------------
// function get_fuse_regval()
//
// Probes to get the internal fuse register value inside dut 
//----------------------------------------------------------------
function dword_t get_fuse_regval(string rname);

  automatic dword_t regval; 
  string pfx = "unknown";
  automatic int j; 

  strq_t prefixes = {"FUSE_UDS_SEED", "FUSE_FIELD_ENTROPY", "FUSE_KEY_MANIFEST_PK_HASH",  
   "FUSE_RUNTIME_SVN", "FUSE_IDEVID_CERT_ATTR", "FUSE_IDEVID_MANUF_HSM_ID"}; 

  begin
    case (rname) 
      //"FUSE_KEY_MANIFEST_PK_HASH_MASK"      :  regval = fuse_key_manifest_pk_hash_mask; 
      "FUSE_FMC_KEY_MANIFEST_SVN"           :  regval = fuse_fmc_key_manifest_svn; 
      "FUSE_ANTI_ROLLBACK_DISABLE"          :  regval = fuse_anti_rollback_disable; 
      "FUSE_LMS_REVOCATION"                 :  regval = fuse_lms_revocation; 
      "FUSE_MLDSA_REVOCATION"               :  regval = fuse_mldsa_revocation; 

      default: begin
        foreach (prefixes[i]) begin
          if (str_startswith(rname, prefixes[i])) begin
            pfx = prefixes[i];
            break;
          end
        end

        if (pfx == "unknown") begin 
          $display ("TB ERROR. Unknown prefix in fuse register name %s", rname);
          error_ctr += 1;
        end else begin
          j = `STR_RMPFX(rname, pfx);
          // $display ("prefix = %s, j = %d", pfx, j);
          regval =  (pfx == "FUSE_UDS_SEED"            ) ? fuse_uds_seed[j]:
                    (pfx == "FUSE_FIELD_ENTROPY"       ) ? fuse_field_entropy[j] :
                    (pfx == "FUSE_KEY_MANIFEST_PK_HASH") ? fuse_key_manifest_pk_hash[j] :
                    (pfx == "FUSE_KEY_MANIFEST_PK_HASH_MASK") ? fuse_key_manifest_pk_hash_mask[j] :
                    (pfx == "FUSE_RUNTIME_SVN"         ) ? fuse_runtime_svn[j] :
                    (pfx == "FUSE_IDEVID_CERT_ATTR"    ) ? fuse_idevid_cert_attr[j] :
                    (pfx == "FUSE_IDEVID_MANUF_HSM_ID" ) ? fuse_idevid_manuf_hsm_id[j] : 'x;
        end
      end

    endcase

    return regval;
  end

endfunction // get_fuse_regval


//----------------------------------------------------------------
// task set_fuse_axi_user_lock()
//
// Sets fuse axi user lock register & checks value
//----------------------------------------------------------------
task set_fuse_axi_user_lock(input logic lock_value, input int tid, output logic lock_status); 

  automatic WordTransaction wrtrans, rdtrans;
  begin
    wrtrans = new();
    rdtrans = new();

    wrtrans.update_byname("CPTRA_FUSE_AXI_USER_LOCK", lock_value, tid); 
    write_reg_trans(SET_AXI, wrtrans);
    repeat (3) @(posedge clk_tb);
    rdtrans.update_byname("CPTRA_FUSE_AXI_USER_LOCK", 0, tid); 
    read_reg_trans(GET_AXI, rdtrans); // FIXME.
    $display ("AXI user lock status = 0x%08x", rdtrans.data); 

    lock_status = rdtrans.data[0];
  end
endtask // set_fuse_axi_user_lock


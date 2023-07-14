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


`define FORLOOP_COMB(x) always_comb for (int j = 0; j < x; j++) 
`define REG_HIER_PFX dut.i_soc_ifc_reg.field_storage
`define STR_RMPFX(astr, bstr) astr.substr(bstr.len(), astr.len() - 1).atoi()


// Declarations for internal signal probing  
logic [31:0] fuse_uds_seed [0:11]; 
logic [31:0] fuse_field_entropy [0:7]; 
logic [31:0] fuse_key_manifest_pk_hash [0:11]; 
logic [3:0]  fuse_key_manifest_pk_hash_mask; 
logic [31:0] fuse_owner_pk_hash [0:11]; 
logic [31:0] fuse_fmc_key_manifest_svn; 
logic [31:0] fuse_runtime_svn [0:3]; 
logic        fuse_anti_rollback_disable; 
logic [31:0] fuse_idevid_cert_attr [0:23]; 
logic [31:0] fuse_idevid_manuf_hsm_id [0:3]; 
logic [1:0]  fuse_life_cycle ; 
logic        fuse_lms_verify ; 
logic [31:0] fuse_lms_revocation; 


`FORLOOP_COMB( 12 ) fuse_uds_seed[j]                  = `REG_HIER_PFX.fuse_uds_seed[j].seed.value;
`FORLOOP_COMB( 8 )  fuse_field_entropy[j]             = `REG_HIER_PFX.fuse_field_entropy[j].seed.value;
`FORLOOP_COMB( 12 ) fuse_key_manifest_pk_hash[j]      = `REG_HIER_PFX.fuse_key_manifest_pk_hash[j].hash.value;
  always_comb       fuse_key_manifest_pk_hash_mask    = `REG_HIER_PFX.fuse_key_manifest_pk_hash_mask.mask.value;
`FORLOOP_COMB( 12 ) fuse_owner_pk_hash[j]             = `REG_HIER_PFX.fuse_owner_pk_hash[j].hash.value;
  always_comb       fuse_fmc_key_manifest_svn         = `REG_HIER_PFX.fuse_fmc_key_manifest_svn.svn.value;
`FORLOOP_COMB( 4 )  fuse_runtime_svn[j]               = `REG_HIER_PFX.fuse_runtime_svn[j].svn.value;
  always_comb       fuse_anti_rollback_disable        = `REG_HIER_PFX.fuse_anti_rollback_disable.dis.value;
`FORLOOP_COMB( 24 ) fuse_idevid_cert_attr[j]          = `REG_HIER_PFX.fuse_idevid_cert_attr[j].cert.value;
`FORLOOP_COMB( 4 )  fuse_idevid_manuf_hsm_id[j]       = `REG_HIER_PFX.fuse_idevid_manuf_hsm_id[j].hsm_id.value;
  always_comb       fuse_life_cycle                   = `REG_HIER_PFX.fuse_life_cycle.life_cycle.value;
  always_comb       fuse_lms_verify                   = `REG_HIER_PFX.fuse_lms_verify.lms_verify.value;
  always_comb       fuse_lms_revocation               = `REG_HIER_PFX.fuse_lms_revocation.lms_revocation.value;


//----------------------------------------------------------------
// fuse_reg_pauser_test()
// 
// Checks fuse permission tests depending on PAUSER bit status 
//----------------------------------------------------------------
task fuse_reg_pauser_test;
  // Fuse Register PA-USER Test 

  automatic word_addr_t addr; 
  automatic int tid = 0; // optional to increment UNLESS multiple writes to same address 
  automatic strq_t fuse_regnames;  // ordered list of fuse register names
  automatic dwordq_t fuse_regdata;  // corresponding data to fuse register names
  automatic dword_t valid_pauser;  
  automatic logic lock_status;
  automatic WordTransaction wrtrans, rdtrans;
  automatic string rname;
  automatic dword_t fuse_regval_actual;  

  begin
    $display("Executing task fuse_reg_pauser_test"); 
    $display("-----------------------------------\n");

    $display("Current security state = 0b%03b", security_state);
    tc_ctr = tc_ctr + 1;

    wrtrans = new();
    rdtrans = new();

    fuse_regnames = get_fuse_regnames(); 

    init_sim();
    reset_dut();

    //------------------------------------------------------------------------------------------- 
    print_banner("1a. Default pauser and unlocked. APB write to registers, check values");
    tphase = "1a";

    write_regs(SET_APB, fuse_regnames, tid, 3);  // effect changes & expec same values on read
    repeat (5) @(posedge clk_tb);
    read_regs(GET_APB, fuse_regnames, tid, 3);  

    //------------------------------------------------------------------------------------------- 
    print_banner("1b. With unlocked non-default pauser, repeat 1a");
    tphase = "1b";

    // Set pauser valid to non-default
    wrtrans.update_byname("CPTRA_FUSE_VALID_PAUSER", 0, tid); 
    wrtrans.randomize();
    valid_pauser = wrtrans.data;
    write_reg_trans(SET_APB, wrtrans);
    repeat (3) @(posedge clk_tb);
    rdtrans.update_byname("CPTRA_FUSE_VALID_PAUSER", 0, tid); 
    read_reg_trans(GET_APB, rdtrans);
    $display ("Pauser value programmed = 0x%08x", rdtrans.data); 
    assert (rdtrans.data == valid_pauser) else begin
      $display("TB ERROR. fuse_pauser_valid modfication failed"); 
      error_ctr += 1;
    end 

    write_regs(SET_APB, fuse_regnames, tid, 3);  // effect changes
    repeat (5) @(posedge clk_tb);
    read_regs(GET_APB, fuse_regnames, tid, 3);  

    //------------------------------------------------------------------------------------------- 
    print_banner("1c. Lock pauser with non-default value. repeat 1a but read with and w/o valid pauser"); 
    tphase = "1c";

    set_fuse_pauser_lock(1'b1, tid, lock_status);
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

    write_regs(SET_APB, fuse_regnames, tid, 3);  // should be ineffectual 
    repeat (5) @(posedge clk_tb);

    // Read twice, with and without valid pauser
    foreach (fuse_regnames[i]) begin
      rname = fuse_regnames[i];
      rdtrans.update_byname(rname,  0, tid); 
      fuse_regval_actual = get_fuse_regval(rname);
      read_reg_chk_inrange(GET_APB, rname, tid, '0, '0);  // get 0's on default pauser
      repeat (3) @(posedge clk_tb);
      read_reg_trans(GET_APB, rdtrans, valid_pauser); 
      repeat (3) @(posedge clk_tb);

      if (str_startswith(rname, "FUSE_UDS_SEED") || str_startswith(rname, "FUSE_FIELD_ENTROPY")) 
        assert (rdtrans.data == '0) else error_ctr += 1;
        continue;

      if (rdtrans.data != fuse_regval_actual) begin
        $display("TB ERROR. Mismatch on APB read w/valid pauser for reg %-30s (0x%08x). Read value = 0x%08x | expected probed = 0x%08x", 
          rname, rdtrans.addr, rdtrans.data, fuse_regval_actual) ;
        error_ctr += 1;
      end
      @(posedge clk_tb);
    end


    //------------------------------------------------------------------------------------------- 
    print_banner("1d. With matching locked non-default pauser, repeat 1a"); 
    tphase = "1d";

    sb.del_all();  // Fresh scoreboard start (except for errors)

    foreach (fuse_regnames[i]) begin
      rname = fuse_regnames[i];
      wrtrans.update_byname(rname, 0, tid);
      wrtrans.randomize();
      rdtrans.update_byname(rname, 0, tid);

      write_reg_trans(SET_APB, wrtrans, valid_pauser); 
      @(posedge clk_tb);
      read_reg_trans(GET_APB, rdtrans, valid_pauser); 
      repeat (3) @(posedge clk_tb);

      if (str_startswith(rname, "FUSE_UDS_SEED") || str_startswith(rname, "FUSE_FIELD_ENTROPY")) 
        continue;

      if (rdtrans.data != (get_mask(rname) & wrtrans.data)) begin
        $display("TB ERROR. Mismatch on APB write and read w/valid pauser for reg %-30s (0x%08x). Masked Write value = 0x%08x | expected Read value = 0x%08x", 
          rname, rdtrans.addr, get_mask(rname) & wrtrans.data, rdtrans.data); 
        error_ctr += 1;
      end

      repeat (3) @(posedge clk_tb);
    end 


    //------------------------------------------------------------------------------------------- 
    print_banner("2a. for completeness try to unlock pauser by writing"); 
    tphase = "2a";

    set_fuse_pauser_lock(1'b0, tid, lock_status);
    assert (lock_status == 1'b1) else begin
      $display("TB ERROR. Resetting of fuse_pauser_lock via APB was allowed!"); 
      error_ctr += 1;
    end


    //------------------------------------------------------------------------------------------- 
    print_banner("2b. then attempt to unlock pauser by warm reseting"); 
    tphase = "2b";

    warm_reset_dut(); 
    reset_exp_data();
    sb.del_all();

    read_reg_chk_inrange(GET_APB, "CPTRA_FUSE_PAUSER_LOCK", tid, '0, '0); 
    @(posedge clk_tb);


    //------------------------------------------------------------------------------------------- 
    print_banner("2c. finally unlock pauser by cold reseting"); 
    tphase = "2c";

    reset_dut(); // expect to be clearing CPTRA_FUSE_WR_DONE effect 
    reset_exp_data();
    // simulate_caliptra_boot();
    sb.del_all();

    read_reg_chk_inrange(GET_APB, "CPTRA_FUSE_PAUSER_LOCK", tid, '0, '0); 
    @(posedge clk_tb);


    error_ctr += sb.err_count;

  end

endtask // fuse_reg_pauser_test



//----------------------------------------------------------------
// function get_fuse_regval()
//
// Probes to get the intenral fuse register value inside dut 
//----------------------------------------------------------------
function dword_t get_fuse_regval(string rname);

  automatic dword_t regval; 
  string pfx = "unknown";
  automatic int j; 

  strq_t prefixes = {"FUSE_UDS_SEED", "FUSE_FIELD_ENTROPY", "FUSE_KEY_MANIFEST_PK_HASH",  
   "FUSE_OWNER_PK_HASH", "FUSE_RUNTIME_SVN", "FUSE_IDEVID_CERT_ATTR", "FUSE_IDEVID_MANUF_HSM_ID"}; 

  begin
    case (rname) 
      "FUSE_KEY_MANIFEST_PK_HASH_MASK"      :  regval = fuse_key_manifest_pk_hash_mask; 
      "FUSE_FMC_KEY_MANIFEST_SVN"           :  regval = fuse_fmc_key_manifest_svn; 
      "FUSE_ANTI_ROLLBACK_DISABLE"          :  regval = fuse_anti_rollback_disable; 
      "FUSE_LIFE_CYCLE"                     :  regval = fuse_life_cycle ; 
      "FUSE_LMS_VERIFY"                     :  regval = fuse_lms_verify ; 
      "FUSE_LMS_REVOCATION"                 :  regval = fuse_lms_revocation; 

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
                    (pfx == "FUSE_OWNER_PK_HASH"       ) ? fuse_owner_pk_hash[j] :
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
// task set_fuse_pauser_lock()
//
// Sets fuse pauser lock register & checks value
//----------------------------------------------------------------
task set_fuse_pauser_lock(input logic lock_value, input int tid, output logic lock_status); 

  automatic WordTransaction wrtrans, rdtrans;
  begin
    wrtrans = new();
    rdtrans = new();

    wrtrans.update_byname("CPTRA_FUSE_PAUSER_LOCK", lock_value, tid); 
    write_reg_trans(SET_APB, wrtrans);
    repeat (3) @(posedge clk_tb);
    rdtrans.update_byname("CPTRA_FUSE_PAUSER_LOCK", 0, tid); 
    read_reg_trans(GET_APB, rdtrans); // FIXME.
    $display ("Pauser lock status = 0x%08x", rdtrans.data); 

    lock_status = rdtrans.data[0];
  end
endtask // set_fuse_pauser_lock


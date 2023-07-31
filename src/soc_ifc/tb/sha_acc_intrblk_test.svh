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


  //----------------------------------------------------------------
  // sha_acc_intrblk_test()
  // 
  // Tests that SHA ACC Interrupt Block Registers are RO over APB  
  //----------------------------------------------------------------


  task sha_acc_intrblk_test; 

    automatic word_addr_t addr; 
    automatic int tid = 0; // TID is to be updated ONLY if multiple writes to an address 
    automatic strq_t sha_acc_intrblk_regnames;
    automatic strq_t nonmatching_regnames;
    automatic dword_t rddata; 
    automatic dwordq_t nonmatching_rddata;
    automatic string rname;
    automatic dword_t ahb_wrdata, exp_regval; 
    automatic dword_t apb_wrdata, apb_rddata; 
    automatic WordTransaction wrtrans, rdtrans;

    // Interrupt Register Block Fields 
    // --------------------------------
    // logic global_intr_en_r.error_en;
    // logic global_intr_en_r.notif_en;
    // logic error_intr_en_r.error0_en;
    // logic error_intr_en_r.error1_en;
    // logic error_intr_en_r.error2_en;
    // logic error_intr_en_r.error3_en;
    // logic notif_intr_en_r.notif_cmd_done_en;
    // logic error_global_intr_r.agg_sts;
    // logic notif_global_intr_r.agg_sts;
    logic [3:0] error_internal_intr_r;  // represent next 4 fields
    // logic error_internal_intr_r.error0_sts;
    // logic error_internal_intr_r.error1_sts;
    // logic error_internal_intr_r.error2_sts;
    // logic error_internal_intr_r.error3_sts;
    logic notif_internal_intr_r;  // proxy for next field 
    // logic notif_internal_intr_r.notif_cmd_done_sts;
    logic [3:0] error_intr_trig_r;  // represent next 4 fields
    // logic error_intr_trig_r.error0_trig;
    // logic error_intr_trig_r.error1_trig;
    // logic error_intr_trig_r.error2_trig;
    // logic error_intr_trig_r.error3_trig;
    logic notif_intr_trig_r;  // proxy for next field;
    // logic notif_intr_trig_r.notif_cmd_done_trig;
    // logic error0_intr_count_r.cnt;
    // logic error1_intr_count_r.cnt;
    // logic error2_intr_count_r.cnt;
    // logic error3_intr_count_r.cnt;
    // logic notif_cmd_done_intr_count_r.cnt;
    // logic error0_intr_count_incr_r.pulse;
    // logic error1_intr_count_incr_r.pulse;
    // logic error2_intr_count_incr_r.pulse;
    // logic error3_intr_count_incr_r.pulse;
    // logic notif_cmd_done_intr_count_incr_r.pulse;

    begin
      $display("Executing task sha_acc_intrblk_test"); 
      $display("---------------------------------\n");

      // set_security_state_byname("DEBUG_UNLOCKED_PRODCUTION"); 

      tc_ctr = tc_ctr + 1;
      wrtrans = new();
      rdtrans = new();

      sha_acc_intrblk_regnames = get_sha_acc_intrblk_regnames();

      // Skip wrting & reading over AHB until post reset sequencing is done 
      // THEN, update scoreboard entry accordingly for a couple of registers which 
      // are written using APB as part of Caliptra boot.  Scoreboard update not 
      // needed for readonly fields which are set directly by wires.
      simulate_caliptra_boot();

      // PHASE I. 1a.  Write (AHB, then APB) and Read register over APB 
      // ------------------------------------------------------------

      repeat (20) @(posedge clk_tb);
      sb.del_all();

      update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);

      $display ("\n1a. Writing over AHB, APB then reading back over APB"); 

      foreach (sha_acc_intrblk_regnames[i]) begin
        rname = sha_acc_intrblk_regnames[i];
        addr = socregs.get_addr(rname);
        wrtrans.update(addr, 0, tid);
        wrtrans.randomize();

        ahb_wrdata = wrtrans.data; 
        apb_wrdata = ~ahb_wrdata; 

        write_reg_trans(SET_AHB, wrtrans);  
        repeat (3) @(posedge clk_tb);
        wrtrans.update_data(apb_wrdata);
        write_reg_trans(SET_APB, wrtrans);  
        repeat (3) @(posedge clk_tb);

        rdtrans.update(addr, 0, tid);
        read_reg_trans(GET_APB, rdtrans);  
        @(posedge clk_tb);

        apb_rddata = rdtrans.data;
        exp_regval = socregs.get_exp_regval(rname);

        if (apb_rddata == exp_regval)
          continue; // all good; move on to next

        if (apb_rddata == apb_wrdata) begin
          $display ("TB ERROR for addr 0x%08x (%s). apb_rddata matches apb_wrdata 0x%08x", addr, rname, apb_rddata);
          error_ctr = error_ctr + 1;
        end else if (apb_rddata != exp_regval) begin 
          if (rddata != '0) begin 
            $display ("TB ERROR for addr 0x%08x (%s). Unexpected non-zero apb_rddata 0x%08x", addr, rname, rddata);
            error_ctr = error_ctr + 1;
          end else begin
            $display ("TB Warning for addr 0x%08x (%s). apb_rddata 0x%08x does not match exp_regval 0x%08x", addr, rname, apb_rddata, exp_regval);
            nonmatching_regnames.push_back(rname);
            nonmatching_rddata.push_back(apb_rddata);
          end
        end
      end 

      // control launch of assertions using directed writes
      // Expect issues w/the 4 registers
      assign error_internal_intr_r = {dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error0_sts.value , 
                                      dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error1_sts.value , 
                                      dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error2_sts.value ,
                                      dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error3_sts.value}; 

      assign notif_internal_intr_r = dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.value; 	

      assign error_intr_trig_r = {dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_intr_trig_r.error0_trig.value ,
                                 dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_intr_trig_r.error1_trig.value ,
                                 dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_intr_trig_r.error2_trig.value ,
                                 dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_intr_trig_r.error3_trig.value};

      assign notif_intr_trig_r = dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.notif_intr_trig_r.notif_cmd_done_trig.value;


      foreach (nonmatching_regnames[i]) begin
        rname = nonmatching_regnames[i];
        rddata = nonmatching_rddata[i];

        addr = socregs.get_addr(rname);
        wrtrans.update(addr, 32'hffff_ffff, tid);
        write_reg_trans(SET_AHB, wrtrans); // This should clear the register to all 0's
        repeat (10) @(posedge clk_tb); 

        fork    // Try to set again over apb - should be unsuccessful 
          begin
            write_reg_trans(SET_APB, wrtrans);  
            repeat (10) @(posedge clk_tb); 
          end

          begin
            repeat (10) begin
              // $display ( "TB DEBUG. checking for assertion");
              @(posedge clk_tb);
              case (rname) 
               "SHA_ACC_INTR_BRF_ERROR_INTERNAL_INTR_R": assert ((|error_internal_intr_r) == 1'b0)
                  else begin
                    $display ("TB ERROR aserted for addr 0x%08x (%s). Register bit-field(s) mutable over APB! agg value is 0b%b", addr, rname, error_internal_intr_r);
                    error_ctr += 1;
                    break;
                  end

                "SHA_ACC_INTR_BRF_NOTIF_INTERNAL_INTR_R": assert ((|notif_internal_intr_r) == 1'b0)
                  else begin
                    $display ("TB ERROR aserted for addr 0x%08x (%s). Register bit-field(s) mutable over APB! agg value is 0b%b", addr, rname, notif_internal_intr_r); 
                    error_ctr += 1;
                    break;
                  end

                "SHA_ACC_INTR_BRF_ERROR_INTR_TRIG_R": assert ((|error_intr_trig_r) == 1'b0)
                  else begin
                    $display ("TB ERROR aserted for addr 0x%08x (%s). Register bit-field(s) mutable over APB! agg value is 0b%b", addr, rname, error_intr_trig_r); 
                    error_ctr += 1;
                    break;
                  end

                "SHA_ACC_INTR_BRF_NOTIF_INTR_TRIG_R": assert ((|notif_intr_trig_r) == 1'b0)
                  else begin
                    $display ("TB ERROR aserted for addr 0x%08x (%s). Register bit-field(s) mutable over APB! agg value is 0b%b", addr, rname, notif_intr_trig_r); 
                    error_ctr += 1;
                    break;
                  end

                default: $display ("TB ERROR for addr 0x%08x (%s). Unexpected mismatch; no handler found", addr, rname); 
              endcase
            end 
          end
        join_any
 
      end
      
    end

  endtask // sha_acc_intrblk_test

/* 
// Placeholder for concurrent assertions in future

sequence remain_low__sha_acc_error_internal_intr_r;
  (| ({ dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error0_sts.value, 
        dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error1_sts.value, 
        dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error2_sts.value,
        dut.i_sha512_acc_top.i_sha512_acc_csr.field_storage.intr_block_rf.error_internal_intr_r.error3_sts.value }) == 1'b0); 
endsequence 

property reg_remains_low;
  @(posedge clk_tb)
  disable iff (reg_sva_off) remain_low__sha_acc_error_internal_intr_r;
endproperty

monitor_trans2ones: assert property(reg_remains_low);
*/


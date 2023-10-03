//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This class can be used to provide stimulus when an interface
//              has been configured to run in a responder mode. It
//              will never finish by default, always going back to the driver
//              and driver BFM for the next transaction with which to respond.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class mbox_sram_responder_sequence 
  extends mbox_sram_sequence_base ;

  `uvm_object_utils( mbox_sram_responder_sequence )

  // pragma uvmf custom class_item_additional begin
  // Implement a model of the Mailbox SRAM
  localparam NUM_BYTES = MBOX_DATA_AND_ECC_W/8 + ((MBOX_DATA_AND_ECC_W % 8) ? 1 : 0);
  // TODO support initialization from mailbox.hex
  logic [7:0] ram [MBOX_DEPTH][NUM_BYTES-1:0] = '{default: 8'h00};

  function bit [1:0] rvecc_decode  ( input [31:0]  din, input [6:0]   ecc_in);
    bit [6:0]  ecc_check;

    // Generate the ecc bits
    ecc_check[0] = ecc_in[0]^din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30];
    ecc_check[1] = ecc_in[1]^din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31];
    ecc_check[2] = ecc_in[2]^din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31];
    ecc_check[3] = ecc_in[3]^din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
    ecc_check[4] = ecc_in[4]^din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
    ecc_check[5] = ecc_in[5]^din[26]^din[27]^din[28]^din[29]^din[30]^din[31];

    // This is the parity bit
    ecc_check[6] = ((^din[31:0])^(^ecc_in[6:0]));

    rvecc_decode[0] = (ecc_check[6:0] != 0) &  ecc_check[6]; // Single-bit error
    rvecc_decode[1] = (ecc_check[6:0] != 0) & ~ecc_check[6]; // Double-bit error

  endfunction: rvecc_decode
  // pragma uvmf custom class_item_additional end

  function new(string name = "mbox_sram_responder_sequence");
    super.new(name);
  endfunction

  task body();
    req=mbox_sram_transaction::type_id::create("req");
    forever begin
      start_item(req);
      finish_item(req);
      // pragma uvmf custom body begin
      // Do something here with the resulting req item.  The
      // finish_item() call above will block until the req transaction is ready
      // to be handled by the responder sequence.
      // If this was an item that required a response, the expectation is
      // that the response should be populated within this transaction now.
      wait(new_rsp.triggered);
      if (req.compare(rsp)) `uvm_info("MBOX_SRAM_SEQ", "req and rsp are the same after finish_item", UVM_DEBUG)
      else                  `uvm_error("MBOX_SRAM_SEQ", $sformatf("NOTE: req and rsp are different after finish_item.\nreq: %s\nrsp: %s", req.convert2string(), rsp.convert2string()))
      // The 'rsp' is actually a request from the DUT, we need to create a response
      if (rsp.is_read) begin
        byte unsigned ii;
        for (ii=0;ii<MBOX_DATA_W/8;ii++) begin
            req.data[ii*8+:8] = ram[rsp.address][ii];
        end
        req.data_ecc = ram[rsp.address][NUM_BYTES-1][MBOX_ECC_DATA_W-1:0];
        {req.ecc_double_bit_error,
         req.ecc_single_bit_error} = rvecc_decode(req.data, req.data_ecc);
      end
      else begin
        byte unsigned ii;
        mbox_sram_data_t wdata;
        mbox_sram_data_t wdata_mask;
        wdata.data = rsp.data;
        wdata.ecc  = rsp.data_ecc;
        if (rsp.ecc_double_bit_error) begin
            if (!std::randomize(wdata_mask) with {$countones(wdata_mask) == 2;})
                `uvm_error("MBOX_SRAM_SEQ", "Failed to generate a random mask to inject ECC double bit error!")
            wdata ^= wdata_mask;
            `uvm_info("MBOX_SRAM_SEQ", $sformatf("Injecting ECC double bit flip to write data. Modified data: 0x%x [%p]", wdata, wdata), UVM_HIGH)
        end
        else if (rsp.ecc_single_bit_error) begin
            if (!std::randomize(wdata_mask) with {$countones(wdata_mask) == 1;})
                `uvm_error("MBOX_SRAM_SEQ", "Failed to generate a random mask to inject ECC single bit error!")
            wdata ^= wdata_mask;
            `uvm_info("MBOX_SRAM_SEQ", $sformatf("Injecting ECC single bit flip to write data. Modified data: 0x%x [%p]", wdata, wdata), UVM_HIGH)
        end
        for (ii=0;ii<MBOX_DATA_W/8;ii++) begin
            ram[rsp.address][ii] = wdata.data[ii*8+:8];
        end
        ram[rsp.address][NUM_BYTES-1][MBOX_ECC_DATA_W-1:0] = wdata.ecc;
      end
      `uvm_info("MBOX_SRAM_SEQ",$sformatf("Processed txn: %s",req.convert2string()),UVM_HIGH)
      // pragma uvmf custom body end
    end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end


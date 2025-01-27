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
// DESCRIPTION: Bringup sequence for the SOC_IFC environment
//              (essentially just a cold-reset sequence)
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_rom_bringup_sequence extends soc_ifc_env_reset_sequence_base;


  `uvm_object_utils( soc_ifc_env_rom_bringup_sequence )

  typedef soc_ifc_ctrl_rom_poweron_sequence soc_ifc_ctrl_agent_poweron_sequence_t;

  localparam SHA384_DIGEST_SIZE             = 48; // bytes

  // 384-bit (12 dwords) vector to store calculated hash of Key Manifest and Owner
  // public keys from ROM image
  bit [0:SHA384_DIGEST_SIZE/4-1]                                     [31:0] vendor_pk_hash_val;
  bit [0:SHA384_DIGEST_SIZE/4-1]                                     [31:0] owner_pk_hash_val;

  // Decide which fuses to initialize
  constraint always_set_uds_c { this.fuses_to_set.uds == 1'b1; }
  constraint always_set_fe_c  { this.fuses_to_set.field_entropy == 1'b1; }
//  // Roughly 50% of the tests
//  constraint randomly_set_lms_verify_c { this.fuses_to_set.lms_verify dist {0 :/ 50, 1 :/ 50}; }
  constraint always_set_vendor_pk_hash_c { this.fuses_to_set.vendor_pk_hash == {12{1'b1}}; }
  constraint always_set_owner_pk_hash_c { this.fuses_to_set.owner_pk_hash == {12{1'b1}}; }
  constraint always_set_key_revocation_c { this.fuses_to_set.ecc_revocation   == 1'b1;
                                           this.fuses_to_set.lms_revocation   == 1'b1;
                                           this.fuses_to_set.mldsa_revocation == 1'b1; }
  constraint always_set_idevid_c  { this.fuses_to_set.idevid_cert_attr[0 ] == 1'b1;
                                    this.fuses_to_set.idevid_cert_attr[11] == 1'b1;
                                    this.fuses_to_set.idevid_cert_attr[12] == 1'b1;
                                    this.fuses_to_set.idevid_cert_attr[13] == 1'b1;
                                    this.fuses_to_set.idevid_cert_attr[14] == 1'b1;
                                    this.fuses_to_set.idevid_cert_attr[15] == 1'b1; }
  // Configure the values to set to initialized fuses
  constraint vendor_pk_hash_values_c { vendor_pk_hash_rand[0]  == this.vendor_pk_hash_val[0] ; //32'h6DC8DE16;
                                       vendor_pk_hash_rand[1]  == this.vendor_pk_hash_val[1] ; //32'hD559D129;
                                       vendor_pk_hash_rand[2]  == this.vendor_pk_hash_val[2] ; //32'h7BAB1E43;
                                       vendor_pk_hash_rand[3]  == this.vendor_pk_hash_val[3] ; //32'hEBD7C533;
                                       vendor_pk_hash_rand[4]  == this.vendor_pk_hash_val[4] ; //32'hDFE57001;
                                       vendor_pk_hash_rand[5]  == this.vendor_pk_hash_val[5] ; //32'h1AA56220;
                                       vendor_pk_hash_rand[6]  == this.vendor_pk_hash_val[6] ; //32'h0F66AD6D;
                                       vendor_pk_hash_rand[7]  == this.vendor_pk_hash_val[7] ; //32'h87051086;
                                       vendor_pk_hash_rand[8]  == this.vendor_pk_hash_val[8] ; //32'hC785E930;
                                       vendor_pk_hash_rand[9]  == this.vendor_pk_hash_val[9] ; //32'hD3D947B4;
                                       vendor_pk_hash_rand[10] == this.vendor_pk_hash_val[10]; //32'h7495822E;
                                       vendor_pk_hash_rand[11] == this.vendor_pk_hash_val[11]; //32'hCB643FF1;
                                       solve this.fuses_to_set before this.vendor_pk_hash_rand; }
  constraint owner_pk_hash_values_c { owner_pk_hash_rand[0]  == owner_pk_hash_val[0] ;//32'hF58D4920;
                                      owner_pk_hash_rand[1]  == owner_pk_hash_val[1] ;//32'hBA65DA44;
                                      owner_pk_hash_rand[2]  == owner_pk_hash_val[2] ;//32'hB0F728BC;
                                      owner_pk_hash_rand[3]  == owner_pk_hash_val[3] ;//32'hFB893202;
                                      owner_pk_hash_rand[4]  == owner_pk_hash_val[4] ;//32'hCFAAA942;
                                      owner_pk_hash_rand[5]  == owner_pk_hash_val[5] ;//32'hBC66A0C0;
                                      owner_pk_hash_rand[6]  == owner_pk_hash_val[6] ;//32'h007A2CE2;
                                      owner_pk_hash_rand[7]  == owner_pk_hash_val[7] ;//32'h29A8E08F;
                                      owner_pk_hash_rand[8]  == owner_pk_hash_val[8] ;//32'h9E8EEBAE;
                                      owner_pk_hash_rand[9]  == owner_pk_hash_val[9] ;//32'hB36E9CC0;
                                      owner_pk_hash_rand[10] == owner_pk_hash_val[10];//32'h962E4B7A;
                                      owner_pk_hash_rand[11] == owner_pk_hash_val[11];//32'h50214999;
                                      solve this.fuses_to_set before this.owner_pk_hash_rand; }
  constraint ecc_revocation_value_c { ecc_revocation_rand  == 0;
                                      solve this.fuses_to_set before this.ecc_revocation_rand; }
  constraint lms_revocation_value_c { lms_revocation_rand == 0;
                                      solve this.fuses_to_set before this.lms_revocation_rand; }
  constraint mldsa_revocation_value_c { mldsa_revocation_rand == 0;
                                      solve this.fuses_to_set before this.mldsa_revocation_rand; }
  constraint idevid_values_c { idevid_cert_attr_rand[0]  == '0; /* SHA1 */
                               idevid_cert_attr_rand[11] == 32'hFFFF_FFFF; /* UEID LSWord */
                               idevid_cert_attr_rand[12] == 32'h0202_0101; /* Manuf Serial Num */
                               idevid_cert_attr_rand[13] == 32'h3030_4040; /* Manuf Serial Num */
                               idevid_cert_attr_rand[14] == 32'h0505_0606; /* Manuf Serial Num */
                               idevid_cert_attr_rand[15] == 32'h7070_8080; /* Manuf Serial Num */}

  //==========================================
  // Function:    new
  // Description: Constructor
  //==========================================
  function new(string name = "" );
    uvm_object obj;
    int fd;
    string hex_val;
    super.new(name);
    obj = soc_ifc_ctrl_agent_poweron_sequence_t::get_type().create_object("soc_ifc_ctrl_agent_poweron_seq");
    if (!$cast(soc_ifc_ctrl_seq,obj))
        `uvm_fatal("SOC_IFC_BRINGUP", "Failed to cast object as poweron sequence!")

    // Read the PK Hash values extracted/calculated from the ROM image
    fd = $fopen("vendor_pk_hash_val.hex", "r");
    if (!fd) begin
        integer errno;
        string str;
        errno = $ferror(fd, str);
        `uvm_fatal("SOC_IFC_BRINGUP", $sformatf("fopen failed to open vendor_pk_hash_val.hex with code [0x%x] message [%s]", errno, str))
    end
    void'($fscanf(fd, "%x", vendor_pk_hash_val));
    $fclose(fd);

    fd = $fopen("owner_pk_hash_val.hex", "r");
    if (!fd) begin
        integer errno;
        string str;
        errno = $ferror(fd, str);
        `uvm_fatal("SOC_IFC_BRINGUP", $sformatf("fopen failed to open owner_pk_hash_val.hex with code [0x%x] message [%s]", errno, str))
    end
    void'($fscanf(fd, "%x", owner_pk_hash_val       ));
    $fclose(fd);

    `uvm_info("SOC_IFC_BRINGUP", $sformatf("Using Vendor Public Key Hash of 0x%x %p from ROM image", vendor_pk_hash_val, vendor_pk_hash_val), UVM_LOW)
    `uvm_info("SOC_IFC_BRINGUP", $sformatf("Using Owner Public Key Hash of 0x%x %p from ROM image", owner_pk_hash_val, owner_pk_hash_val), UVM_LOW)

  endfunction

endclass

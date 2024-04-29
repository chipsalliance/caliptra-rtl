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
  bit [0:SHA384_DIGEST_SIZE/4-1]                                     [31:0] key_manifest_pk_hash_val;
  bit [0:SHA384_DIGEST_SIZE/4-1]                                     [31:0] owner_pk_hash_val;

  // Decide which fuses to initialize
  constraint always_set_uds_c { this.fuses_to_set.uds == 1'b1; }
  constraint always_set_fe_c  { this.fuses_to_set.field_entropy == 1'b1; }
  // Roughly 50% of the tests
  constraint randomly_set_lms_verify_c { this.fuses_to_set.lms_verify dist {0 :/ 50, 1 :/ 50}; }
  constraint always_set_key_manifest_pk_hash_c { this.fuses_to_set.key_manifest_pk_hash == {12{1'b1}}; }
  constraint always_set_owner_pk_hash_c { this.fuses_to_set.owner_pk_hash == {12{1'b1}}; }
  constraint always_set_idevid_c  { this.fuses_to_set.idevid_cert_attr[0] == 1'b1;
                                    this.fuses_to_set.idevid_cert_attr[6] == 1'b1;
                                    this.fuses_to_set.idevid_cert_attr[7] == 1'b1; }
  // Configure the values to set to initialized fuses
  constraint key_manifest_pk_hash_values_c { key_manifest_pk_hash_rand[0]  == this.key_manifest_pk_hash_val[0] ; //32'h6DC8DE16;
                                             key_manifest_pk_hash_rand[1]  == this.key_manifest_pk_hash_val[1] ; //32'hD559D129;
                                             key_manifest_pk_hash_rand[2]  == this.key_manifest_pk_hash_val[2] ; //32'h7BAB1E43;
                                             key_manifest_pk_hash_rand[3]  == this.key_manifest_pk_hash_val[3] ; //32'hEBD7C533;
                                             key_manifest_pk_hash_rand[4]  == this.key_manifest_pk_hash_val[4] ; //32'hDFE57001;
                                             key_manifest_pk_hash_rand[5]  == this.key_manifest_pk_hash_val[5] ; //32'h1AA56220;
                                             key_manifest_pk_hash_rand[6]  == this.key_manifest_pk_hash_val[6] ; //32'h0F66AD6D;
                                             key_manifest_pk_hash_rand[7]  == this.key_manifest_pk_hash_val[7] ; //32'h87051086;
                                             key_manifest_pk_hash_rand[8]  == this.key_manifest_pk_hash_val[8] ; //32'hC785E930;
                                             key_manifest_pk_hash_rand[9]  == this.key_manifest_pk_hash_val[9] ; //32'hD3D947B4;
                                             key_manifest_pk_hash_rand[10] == this.key_manifest_pk_hash_val[10]; //32'h7495822E;
                                             key_manifest_pk_hash_rand[11] == this.key_manifest_pk_hash_val[11]; //32'hCB643FF1;
                                             solve this.fuses_to_set before this.key_manifest_pk_hash_rand; }
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
  constraint idevid_values_c { idevid_cert_attr_rand[0] == '0; /* SHA1 */
                               idevid_cert_attr_rand[6] == 32'hFFFF_FFFF; /* UEID LSWord */
                               idevid_cert_attr_rand[7] == 32'hFFFF_FFFF; /* MSWord */}

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
    fd = $fopen("key_manifest_pk_hash_val.hex", "r");
    if (!fd) begin
        integer errno;
        string str;
        errno = $ferror(fd, str);
        `uvm_fatal("SOC_IFC_BRINGUP", $sformatf("fopen failed to open key_manifest_pk_hash_val.hex with code [0x%x] message [%s]", errno, str))
    end
    void'($fscanf(fd, "%x", key_manifest_pk_hash_val));
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

    `uvm_info("SOC_IFC_BRINGUP", $sformatf("Using Vendor Public Key Hash of 0x%x %p from ROM image", key_manifest_pk_hash_val, key_manifest_pk_hash_val), UVM_LOW)
    `uvm_info("SOC_IFC_BRINGUP", $sformatf("Using Owner Public Key Hash of 0x%x %p from ROM image", owner_pk_hash_val, owner_pk_hash_val), UVM_LOW)

  endfunction

endclass

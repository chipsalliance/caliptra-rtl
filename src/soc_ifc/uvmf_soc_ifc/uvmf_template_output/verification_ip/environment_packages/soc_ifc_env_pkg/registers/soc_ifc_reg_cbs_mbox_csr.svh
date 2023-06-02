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
//----------------------------------------------------------------------

// This class exists only to serve as a base class for other mbox_csr
// register fields that will need some common functionality
virtual class soc_ifc_reg_cbs_mbox_csr extends uvm_reg_cbs;

    string AHB_map_name = "soc_ifc_AHB_map";
    string APB_map_name = "soc_ifc_APB_map";

    // Shorthand methods to make the 'post_predict' logic more readable
    // in descendant classes
    virtual function uvm_reg_data_t mbox_dlen_mirrored(mbox_csr_ext rm);
        return rm.mbox_dlen.length.get_mirrored_value();
    endfunction

    // Convert the ceiling value of DLEN in dwords (converted from bytes)
    // FIXME here and elsewhere, 4-byte size for SOC_IFC_DATA_W is hardcoded in the converion from DLEN to DWORDS
    virtual function uvm_reg_data_t mbox_dlen_mirrored_dword_ceil(mbox_csr_ext rm);
        return (mbox_dlen_mirrored(rm) >> 2) + ((mbox_dlen_mirrored(rm) & 3) ? 1 : 0);
    endfunction

endclass


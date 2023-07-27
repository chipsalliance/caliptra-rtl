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
// DESCRIPTION: This package contains test level parameters
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//


package caliptra_top_parameters_pkg;

  import uvmf_base_pkg_hdl::*;

  // pragma uvmf custom package_imports_additional begin 
  // pragma uvmf custom package_imports_additional end


  // These parameters are used to uniquely identify each interface.  The monitor_bfm and
  // driver_bfm are placed into and retrieved from the uvm_config_db using these string 
  // names as the field_name. The parameter is also used to enable transaction viewing 
  // from the command line for selected interfaces using the UVM command line processing.
  parameter string uvm_test_top_environment_soc_ifc_subenv_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0  = "uvm_test_top.environment.soc_ifc_subenv.qvip_ahb_lite_slave_subenv.ahb_lite_slave_0"; /* [0] */
  parameter string uvm_test_top_environment_soc_ifc_subenv_qvip_apb5_slave_subenv_apb5_master_0  = "uvm_test_top.environment.soc_ifc_subenv.qvip_apb5_slave_subenv.apb5_master_0"; /* [1] */
  parameter string soc_ifc_subenv_soc_ifc_ctrl_agent_BFM  = "soc_ifc_subenv_soc_ifc_ctrl_agent_BFM"; /* [2] */
  parameter string soc_ifc_subenv_cptra_ctrl_agent_BFM  = "soc_ifc_subenv_cptra_ctrl_agent_BFM"; /* [3] */
  parameter string soc_ifc_subenv_soc_ifc_status_agent_BFM  = "soc_ifc_subenv_soc_ifc_status_agent_BFM"; /* [4] */
  parameter string soc_ifc_subenv_cptra_status_agent_BFM  = "soc_ifc_subenv_cptra_status_agent_BFM"; /* [5] */
  parameter string soc_ifc_subenv_mbox_sram_agent_BFM  = "soc_ifc_subenv_mbox_sram_agent_BFM"; /* [6] */

  // pragma uvmf custom package_item_additional begin
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end


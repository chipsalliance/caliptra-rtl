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


module soc_ifc_cov_bind;
    `ifdef FCOV
    import soc_ifc_pkg::*;
    bind soc_ifc_top soc_ifc_cov_if #(
        .AHB_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .AHB_DATA_WIDTH(`CALIPTRA_AHB_HDATA_SIZE),
        .AXI_ADDR_WIDTH(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .AXI_DATA_WIDTH(`CALIPTRA_AXI_DATA_WIDTH),
        .AXI_ID_WIDTH  (`CALIPTRA_AXI_ID_WIDTH  ),
        .AXI_USER_WIDTH(`CALIPTRA_AXI_USER_WIDTH),
        .AXIM_ADDR_WIDTH(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .AXIM_DATA_WIDTH(soc_ifc_pkg::CPTRA_AXI_DMA_DATA_WIDTH),
        .AXIM_ID_WIDTH  (soc_ifc_pkg::CPTRA_AXI_DMA_ID_WIDTH),
        .AXIM_USER_WIDTH(soc_ifc_pkg::CPTRA_AXI_DMA_USER_WIDTH)
        )
        i_soc_ifc_cov_if (.*);
    `endif
endmodule

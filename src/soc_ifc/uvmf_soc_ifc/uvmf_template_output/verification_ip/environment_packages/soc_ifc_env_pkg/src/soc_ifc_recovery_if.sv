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

// Carries recovery sidebands driven by the endpoint component. Clock and reset
// are shared with the AXI-facing FIFO so status changes can be checked against
// read-data handshakes without hierarchy references.
interface soc_ifc_recovery_if (
  input logic clk,
  input logic rst_n
);
  logic recovery_data_avail;
  logic recovery_image_activated;

endinterface

_*SPDX-License-Identifier: Apache-2.0<BR>
<BR>
<BR>
Licensed under the Apache License, Version 2.0 (the "License");<BR>
you may not use this file except in compliance with the License.<BR>
You may obtain a copy of the License at<BR>
<BR>
http://www.apache.org/licenses/LICENSE-2.0 <BR>
<BR>
Unless required by applicable law or agreed to in writing, software<BR>
distributed under the License is distributed on an "AS IS" BASIS,<BR>
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.<BR>
See the License for the specific language governing permissions and<BR>
limitations under the License.*_<BR>

# HMAC

Date: 28-07-2023 Author: LUBIS EDA

## Folder Structure

The following subdirectories are part of the main directory **formal**

- model: Contains the high level abstracted model
- properties: Contains the assertion IP(AIP) named as fv_hmac.sv and the constraints in place for the respective AIP fv_constraints.sv and fv_constraints_wip.sv

## DUT Overview

The DUT hmac_core has the primary inputs and primary outputs as shown below.

|S.No |	Port	         |Direction| Description                                                                               |
|---- |----------------- |-------- |-------------------------------------------------------------------------------------------|
|1	  |clk	             | input   | The positive edge of the clk is used for all the signals                                  |
|2	  |reset_n	         | input   | The reset signal is active low and resets the core                                        |
|3	  |zeroize	         | input   | The core is reseted when this signal is triggered.                                        |
|4	  |init_cmd	         | input   | The core is initialised with respective mode constants and processes the message.         |
|5	  |next_cmd	         | input   | The core processes the message block with the previously computed results                 |
|6	  |key[383:0]	     | input   | The input key                                                                             |
|7	  |block_msg[1023:0] | input   | The padded block message                                                                  |
|8	  |lfsr_seed[147:0]	 | input   | The input constant value that is feed to sha512_masked as an input for digest computation |
|8	  |ready	         | output  | When triggered indicates that the core is ready                                           |
|9	  |tag[383:0]	     | output  | The tag value of the given message block                                                  |
|10	  |tag_valid	     | output  | When triggered indicates that the computed tag is ready                                   |

Hmac algorithm starts with padding the key with IPAD and OPAD constants. Once HMAC receives init_cmd, it initalizes both HMAC and first instantance of SHA, with IPAD padded key. With next_cmd, HMAC feeds block msg to first instantance of SHA, at the same time initalizes second instantance of SHA with OPAD padded key. With the digest recieved from first SHA, the digest is padded to have 1024 bit and later feed to second instantance of SHA, to get the final digest value, which the tag for HMAC. The digest of SHA is always of 512 bits, first 384 is considered valid while rest is garabage value.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the rst is binded with the DUT (reset_n && !zeroize), which ensures the reset functionality. Assertion IP is binded with hmac_core and checks for the functionality of only hmac_core. The digest of sha512_masked_core is considered to be cut open. This is perfomed on the formal tool. This way the tool has the freedom to choose any random value of digest coming out of sha512_maked_core so as to reduce the complex functionality of sha512 hashing. With this approach, IP makes sure hmac_core is functionality correct irrespective of correct computed value of digest and helps in proof convergence. Constraints are made on init_cmd and next_cmd signals of hmac_core The constraints can be looked up at fv_constraints.sv.

- reset_a: Checks that all the resgiters are resetted and the state is idle, with the ready to high.

- ctrl_hmac_to_done_tag_a: Checks the necessary registers, outputs holds the values when state transits from Done to idle,

- done_tag_to_idle_a: Checks if tag register outputs correct value and tag_valid is high, when transition from done to idle states.

- idle_to_ctrl_ipad_a: Checks if the state is in idle , if init is triggered then the sha_blocks should be assigned with respective padded key values and SHA1 is initailized.

- idle_to_ctrl_opad_a: Checks if the state is in idle , if next is triggered then SHA2 is initailized with right padded key value, and SHA1 should be assigned with hmac block msg.

- ctrl_ipad_to_ctrl_opad_a: Checks if the state is transitioned from inner_padding to outer_padding state , then SHA2 is initailized with right padded key value, and SHA1 should be assigned with hmac block msg.

- ctrl_hmac_wait_a: Checks if digest from SHA2 is not ready, it remains in the same state until digest is ready.

- idle_wait_a: Checks if the state remains same until, there is an init or next command.

- ctrl_ipad_wait_a: Checks if the state remains same until, digest from SHA1 is ready.

- ctrl_opad_wait_a: Checks if the state remains same until, digest from SHA2 is ready.


## Reproduce results

The AIP has been tested with two major FV tools. For both tools proves pass in less then 2 hour and coverage is at 100%. 

For reproducing the results:
Load the AIP, hmac_core and fv_constraints together in your formal tool. 
To ensure converging proves cut the following signals: 

cut u_sha512_core_h1.digest
cut u_sha512_core_h2.digest

The sha512_masked core had been verified separately. By cutting the signal model complexity is drastically reduced. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 

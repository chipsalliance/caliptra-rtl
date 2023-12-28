# HMAC DRBG

Date: 28-08-2023 Author: LUBIS EDA

## Folder Structure

The following subdirectories are part of the main directory **formal**

- model: Contains the high level abstracted model
- properties: Contains the assertion IP(AIP) named as fv_hmac_drbg.sv and the constraints in place for the respective AIP fv_constraints.sv. The folder also contains fv_cover_points.sv that cover certain conditions that are not covered by the properties.

## DUT Overview

The DUT hmac_drbg has the primary inputs and primary outputs as shown below.

|S.No |	Port	         |Direction| Description                                                                               |
|---- |----------------- |-------- |-------------------------------------------------------------------------------------------|
|1	  |clk	             | input   | The positive edge of the clk is used for all the signals                                  |
|2	  |reset_n	         | input   | The reset signal is active low and resets the core                                        |
|3	  |zeroize	         | input   | The drbg is reseted when this signal is triggered.                                        |
|4	  |init_cmd	         | input   | The drbg is initialised with respective register init values                              |
|5	  |next_cmd	         | input   | The drbg processes by increasing count_register                                           |
|6	  |entropy   [383:0] | input   | The input entropy                                                                         |
|7	  |nonce     [383:0] | input   | The input nonce                                                                           |
|8	  |lfsr_seed [147:0] | input   | The input constant value that is feed to sha512_masked as an input for digest computation |
|8	  |ready	         | output  | When triggered indicates that the drbg is ready                                           |
|9	  |drbg      [383:0] | output  | The drbg value of the given input values                                                  |
|10	  |valid	         | output  | When triggered indicates that the computed drbg is valid                                  |

Drbg algorithm starts with assigning block_register and key_register to its init values. When the model receives an init_cmd, the count_register which helps in creating more randomness in generation of the drbg_tag, is assigned to zero. If the drbg_model recieves next_cmd the count_register is incremented. Initially drbg initializes HMAC by appending block_msg register with count_register and other input signals such as entropy and nonce. Using the updated tag from previous hmac is used as new hmac_key and hmac_block_msg as previous block_register for new tag computation. The updated tag computed will used as new hmac_block_msg and hmac_key remains the same. This repitation is done until we have recieved the tag value in the range of greater than 0 and less than the HMAC_TAG_PRIME value.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the rst is binded with the DUT (reset_n && !zeroize), which ensures the reset functionality. Assertion IP is binded with hmac_drbg and checks for the functionality of only hmac_drbg. hmac_tag from HMAC_CORE, is an open wire. This is achieved by cut open the signal from output port of HMAC_CORE, using formal tool. Since it is an open signal the complexity of tag computation is reduced and helps in converging the properties. Similarily two instantances of sha_digest from sha512_masked_core inside HMAC_CORE instantance are also cut open.

- reset_a: Checks that all the resgiters are resetted and the state is idle, with the ready to high.

- Done_to_idle_a:  Checks if tag register outputs correct value and valid is high, when transition from done to idle states.

- K10_to_K11_a: Checks if the state is in K11, the hmac_core is called with hmac_next_cmd is set to high and remaining nonce as the block_msg and key remains the same.

- K11_to_V1_a: Checks if the state is in V1, the hmac_core is called with hmac_init_cmd is set to high and block_msg as the previous block_register and key as updated tag from previous hmac computation.

- K20_to_K21_a: Checks if the state is in K21, the hmac_core is called with hmac_next_cmd is set to high and remaining nonce as the block_msg and key remains the same.

- K21_to_V2_a: Checks if the state is in V2, the hmac_core is called with hmac_init_cmd is set to high and block_msg as the previous block_register and key as updated tag from previous hmac computation.

- K3_to_V3_a: Checks if the state is in V3, the hmac_core is called with hmac_init_cmd is set to high and block_msg as the previous block_register and key as updated tag from previous hmac computation.

- T_to_Done_a: Checks if the is in done state, where the computated tag from hmac_core passes the required tag condition.

- T_to_K3_a: Checks if the state is in K3, where the computated tag from hmac_core failes the required tag condition and goes another round of randomness, by initalizing hmac_core and setting hmac_key as same and block_msg as previous tag appended with zeroes.

- V1_to_K20_a: Checks if the state is in K20, the hmac_core is initalized with hmac_init_cmd set, hmac_key remains the same and block_msg as the newly computed hmac_tag appened with count_register incremented and inputs entropy and nonce.

- V2_to_T_a: Checks if the state is in T, reads the computed tag from the hmac_core and appends it with previous stored tag_register in order to check if tag condition is holding or not.

- V3_to_T_a: Checks if the state is in T, reads the computed tag from the hmac_core and appends it with previous stored tag_register in order to check if tag condition is holding or not.

- idle_to_K10_a: Checks if the state reached is K10, checks for initalization of drbg and HMAC_CORE is ready. Count_register is set to zero, hmac_key is set with init key and hmac_block is appened with init block_register and inputs nonce and entropy.

- idle_to_K10_1_a: Checks if the state reached is K10, checks for next_cmd and HMAC_CORE is ready. Count_register is incremented, hmac_key is set with previously computed and hmac_block is appened with previously computed hmac_tag and inputs nonce and entropy.

- K10_wait_a: Checks if there is valid hmac_tag from hmac_core while in state K10, it remains in same state and certain registers holds past values and ready is low.

- K20_wait_a: Checks if there is valid hmac_tag from hmac_core while in state K20, it remains in same state and certain registers holds past values and ready is low. 

- V1_wait_a: Checks if there is valid hmac_tag from hmac_core while in state V1, it remains in same state and certain registers holds past values and ready is low. 

- K11_wait_a: Checks if there is valid hmac_tag from hmac_core while in state K11, it remains in same state and certain registers holds past values and ready is low. 

- K21_wait_a: Checks if there is valid hmac_tag from hmac_core while in state K21, it remains in same state and certain registers holds past values and ready is low. 

- V2_wait_a: Checks if there is valid hmac_tag from hmac_core while in state V2, it remains in same state and certain registers holds past values and ready is low. 

- T_wait_a: Checks if there is valid hmac_tag from hmac_core while in state T, it remains in same state and certain registers holds past values and ready is low. 

- K3_wait_a: Checks if there is valid hmac_tag from hmac_core while in state K3, it remains in same state and certain registers holds past values and ready is low. 

- V3_wait_a: Checks if there is valid hmac_tag from hmac_core while in state V3, it remains in same state and certain registers holds past values and ready is low. 

- idle_wait_a: Checks if there is valid hmac_tag from hmac_core while in state idle, it remains in same state and certain registers holds past values and while ready is high and previous computed drbg is valid. 

## Reproduce results

The AIP has been tested with two major FV tools. <em>For both tools proves pass in less then 2 hour and coverage is at 100% </em>.

For reproducing the results: Load the AIP, hmac_drbg and fv_constraints together in your formal tool. To ensure converging proves cut the following signals:

cut HMAC_K.u_sha512_core_h1.digest cut HMAC_K.u_sha512_core_h2.digest cut HMAC_K.tag

The hmac_core and sha512_masked core had been verified separately. By cutting the signal model complexity is drastically reduced.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts.
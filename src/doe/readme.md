# DOE
Date: 29-08-2023
Author: LUBIS EDA

## Folder Structure
The following subdirectories are part of the main directory **formal**

- properties: Contains the assertion IP(AIP) for each submodule of DUT along with the valid system constraints in **fv_constraints.sv**
    - keymem: **fv_doe_keymem** folder contains the assertion IP(AIP) for the submodule doe_key_mem along with the constraints for the respective AIP.
    - encipher: **fv_doe_encryption** folder contains the assertion IP(AIP) for the submodule doe_encipher_block along with the constraints for the respective AIP.
    - decipher: **fv_doe_decryption** folder contains the assertion IP(AIP) for the submodule doe_decipher_block along with the constraints for the respective AIP.
    - iv: **fv_doe_iv** folder contains the assertion IP(AIP) for the IV_Controller implementation in the DUT.
    - The folder also contains assertion IP(AIP) **fv_doe_core_cbc.sv** that covers few primary IO's properties and **fv_constraints.sv** contains the valid system constraints that drive primary Inputs as intended.

## DUT Overview

The DUT doe_core_cbc has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                       |
| ---- | ----------------- | --------- | --------------------------------------------------------------------------------- |
| 1    | clk               | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n           | input     | The reset signal is active low and resets the core                                |
| 3    | zeroize           | input     | The core is reseted when this signal is triggered.                                |
| 4    | encdec            | input     | The core is driven to perform encryption or decryption.                           |
| 5    | init_cmd          | input     | The core is initialised for the key expansion                                     |
| 6    | next_cmd          | input     | The core is initialised for the encryption or decryption                          |
| 7    | ready             | output    | Indicates that core is ready to accept new block in CBC                           |
| 8    | key[255:0]        | input     | The input key used for keyexpansion and later for encryption/decryption           |
| 9    | keylen            | input     | The core is initialised for the 128/256 bit configuration                         |
| 10   | IV[127:0]         | input     | The 128 bit Initialization_Vector value for CBC                                   |
| 11   | IV_updated        | input     | The core is initialised when to consider the IV for CBC                           |
| 12   | block_msg[127:0]  | input     | The 128 bit input block message for encryption/decryption                         |
| 13   | result[127:0]     | output    | The 128 bit encrypted/decrypted message                                           |
| 14   | result_valid      | output    | Indicates that the /encryption/decryption is done                                 |

When init_cmd is received, the core module uses the incoming 256 bit key and starts keyexpansion to generate either 10/14 roundkeys based on the incoming keylen.
Once the keyexpansion is done, the core is ready to receive IV_updated. If the core receives IV_updated, it uses incoming IV value else the previous value will be used.
When next_cmd is received, the core starts performing the encryption/decryption. It asserts the ready signal once the encryption/decryption is done. 
## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut.

**properties** folder contains **global_package.sv** where all the required functions are implemented either for AES encryption or  decryption

### fv_keymem

 **fv_doe_keymem** folder contains the assertion IP(AIP) for the submodule doe_key_mem along with the constraints for the respective AIP. When this submodule is verified individually considers constraints that are in **fv_doe_keymem/fv_constraints.sv** else all inputs are driven from DUT.

- reset_a: Checks that the ready is low and the state is idle.

- IDLE_to_IDLE_a: Checks if there isn't any init_cmd in idle state and then the state stays in  idle and holds the past value of ready.

- IDLE_to_keyExpansion128_a: Checks if there is init_cmd in idle state and there isn't keylen input and then the state changes to keyexpansion for 128 bit config and verify that the ready is still low during keyexpansion.

- IDLE_to_keyExpansion256_a: Checks if there is init_cmd in idle state and there is keylen input and then the state changes to keyexpansion for 256 bit config and verify that the ready is still low during keyexpansion.

- roundkey_check_128_cbc_a: Checks that once the keyexpansion is done, doe_key_mem module sends out correct round_key of 128bit configuration based on the round input.

- roundkey_check_256_cbc_a: Checks that once the keyexpansion is done, doe_key_mem module sends out correct round_key of 256bit configuration based on the round input.

### fv_encrypt

 **fv_doe_encryption** folder contains the assertion IP(AIP) for the submodule doe_encipher_block along with the constraints for the respective AIP. When this submodule is verified individually considers constraints that are in **fv_doe_encryption/fv_constraints.sv** else all inputs are driven from DUT.

- reset_a: Checks that the ready is high and the state is idle.

- encryption_check_128_a: Checks that once the encryption is done, doe_encipher_block module sends out the encrypted 128bit message to new_block along with the ready signal

- round_check_128_a: Checks that round output sends out the correct round number during the encryption of 128 bit block message

- encryption_check_256_a: Checks that once the encryption is done, doe_encipher_block module sends out the encrypted 256bit message to new_block along with the ready signal

- round_check_256_a: Checks that round output sends out the correct round number during the encryption of 256 bit block message

### fv_decrypt

 **fv_doe_decryption** folder contains the assertion IP(AIP) for the submodule doe_decipher_block along with the constraints for the respective AIP. When this submodule is verified individually considers constraints that are in **fv_doe_decryption/fv_constraints.sv** else all inputs are driven from DUT.

- reset_a: Checks that the ready is high and the state is idle.

- decryption_check_128_a: Checks that once the decryption is done, doe_encipher_block module sends out the encrypted 128bit message to new_block along with the ready signal

- round_check_128_a: Checks that round output sends out the correct round number during the decryption of 128 bit block message

- decryption_check_256_a: Checks that once the decryption is done, doe_encipher_block module sends out the encrypted 256bit message to new_block along with the ready signal

- round_check_256_a: Checks that round output sends out the correct round number during the decryption of 256 bit block message


### fv_doe_iv_process

 **fv_doe_iv** folder contains the assertion IP(AIP) for the IV_Controller implementation for CBC in DUT. This checker uses the same set of constraints that on the doe_core_cbc module which are in **properties/fv_constraints.sv**.

 **doe_iv_process_pkg.sv** consists of defined struct of input data taht will be used in the **fv_doe_iv_process** checker

- reset_a: Checks that the ready is high and the state is idle.

- enc_to_idle_a: Checks if encryption is done and state changes to idle while IV_controller loads IV_encry with the encrypted message

- idle_to_enc_a: Checks if there is next_cmd in idle state and there is encdec input and then the state changes to enc.

- idle_to_dec_first_a:  Checks if the block switches from idle state to first decrypt state upon receiving next_cmd and updates IV_decry with the IV, IV_decry_next with incoming block message

- dec_first_to_dec_next_a: Checks if the block switches from first decrypt state to next decrypt state upon receiving next_cmd  and updates IV_decry with the previous IV_decry_next, IV_decry_next with incoming block message

- dec_next_to_dec_first_a: Checks if the block switches from next decrypt state to first decrypt state in next cycle and holds values of IV_decry, IV_decry_next from previous state

- dec_first_to_idle_a: Checks if the block switches from first decrypt state to idle state upon receiving IV_updated and updates IV_decry, IV_decry_next with incoming IV

- enc_wait_a: Checks if encryption is done else wait in the same state until encryption is finished

- dec_first_wait_a: Checks if the block waits in first decrypt state until new decryption starts or IV_updated is received

- idle_wait_a: Checks if there is encryption or decryption request in idle and waits in the same state until either of them are received


### fv_doe_cbc_inst

 **properties** folder contains the assertion IP(AIP) for few of the primary outputs in DUT that are not covered in the previous checkers. This checker uses the same set of constraints that on the doe_core_cbc module which are in **properties/fv_constraints.sv**.

- result_valid_enc_a: Checks if result_valid is asserted once after the encryption is done.

- result_valid_dec_a: Checks if result_valid is asserted once after the decryption is done.

- ready_kemem_a: Checks if ready is asserted once after the keyexpansion is done.

- ready_enc_a: Checks if ready is asserted once after the encryption is done.

- result_enc_a: Checks if result is stored with the encrypted message once the encryption is done.

- result_dec_a: Checks if result is stored with the decrypted message once the decryption is done.

- sbox_check_a: Checks if doe_sbox block produces correct values

### fv_coverpoints

- cover_zeroize: Checks that the ready is high and the state is idle.

- cover_zeroize_after_next: Assert zeroize input and check the status of all registers. All registers/internal memories should be cleared.

- cover_multiple_next: Cover that checks multiple next_cmd can be received for CBC encryption/decryption.

- cover_transition_keyexp_to_iv: Cover that checks IV_updated asserted once the keyexapnsion is done

- cover_transition_keyexp_to_encdec: Cover that checks if design can have a trandition from keyexpansion to encryption/decryption

- cover_transition_keyexp_to_keyexp: Cover that checks if design can have a trandition from keyexpansion to keyexpansion

- cover_transition_encdec_to_encdec: Cover that checks if design can have a trandition from encryption/decryption to encryption/decryption

- cover_transition_encdec_to_keyexp: Cover that checks if design can have a trandition from encryption/decryption to keyexpansion


# Reproduce results

**MACROS :** 
CBC_BIND 

- Differentiates the set of assertions and assumptions added when loaded with top as respective submodule or doe_core_cbc.

- When defined, the assertions and assumptions are considered based on doe_core_cbc module.

- When not defined, the assertions and assumptions are independednt of doe_core_cbc module.

- Differentiates the binding of the checker files when loaded with top as respective submodule or doe_core_cbc.

- When not defined, the inputs are open and necessary inputs are driven from the respective constraints

- When defined, the inputs are driven from doe_core_cbc based on constraints on doe_core_cbc module.


## Proving the submodules

- Load submodule as top in the formal tool.

- Load the checker files along with the constraints and respective packages in the formal tool.

- Run the properties with ASSERT_BIND macro defined to verify that submodule behaves as intended.

## Proving the top 

- Load all design files in the formal tool and set doe_core_cbc as top module.

- Load all the checker files with CBC_BIND macro defined along with the constraints and respective packages in the formal tool.

- Copy all the submodule assertions, covers and assumptions into seperate task and cut the signals from the top that affect the submodule verification.

- On the main task, disable all submodule assumptions and just keep the assumptions on the doe_core_cbc module.

- Run the properties on the main task to verify that the  top module behaves as intended.

- Switch the tasks to one of the submodules which consists of the assumptions and assertions of that particular submodule.

- Run the properties on each submodule task to verify that the submodule behaves as intended.


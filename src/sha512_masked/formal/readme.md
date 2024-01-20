# SHA512_MASKED
Date: 28-06-2023
Author: LUBIS EDA

## Folder Structure
The following subdirectories are part of the main directory **formal**

- properties: Contains the assertion IP(AIP) named as **fv_sha512_masked.sv** and the constraints in place for the respective AIP **fv_constraints.sv**


## DUT Overview

The DUT sha512_core has the primary inputs and primary outputs as shown below.

| S.No | Port               | Direction | Description                                                                       |
| ---- | -------------------| --------- | --------------------------------------------------------------------------------- |
| 1    | clk                | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n            | input     | The reset signal is active low and resets the core                                |
| 3    | zeroize            | input     | The core is reseted when this signal is triggered.                                |
| 4    | init_cmd           | input     | The core is initialised with respective mode constants and processes the message. |
| 5    | next_cmd           | input     | The core processes the message block with the previously computed results         |
| 6    | mode[1:0]          | input     | Define which hash function: SHA512,SHA384,SHA224,SHA256                           |
| 7    | block_msg[1023:0]  | input     | The padded block message                                                          |
| 8    | lfsr_seed[73:0]    | input     | random bit vectors that are left shifted and rotated                              |
| 9    | ready              | output    | When triggered indicates that the core is ready                                   |
| 10   | digest[511:0]      | output    | The hashed value of the given message block                                       |
| 11   | digest_valid       | output    | When triggered indicates that the computed digest is ready                        |

When the respective mode is selected and initalised the core iterates for 80 rounds to process the hash value with random lfsr seed value so as a countermeasure for single channel side-attacks. if the next is triggered then the previous values of the **H** registers are in place for processing the hash value. The digest is always generated of 512 bits, in which if the mode changes to 384 then from MSB 384 bits is a valid output and rest is garbage value.
## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst** in binded with the DUT (reset_n && !zeroize), which ensures the reset functionality. And another AIP signal block_in_valid is triggered whenever the init or next is high.

- reset_a: Checks that all the resgiters are resetted and the state is idle, with the ready to high.

- DONE_to_IDLE_a: Checks the necessary registers, outputs holds the values when state transits from Done to idle.

- IDLE_to_CTRL_RND_a: Checks if the state is in idle, if there is an init_cmd or next_cmd, state transists to CTRL_RND and checks if the state registers are unchanged and round counter remains zero.

- CTRL_RND_TO_CTRL_RND: State transition remains CTRL_RND as long as the round_counter values is less than 9 and checks the necessary registers, masking register holds corrcet value.

- CTRL_RND_to_SHA_Rounds_224_a: Checks if the state is in ctrl_rnd ,the mode choosen as 224,the init is triggered then the registers should be initialised with the respective constants of 224.

- CTRL_RND_to_SHA_Rounds_256_a: Checks if the state is in ctrl_rnd ,the mode choosen as 256,the init is triggered then the registers should be initialised with the respective constants of 256.

- CTRL_RND_to_SHA_Rounds_512_a: Checks if the state is in ctrl_rnd ,the mode choosen as 512,the init is triggered then the registers should be initialised with the respective constants of 512.

- CTRL_RND_to_SHA_Rounds_384_a: Checks if the state is in ctrl_rnd ,the mode choosen is neither 512,256 nor 224,the init is triggered then the registers should be initialised with the respective constants of default, which covers 384 mode also.

- CTRL_RND_to_SHA_Rounds_next_a: Checks if the state is in ctrl_rnd and there is no init signal and the next signal asserts then the register holds the past values.

- SHA_Rounds_to_DONE_a: Checks if the rounds are done then the registers are updated correctly.

- SHA_Rounds_to_SHA_Rounds_before_16_a: Checks if the the rounds less than 16 then the necessary registers are updated correctly and the round increments.

- SHA_Rounds_to_SHA_Rounds_after_16_a: Checks if the rounds are greater than 16 and less than 80 then the respective registers are updated correctly and the round increments.

- IDLE_wait_a: Checks if there isn't either init or next signal triggered in idle state then the state stays in idle and holds the past values and the core is ready.


## Reproduce results
For reproducing the results: Load the AIP, sha512_masked_core and fv_constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts.

# Reproducing results and Notable changes from caliptra 1.0
The description of the proofs, is provided in the caliptra 1.0 version which are still valid.
**MACROS :** 
TOP 

- Used for the submodules fv_ecc_fau.sv and fv_scalar_blinding.sv and in fv_ecc_dsa_ctrl_constraints.sv.

- Use this macro or define this macro only when loading the design the with ecc_dsa_ctrl as top module.

FOR48

- This macro is used for fv_montmultiplier.sv as the montgomery multiplier shorter version end-to-end checkers. Due to the restriction of the formal tool overmultiplication this file is used for only reduced version of the design. This macro is for 48 bit version and radix as 4 which reproduces the same number of processing elements instantiations in the original version(384 bit and radix 48 bit). If this macro isn't enabled then 16 bit version of the multiplier proofs are set (16bit and Radix as 2)

## Notable changes from caliptra 1.0

- The following sections for each module depicts the changes occurred
    # Montgomery Multiplier
        - Reduced version proofs for REG_SIZE 16 and 48 with RADIX 2 and 4 respectively
        - Created a set of five different primes, p_mu, q_mu, r_inv to run the proofs
        - Adapted the proofs for ecc_pe, ecc_pe_first and ecc_pe_final for RADIX 48 bit
        - Similary the proofs were adjusted for the fv_montmultiplier_glue.sv for the RADIX 48bit
    # HMAC_DRBG interface 
        - The interface has the lfsr_seed input previously of 148 bit wide in the latest version adopted the changes to 384 bit in the proofs
        - For hmac_drbg and hmac_core can have the same AIP as the caliptra 1.0 as verifying those modules we would cut out the outputs from sha_masked and lfsr_seed is only fed to sha_masked as entropy.


## Proving the submodules

- Load submodule as top in the formal tool.

- Load the checker files along with the constraints and respective packages in the formal tool. 

- Run the properties.

## Proving the top 

- Load all design files in the formal tool and set ecc_dsa_ctrl as top module, disable the proofs as mentioned in the sheet which are not for the top.

- Load all the checker files with respective macro defined along with the constraints and respective packages in the formal tool.

- Copy all the submodule assertions and assumptions and enable if they were disabled into seperate task and cut the signals from the top that affect the submodule verification.

    If the following modules are chossen as a task then the respective signals need to be cut.

  
    # ecc_add_sub_mod_alter

        - cut the signals add_en_i, sub_i
    
    # ecc_pm_sequencer

        - cut the signal addra
    
    # ecc_dsa_sequencer

        - cut the signal addra
    
    # ecc_pm_sequencer

        - cut the signal addra
    
    # ecc_ram_tdp_file

        - cut the signals wea,web,ena,enb
    
    # ecc_pm_ctrl

        - cut the signal ecc_cmd_i

    # ecc_hmac_drbg_interface
        - updates from previous version included the LFSR_SEED of 384 bit version into the proofs.
        - cut the signal counter_nonce, keygen_sign, hmac_drbg_i.drbg, hmac_drbg_i.ready,hmac_drbg_i.valid, internal signal counter_nonce. Constraints do the work by reducing the timing.

    # hmac_drbg

        - cut the signals init_cmd,next_cmd,nonce, entropy,u_sha512_core_h1.digest,
          u_sha512_core_h2.digest,HMAC_K.tag,HMAC_K.lfsr_inst_i.rnd
    
    # sha512_masked

        - cut the signals init_cmd,next_cmd,mode,block_msg,entropy

    # reduced versions
        - For montgomerymultiplier, scalar_blinding and ecc_pe_first modules, a reduced 
        version instantiations are created inside the module ecc_reduced_instatiations, these proofs could be created in a separate task as they are not part of the actual top design and these proofs should be disabled on the top.

- On the main task, disable all submodule assumptions(convert to assertions) and just keep the assumptions on the ecc_dsa_ctrl module.

- Run the properties on the main task .

- Switch the tasks to one of the submodules which consists of the assumptions and assertions of that particular submodule.

- Run the properties.

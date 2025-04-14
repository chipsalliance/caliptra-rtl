# Programmer's Guide

## Initialization Configuration

The software can update the SHA3 configurations only when the IP is in the idle state.
1. The software should check [`STATUS.sha3_idle`](sha3_reg.md#status-register) before updating the configurations.
The configuration request to [`CFG_SHADOWED`](sha3_reg.md#cfg_shadowed-register) will be discarded if [`STATUS.sha3_idle`](sha3_reg.md#status-register) is not 1.

2. The software must program [`CFG_SHADOWED.msg_endianness`](sha3_reg.md#cfg_shadowed-register) and [`CFG_SHADOWED.state_endianness`](sha3_reg.md#cfg_shadowed-register) at the initialization stage. These determine the byte order of incoming messages (msg_endianness) and the Keccak state output (state_endianness).
3. The software must configure [`CFG_SHADOWED.mode`](sha3_reg.md#cfg_shadowed-register) and [`CFG_SHADOWED.kstrength`](sha3_reg.md#cfg_shadowed-register) for hash algorithm and security strengh.
SHA3 engine only supports SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE-128 and SHAKE-256.

Please note about [`CFG_SHADOWED`](sha3_reg.md#cfg_shadowed-register) :

1. Two subsequent write operations with same value are required to change its content.
2. If the two write operations try to set a different value, a recoverable alert is triggered (See [`STATUS.ALERT_RECOV_CTRL_UPDATE_ERR`](sha3_reg.md#status-register)).
3. A read operation clears the internal phase tracking.
4. If storage error of [`CFG_SHADOWED`](sha3_reg.md#cfg_shadowed-register) happens, it will trigger a fatal fault alert (See [`STATUS.ALERT_FATAL_FAULT`](sha3_reg.md#status-register)).

## Software Initiated SHA3 process

This section describes the expected software process to run the SHA3 HW IP.

### Kick-off SHA3 engine
After the configuring, the software notifies the SHA3 engine to accept incoming messages by issuing Start command into [`CMD`](sha3_reg.md#cmd-register).
If Start command is not issued, the incoming message written to [`MSG_FIFO`](sha3_reg.md#msg_fifo-memory) is discarded.

### Notify SHA3 engine message input done
After the software pushes all messages into [`MSG_FIFO`](sha3_reg.md#msg_fifo-memory), it issues Process command to [`CMD`](sha3_reg.md#cmd-register) for SHA3 engine to complete the sponge absorbing process.
SHA3 hashing engine pads the incoming message as defined in the SHA3 specification.

### Get digest from SHA3 engine
After the SHA3 engine completes the sponge absorbing step, it generates `sha3_done` interrupt ([`notif_internal_intr_r.notif_cmd_done_sts`](sha3_reg.md#notif_internal_intr_r-register)).
Or the software can poll the [`STATUS.squeeze`](sha3_reg.md#status-register) bit until it becomes 1.

#### SHA3 case
In this stage, Software can read the digest value from [`STATE`](sha3_reg.md#state-memory).

#### SHAKE case
It is same as SHA3 case, if the desired digest length is not greater than Keccak rate.

If the desired digest length is greater than the Keccak rate, after the software reads the 1st rate of available Keccak state, the software needs to:
1. Issue an Run command for the Keccak round logic to run another full round.
2. Read next rate of digest from [`STATE`](sha3_reg.md#state-memory). Please notice that SHA3 engine will not raise any interrupts when the Keccak round completes the software initiated manual run. The software can only check [`STATUS.squeeze`](sha3_reg.md#status-register) register field for the readiness of [`STATE`](sha3_reg.md#state-memory) value.

By repeating these two steps above, software can get all desired digest.

## Software release SHA3

After the software reads all the digest values, it issues Done command to [`CMD`](sha3_reg.md#cmd-register) register to clear the internal states and release sha3 engine.
Done command clears the Keccak state, FSM in SHA3, and a few internal variables.
Software programmed values won't be reset.

## Endianness

This SHA3 HW IP operates in little-endian.
Internal SHA3 hashing engine receives in 64-bit granularity.
The data written to SHA3 is assumed to be little endian.

The software may write/read the data in big-endian order if [`CFG_SHADOWED.msg_endianness`](sha3_reg.md#cfg_shadowed-register) or [`CFG_SHADOWED.state_endianness`](sha3_reg.md#cfg_shadowed-register) is set to 1.
If the endianness bit is 1, the data is assumed to be big-endian.
So, the internal logic byte-swap the data.
For example, when the software writes `0xDEADBEEF` with endianness as 1, the logic converts it to `0xEFBEADDE` then writes into MSG_FIFO.

## Error Handling

When the SHA3 HW IP encounters an error, it raises the `SHA3_err` IRQ ([`error_internal_intr_r.error0_sts`](sha3_reg.md#error_internal_intr_r-register)).
SW can then read the [`ERR_CODE`](sha3_reg.md#err_code-register) CSR to obtain more information about the error.
Having handled that IRQ, SW is expected to clear the `error0_sts` bit in the [`error_internal_intr_r`](sha3_reg.md#error_internal_intr_r-register) CSR before exiting the ISR.
When SW has handled the error condition, it is expected to set the `err_processed` bit in the [`CMD`](sha3_reg.md#cmd-register) CSR.
The internal SHA3 engine then flushes its FIFOs and state, which may take a few cycles.
The SHA3 HW IP is ready for operation again as soon as the `sha3_idle` bit in the [`STATUS`](sha3_reg.md#status-register) CSR is set; SW must not change the configuration of or send commands to the SHA3 HW IP before that.
The `sha3_done` IRQ([`notif_internal_intr_r.notif_cmd_done_sts`](sha3_reg.md#notif_internal_intr_r-register)) is raised when the SHA3 HW IP is ready again.

## SHA3 context switching

This version of SHA3 HW IP _does not_ support the software context switching.
A context switching scheme would allow software to save the current hashing engine state and initiate a new high priority hashing operation.
It could restore the previous hashing state later and continue the operation.

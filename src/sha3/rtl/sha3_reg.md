<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: sha3_reg
  - sha3_reg.rdl
-->

## sha3_reg address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x1000

<p>address maps for SHAKE accelerator register space</p>

|Offset|   Identifier  |                            Name                           |
|------|---------------|-----------------------------------------------------------|
| 0x000|  SHA3_NAME[0] |     SHA3/SHAKE component name register type definition    |
| 0x004|  SHA3_NAME[1] |     SHA3/SHAKE component name register type definition    |
| 0x008|SHA3_VERSION[0]|   SHA3/SHAKE component version register type definition   |
| 0x00C|SHA3_VERSION[1]|   SHA3/SHAKE component version register type definition   |
| 0x01C|   ALERT_TEST  |          SHA3/SHAKE component Alert Test Register         |
| 0x020|   CFG_REGWEN  |SHA3/SHAKE component Write enable for CFG_SHADOWED register|
| 0x024|  CFG_SHADOWED |        SHA3/SHAKE component Configuration register        |
| 0x028|      CMD      |           SHA3/SHAKE component command register           |
| 0x02C|     STATUS    |            SHA3/SHAKE component status register           |
| 0x0D0|    ERR_CODE   |          SHA3/SHAKE component error code register         |
| 0x200|     STATE     |          SHA3/SHAKE component Keccak State memory         |
| 0x400| intr_block_rf |                  Interrupt Register Block                 |
| 0xC00|    MSG_FIFO   |             SHA3/SHAKE component Message FIFO             |

### SHA3_NAME register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

<p>Two 32-bit read-only registers representing the name
of SHA3/SHAKE component.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   NAME   |   r  |  —  |  — |

#### NAME field

<p>Name field</p>

### SHA3_NAME register

- Absolute Address: 0x4
- Base Offset: 0x0
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

<p>Two 32-bit read-only registers representing the name
of SHA3/SHAKE component.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   NAME   |   r  |  —  |  — |

#### NAME field

<p>Name field</p>

### SHA3_VERSION register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

<p>Two 32-bit read-only registers representing of the version
of SHA3/SHAKE component.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  VERSION |   r  |  —  |  — |

#### VERSION field

<p>Version field</p>

### SHA3_VERSION register

- Absolute Address: 0xC
- Base Offset: 0x8
- Size: 0x4
- Array Dimensions: [2]
- Array Stride: 0x4
- Total Size: 0x8

<p>Two 32-bit read-only registers representing of the version
of SHA3/SHAKE component.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  VERSION |   r  |  —  |  — |

#### VERSION field

<p>Version field</p>

### ALERT_TEST register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

|Bits|     Identifier    |Access|Reset|Name|
|----|-------------------|------|-----|----|
|  0 |RECOV_OPERATION_ERR|   w  | 0x0 |  — |
|  1 |  FATAL_FAULT_ERR  |   w  | 0x0 |  — |

#### RECOV_OPERATION_ERR field

<p>Write 1 to trigger one alert event of this kind.</p>

#### FATAL_FAULT_ERR field

<p>Write 1 to trigger one alert event of this kind.</p>

### CFG_REGWEN register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |    en    |   r  | 0x1 |  — |

#### en field

<p>Configuration enable.</p>

### CFG_SHADOWED register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>This register is shadowed and protected by CFG_REGWEN.en
1. Two subsequent write operation are required to change its content,
If the two write operations try to set a different value, a recoverable alert is triggered (See Status Register).
2. A read operation clears the internal phase tracking.
3. If storage error(~staged_reg!=committed_reg) happen, it will trigger fatal fault alert</p>

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
| 3:1|    kstrength   |  rw  | 0x0 |  — |
| 5:4|      mode      |  rw  | 0x0 |  — |
|  8 | msg_endianness |  rw  | 0x0 |  — |
|  9 |state_endianness|  rw  | 0x0 |  — |

#### kstrength field

<p>Hashing Strength, Protected by CFG_REGWEN.en 
bit field to select the security strength of SHA3 hashing engine. 
If mode field is set to SHAKE, only 128 and 256 strength can be selected. 
Other value will result error when hashing starts.</p>

| Value | Name | Description |
|-------|------|-------------|
| 0x0   | L128 | 128-bit strength |
| 0x1   | L224 | 224-bit strength |
| 0x2   | L256 | 256-bit strength |
| 0x3   | L384 | 384-bit strength |
| 0x4   | L512 | 512-bit strength |

#### mode field

<p>Keccak hashing mode, Protected by CFG_REGWEN.en
This module supports SHA3 main hashing algorithm and the part of its derived functions, 
SHAKE with limitations. This field is to select the mode.</p>

| Value | Name | Description |
|-------|------|-------------|
| 0x0   | SHA3 | Standard SHA3 hashing |
| 0x1   | SHAKE | SHAKE hashing mode |
   

#### msg_endianness field

<p>Protected by CFG_REGWEN.en
If 1 then each individual multi-byte value, regardless of its alignment, 
written to MSG_FIFO will be added to the message in big-endian byte order. 
If 0, each value will be added to the message in little-endian byte order. 
A message written to MSG_FIFO one byte at a time will not be affected by this setting. 
From a hardware perspective byte swaps are performed on a TL-UL word granularity.</p>

#### state_endianness field

<p>Protected by CFG_REGWEN.en
If 1 then each individual multi-byte value, regardless of its alignment, 
written to MSG_FIFO will be added to the message in big-endian byte order. 
If 0, each value will be added to the message in little-endian byte order. 
A message written to MSG_FIFO one byte at a time will not be affected by this setting. 
From a hardware perspective byte swaps are performed on a TL-UL word granularity.</p>

### CMD register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

|Bits|  Identifier |  Access |Reset|Name|
|----|-------------|---------|-----|----|
| 5:0|     cmd     |rw, woclr| 0x0 |  — |
| 10 |err_processed|rw, woclr| 0x0 |  — |

#### cmd field

<p>Issues a command to the SHA3 IP. The command is sparse encoded. 
To prevent sw from writing multiple commands at once, the field is defined as enum.
Always return 0 for SW reads.
START: Writing 6'b011101 or dec 29 into this field when SHA3/SHAKE is in idle, SHA3/SHAKE begins its operation and start absorbing.
PROCESS: Writing 6'b101110 or dec 46 into this field when SHA3/SHAKE began its operation and received the entire message, it computes the digest or signing.
RUN: The run field is used in the sponge squeezing stage. 
It triggers the Keccak round logic to run full 24 rounds. 
This is optional and used when software needs more digest bits than the keccak rate. 
It only affects when the SHA3/SHAKE operation is completed.
DONE: Writing 6'b010110 or dec 22 into this field when SHA3 squeezing is completed, 
SHA3/SHAKE hashing engine clears internal variables and goes back to Idle state for next command.</p>

| Value (hex) | Value (bin) | Name | Description |
|-------------|-------------|------|-------------|
| 0x1D | 6'b011101 | START | Start SHA3/SHAKE operation and begin absorbing |
| 0x2E | 6'b101110 | PROCESS | Process the entire message and compute digest |
| 0x31 | 6'b110001 | RUN | Run Keccak round logic for squeezing stage |
| 0x16 | 6'b010110 | DONE | Clear internal state and return to idle |

#### err_processed field

<p>When error occurs and one of the state machine stays at Error handling state, 
SW may process the error based on ERR_CODE, then let FSM back to the reset state.
Always return 0 for SW reads.</p>

### STATUS register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

|Bits|         Identifier        |Access|Reset|Name|
|----|---------------------------|------|-----|----|
|  0 |         sha3_idle         |   r  | 0x1 |  — |
|  1 |        sha3_absorb        |   r  | 0x0 |  — |
|  2 |        sha3_squeeze       |   r  | 0x0 |  — |
|12:8|         fifo_depth        |   r  | 0x0 |  — |
| 14 |         fifo_empty        |   r  | 0x1 |  — |
| 15 |         fifo_full         |   r  | 0x0 |  — |
| 16 |     ALERT_FATAL_FAULT     |   r  | 0x0 |  — |
| 17 |ALERT_RECOV_CTRL_UPDATE_ERR|   r  | 0x0 |  — |

#### sha3_idle field

<p>If 1, SHA3 hashing engine is in idle state.</p>

#### sha3_absorb field

<p>If 1, SHA3 is receiving message stream and processing it</p>

#### sha3_squeeze field

<p>If 1, SHA3 completes sponge absorbing stage. In this stage, SW can manually run the hashing engine.</p>

#### fifo_depth field

<p>Count of occupied entries in the message FIFO.</p>

#### fifo_empty field

<p>Message FIFO Empty indicator.
The FIFO's Pass parameter is set to 1'b 1. So, by default, if the SHA engine is ready, the write data to FIFO just passes through.
In this case, fifo_depth remains 0. fifo_empty, however, lowers the value to 0 for a cycle, then goes back to the empty state, 1.
See the Message FIFO section in the spec for the reason.</p>

#### fifo_full field

<p>Message FIFO Full indicator.</p>

#### ALERT_FATAL_FAULT field

<p>No fatal fault has occurred inside the SHA3 unit (0). 
A fatal fault has occured and the SHA3 unit needs to be reset (1), 
Examples for such faults include i) TL-UL bus integrity fault 
ii) storage errors in the shadow registers 
iii) errors in the message, round, or key counter 
iv) any internal FSM entering an invalid state.</p>

#### ALERT_RECOV_CTRL_UPDATE_ERR field

<p>An update error has not occurred (0) or has occured (1) in the shadowed Control Register. 
SHA3 operation needs to be restarted by re-writing the Control Register.</p>

### ERR_CODE register

- Absolute Address: 0xD0
- Base Offset: 0xD0
- Size: 0x4

<p>SHA3 Error Code</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0| ERR_CODE |   r  | 0x0 |  — |

#### ERR_CODE field

<p>If the error_internal_intr_r.error0_sts interrupt occurs, this register has information on the error cause.
Bits 31:24 contain the error code for the encoding, and bits 23:0 contain additional debug information.
This register does <em>not</em> get cleared when the error_internal_intr_r.error0_sts interrupt state gets cleared.</p>

| Value | Name | Description |
|-------|------|-------------|
| 0x00  | ErrNone | No error |
| 0x02  | ERR_SW_PUSHED_MSGFIFO | Software pushed message to FIFO incorrectly |
| 0x06  | ErrUnexpectedModeStrength | Unexpected mode/strength combination |
| 0x07  | ERR_INCORRECT_FUNCTION_NAME | Incorrect function name |
| 0x08  | ERR_SW_CMD_SEQUENCE | Incorrect command sequence |
| 0xC1  | ERR_FATAL_ERROR | Fatal error occurred |


## STATE memory

- Absolute Address: 0x200
- Base Offset: 0x200
- Size: 0x200

<p>Keccak State (1600 bit) memory.
The software can get the processed digest by reading this memory
region. Unlike MSG_FIFO, STATE memory space sees the addr[9:0].
If Masking feature is enabled, the software reads two shares from
this memory space.
0x200 - 0x2C7: State share
for Keccak State access:
1. Output length &lt;= rate length, sha3_done will be raised or software can poll STATUS.squeeze become 1.
2. Output length &gt; rate length, after software read 1st keccak state, software should issue run cmd to trigger Keccak round logic to run full 24 rounds.
And then software should check STATUS.squeeze register field for the readiness of STATE value(SHA3 FSM become MANUAL_RUN before keccak state complete).</p>

No supported members.


## intr_block_rf register file

- Absolute Address: 0x400
- Base Offset: 0x400
- Size: 0x214

<p>Set of registers to implement interrupt functionality</p>

|Offset|           Identifier           |                         Name                        |
|------|--------------------------------|-----------------------------------------------------|
| 0x000|        global_intr_en_r        |          Per-Type Interrupt Enable Register         |
| 0x004|         error_intr_en_r        |         Per-Event Interrupt Enable Register         |
| 0x008|         notif_intr_en_r        |         Per-Event Interrupt Enable Register         |
| 0x00C|       error_global_intr_r      |Interrupt Status Aggregation Register type definition|
| 0x010|       notif_global_intr_r      |Interrupt Status Aggregation Register type definition|
| 0x014|      error_internal_intr_r     |      Interrupt Status Register type definition      |
| 0x018|      notif_internal_intr_r     |      Interrupt Status Register type definition      |
| 0x01C|        error_intr_trig_r       |      Interrupt Trigger Register type definition     |
| 0x020|        notif_intr_trig_r       |      Interrupt Trigger Register type definition     |
| 0x100|       error0_intr_count_r      |               Interrupt Event Counter               |
| 0x104|       error1_intr_count_r      |               Interrupt Event Counter               |
| 0x108|       error2_intr_count_r      |               Interrupt Event Counter               |
| 0x10C|       error3_intr_count_r      |               Interrupt Event Counter               |
| 0x180|   notif_cmd_done_intr_count_r  |               Interrupt Event Counter               |
| 0x200|    error0_intr_count_incr_r    |          Interrupt Event Count Incrementor          |
| 0x204|    error1_intr_count_incr_r    |          Interrupt Event Count Incrementor          |
| 0x208|    error2_intr_count_incr_r    |          Interrupt Event Count Incrementor          |
| 0x20C|    error3_intr_count_incr_r    |          Interrupt Event Count Incrementor          |
| 0x210|notif_cmd_done_intr_count_incr_r|          Interrupt Event Count Incrementor          |

### global_intr_en_r register

- Absolute Address: 0x400
- Base Offset: 0x0
- Size: 0x4

<p>Dedicated register with one bit for each event type that may produce an interrupt.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 | error_en |  rw  | 0x0 |  — |
|  1 | notif_en |  rw  | 0x0 |  — |

#### error_en field

<p>Global enable bit for all events of type 'Error'</p>

#### notif_en field

<p>Global enable bit for all events of type 'Notification'</p>

### error_intr_en_r register

- Absolute Address: 0x404
- Base Offset: 0x4
- Size: 0x4

<p>Dedicated register with one bit for each event that may produce an interrupt.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 | error0_en|  rw  | 0x0 |  — |
|  1 | error1_en|  rw  | 0x0 |  — |
|  2 | error2_en|  rw  | 0x0 |  — |
|  3 | error3_en|  rw  | 0x0 |  — |

#### error0_en field

<p>Enable bit for Event 0. 
If enabled, interrupt will be asserted 
if there is a SHAKE configuration error.</p>

#### error1_en field

<p>Enable bit for Event 1</p>

#### error2_en field

<p>Enable bit for Event 2</p>

#### error3_en field

<p>Enable bit for Event 3</p>

### notif_intr_en_r register

- Absolute Address: 0x408
- Base Offset: 0x8
- Size: 0x4

<p>Dedicated register with one bit for each event that may produce an interrupt.</p>

|Bits|       Identifier      |Access|Reset|Name|
|----|-----------------------|------|-----|----|
|  0 |   notif_cmd_done_en   |  rw  | 0x0 |  — |
|  1 |notif_msg_fifo_empty_en|  rw  | 0x0 |  — |

#### notif_cmd_done_en field

<p>Enable bit for Command Done Interrupt.
Interrupt is asserted when there is valid digest to be read.</p>

#### notif_msg_fifo_empty_en field

<p>Enable bit for MSG FIFO Empty Interrupt.
Interrupt is asserted when MSG FIFO Is Empty.</p>

### error_global_intr_r register

- Absolute Address: 0x40C
- Base Offset: 0xC
- Size: 0x4

<p>Single bit indicating occurrence of any interrupt event
of a given type. E.g. Notifications and Errors may drive
to two separate interrupt registers. There may be
multiple sources of Notifications or Errors that are
aggregated into a single interrupt pin for that
respective type. That pin feeds through this register
in order to apply a global enablement of that interrupt
event type.
Nonsticky assertion.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  agg_sts |   r  | 0x0 |  — |

#### agg_sts field

<p>Interrupt Event Aggregation status bit</p>

### notif_global_intr_r register

- Absolute Address: 0x410
- Base Offset: 0x10
- Size: 0x4

<p>Single bit indicating occurrence of any interrupt event
of a given type. E.g. Notifications and Errors may drive
to two separate interrupt registers. There may be
multiple sources of Notifications or Errors that are
aggregated into a single interrupt pin for that
respective type. That pin feeds through this register
in order to apply a global enablement of that interrupt
event type.
Nonsticky assertion.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  agg_sts |   r  | 0x0 |  — |

#### agg_sts field

<p>Interrupt Event Aggregation status bit</p>

### error_internal_intr_r register

- Absolute Address: 0x414
- Base Offset: 0x14
- Size: 0x4

<p>Single bit indicating occurrence of each interrupt event.
Sticky, level assertion, write-1-to-clear.
SHA3 error occurred. ERR_CODE register shows the details</p>

|Bits|Identifier|  Access |Reset|Name|
|----|----------|---------|-----|----|
|  0 |error0_sts|rw, woclr| 0x0 |  — |
|  1 |error1_sts|rw, woclr| 0x0 |  — |
|  2 |error2_sts|rw, woclr| 0x0 |  — |
|  3 |error3_sts|rw, woclr| 0x0 |  — |

#### error0_sts field

<p>Interrupt Event 0 status bit; Used to indicate SHA3 error.</p>

#### error1_sts field

<p>Interrupt Event 1 status bit</p>

#### error2_sts field

<p>Interrupt Event 2 status bit</p>

#### error3_sts field

<p>Interrupt Event 3 status bit</p>

### notif_internal_intr_r register

- Absolute Address: 0x418
- Base Offset: 0x18
- Size: 0x4

<p>Single bit indicating occurrence of each interrupt event.
Sticky, level assertion, write-1-to-clear.</p>

|Bits|       Identifier       |  Access |Reset|Name|
|----|------------------------|---------|-----|----|
|  0 |   notif_cmd_done_sts   |rw, woclr| 0x0 |  — |
|  1 |notif_msg_fifo_empty_sts|    r    | 0x0 |  — |

#### notif_cmd_done_sts field

<p>SHA3 cmd_done indicate 
1. SHA3 absorbing has been completed, 1st rate of digest is ready.</p>

#### notif_msg_fifo_empty_sts field

<p>MSG_FIFO Empty Interrupt status bit.
This interrupt is raised only if the message FIFO is actually writable by software, i.e., if all of the following conditions are met:
i) The SHA3 block is in the Absorb state.
ii) Software has not yet written the Process command to finish the absorption process.
For the interrupt to be raised, the message FIFO must also have been full previously.
Otherwise, the hardware empties the FIFO faster than software can fill it 
and there is no point in interrupting the software to inform it about the message FIFO being empty.</p>

### error_intr_trig_r register

- Absolute Address: 0x41C
- Base Offset: 0x1C
- Size: 0x4

<p>Single bit for each interrupt event allows SW to manually
trigger occurrence of that event. Upon SW write, the trigger bit
will pulse for 1 cycle then clear to 0. The pulse on the
trigger register bit results in the corresponding interrupt
status bit being set to 1.</p>

|Bits| Identifier|  Access |Reset|Name|
|----|-----------|---------|-----|----|
|  0 |error0_trig|rw, woset| 0x0 |  — |
|  1 |error1_trig|rw, woset| 0x0 |  — |
|  2 |error2_trig|rw, woset| 0x0 |  — |
|  3 |error3_trig|rw, woset| 0x0 |  — |

#### error0_trig field

<p>Interrupt Trigger 0 bit</p>

#### error1_trig field

<p>Interrupt Trigger 1 bit</p>

#### error2_trig field

<p>Interrupt Trigger 2 bit</p>

#### error3_trig field

<p>Interrupt Trigger 3 bit</p>

### notif_intr_trig_r register

- Absolute Address: 0x420
- Base Offset: 0x20
- Size: 0x4

<p>Single bit for each interrupt event allows SW to manually
trigger occurrence of that event. Upon SW write, the trigger bit
will pulse for 1 cycle then clear to 0. The pulse on the
trigger register bit results in the corresponding interrupt
status bit being set to 1.</p>

|Bits|        Identifier       |  Access |Reset|Name|
|----|-------------------------|---------|-----|----|
|  0 |   notif_cmd_done_trig   |rw, woset| 0x0 |  — |
|  1 |notif_msg_fifo_empty_trig|rw, woset| 0x0 |  — |

#### notif_cmd_done_trig field

<p>Interrupt Trigger 0 bit</p>

#### notif_msg_fifo_empty_trig field

<p>MSG_FIFO Empty Interrupt Trigger 0 bit</p>

### error0_intr_count_r register

- Absolute Address: 0x500
- Base Offset: 0x100
- Size: 0x4

<p>Provides statistics about the number of events that have
occurred.
Will not overflow ('incrsaturate').</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    cnt   |  rw  | 0x0 |  — |

#### cnt field

<p>Count field</p>

### error1_intr_count_r register

- Absolute Address: 0x504
- Base Offset: 0x104
- Size: 0x4

<p>Provides statistics about the number of events that have
occurred.
Will not overflow ('incrsaturate').</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    cnt   |  rw  | 0x0 |  — |

#### cnt field

<p>Count field</p>

### error2_intr_count_r register

- Absolute Address: 0x508
- Base Offset: 0x108
- Size: 0x4

<p>Provides statistics about the number of events that have
occurred.
Will not overflow ('incrsaturate').</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    cnt   |  rw  | 0x0 |  — |

#### cnt field

<p>Count field</p>

### error3_intr_count_r register

- Absolute Address: 0x50C
- Base Offset: 0x10C
- Size: 0x4

<p>Provides statistics about the number of events that have
occurred.
Will not overflow ('incrsaturate').</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    cnt   |  rw  | 0x0 |  — |

#### cnt field

<p>Count field</p>

### notif_cmd_done_intr_count_r register

- Absolute Address: 0x580
- Base Offset: 0x180
- Size: 0x4

<p>Provides statistics about the number of events that have
occurred.
Will not overflow ('incrsaturate').</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    cnt   |  rw  | 0x0 |  — |

#### cnt field

<p>Count field</p>

### error0_intr_count_incr_r register

- Absolute Address: 0x600
- Base Offset: 0x200
- Size: 0x4

<p>Trigger the event counter to increment based on observing
the rising edge of an interrupt event input from the
Hardware. The same input signal that causes an interrupt
event to be set (sticky) also causes this signal to pulse
for 1 clock cycle, resulting in the event counter
incrementing by 1 for every interrupt event.
This is implemented as a down-counter (1-bit) that will
decrement immediately on being set - resulting in a pulse</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   pulse  |   r  | 0x0 |  — |

#### pulse field

<p>Pulse mirrors interrupt event occurrence</p>

### error1_intr_count_incr_r register

- Absolute Address: 0x604
- Base Offset: 0x204
- Size: 0x4

<p>Trigger the event counter to increment based on observing
the rising edge of an interrupt event input from the
Hardware. The same input signal that causes an interrupt
event to be set (sticky) also causes this signal to pulse
for 1 clock cycle, resulting in the event counter
incrementing by 1 for every interrupt event.
This is implemented as a down-counter (1-bit) that will
decrement immediately on being set - resulting in a pulse</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   pulse  |   r  | 0x0 |  — |

#### pulse field

<p>Pulse mirrors interrupt event occurrence</p>

### error2_intr_count_incr_r register

- Absolute Address: 0x608
- Base Offset: 0x208
- Size: 0x4

<p>Trigger the event counter to increment based on observing
the rising edge of an interrupt event input from the
Hardware. The same input signal that causes an interrupt
event to be set (sticky) also causes this signal to pulse
for 1 clock cycle, resulting in the event counter
incrementing by 1 for every interrupt event.
This is implemented as a down-counter (1-bit) that will
decrement immediately on being set - resulting in a pulse</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   pulse  |   r  | 0x0 |  — |

#### pulse field

<p>Pulse mirrors interrupt event occurrence</p>

### error3_intr_count_incr_r register

- Absolute Address: 0x60C
- Base Offset: 0x20C
- Size: 0x4

<p>Trigger the event counter to increment based on observing
the rising edge of an interrupt event input from the
Hardware. The same input signal that causes an interrupt
event to be set (sticky) also causes this signal to pulse
for 1 clock cycle, resulting in the event counter
incrementing by 1 for every interrupt event.
This is implemented as a down-counter (1-bit) that will
decrement immediately on being set - resulting in a pulse</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   pulse  |   r  | 0x0 |  — |

#### pulse field

<p>Pulse mirrors interrupt event occurrence</p>

### notif_cmd_done_intr_count_incr_r register

- Absolute Address: 0x610
- Base Offset: 0x210
- Size: 0x4

<p>Trigger the event counter to increment based on observing
the rising edge of an interrupt event input from the
Hardware. The same input signal that causes an interrupt
event to be set (sticky) also causes this signal to pulse
for 1 clock cycle, resulting in the event counter
incrementing by 1 for every interrupt event.
This is implemented as a down-counter (1-bit) that will
decrement immediately on being set - resulting in a pulse</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   pulse  |   r  | 0x0 |  — |

#### pulse field

<p>Pulse mirrors interrupt event occurrence</p>

## MSG_FIFO memory

- Absolute Address: 0xC00
- Base Offset: 0xC00
- Size: 0x400

<p>Message FIFO. window size is 1024 bytes.
Any write operation to this window will be appended to MSG_FIFO. SW can
simply write bytes/words to any address within this address range.
Ordering and packing of the incoming bytes/words are handled
internally. Therefore, the least significant 10 bits of the address
are ignored.</p>

No supported members.


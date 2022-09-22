// <copyright file="PicoStatus.cs" company="Pico Technology Ltd">
// Copyright(C) 2009-2018 Pico Technology Ltd. See LICENSE file for terms.
// </copyright>

namespace PicoStatus
{
    /// <summary>
    /// PICO_INFO Values
    /// </summary>
    public static class PicoInfo
    {
        public const uint PICO_DRIVER_VERSION = (uint)0x00000000UL;
        public const uint PICO_USB_VERSION = (uint)0x00000001UL;
        public const uint PICO_HARDWARE_VERSION = (uint)0x00000002UL;
        public const uint PICO_VARIANT_INFO = (uint)0x00000003UL;
        public const uint PICO_BATCH_AND_SERIAL = (uint)0x00000004UL;
        public const uint PICO_CAL_DATE = (uint)0x00000005UL;
        public const uint PICO_KERNEL_VERSION = (uint)0x00000006UL;

        public const uint PICO_DIGITAL_HARDWARE_VERSION = (uint)0x00000007UL;
        public const uint PICO_ANALOGUE_HARDWARE_VERSION = (uint)0x00000008UL;

        public const uint PICO_FIRMWARE_VERSION_1 = (uint)0x00000009UL;
        public const uint PICO_FIRMWARE_VERSION_2 = (uint)0x0000000AUL;

        public const uint PICO_MAC_ADDRESS = (uint)0x0000000BUL;

        public const uint PICO_SHADOW_CAL = (uint)0x0000000CUL;

        public const uint PICO_IPP_VERSION = (uint)0x0000000DUL;

        public const uint PICO_DRIVER_PATH = (uint)0x0000000EUL;
    }

    /// <summary>
    /// This class defines the status codes returned by a Pico device,
    /// a PC Oscilloscope or data logger and is based on the PicoStatus.h header file.
    /// </summary>
    /// <remarks>
    /// In comments, "-API-" is a placeholder for the name of the scope or data logger API.
    /// For example, for the ps5000a API, it stands for "PS5000A" Or "ps5000a".
    /// </remarks>
    public static class StatusCodes
    {
        /// <summary>The PicoScope is functioning correctly.</summary>
        public const uint PICO_OK = (uint)0x00000000UL;

        /// <summary>An attempt has been made to open more than -API-_MAX_UNITS.</summary>
        public const uint PICO_MAX_UNITS_OPENED = (uint)0x00000001UL;

        /// <summary>Not enough memory could be allocated on the host machine.</summary>
        public const uint PICO_MEMORY_FAIL = (uint)0x00000002UL;

        /// <summary>No Pico Technology device could be found.</summary>
        public const uint PICO_NOT_FOUND = (uint)0x00000003UL;

        /// <summary>Unable to download firmware.</summary>
        public const uint PICO_FW_FAIL = (uint)0x00000004UL;

        /// <summary>The driver is busy opening a device.</summary>
        public const uint PICO_OPEN_OPERATION_IN_PROGRESS = (uint)0x00000005UL;

        /// <summary>An unspecified failure occurred.</summary>
        public const uint PICO_OPERATION_FAILED = (uint)0x00000006UL;

        /// <summary>The PicoScope is not responding to commands from the PC.</summary>
        public const uint PICO_NOT_RESPONDING = (uint)0x00000007UL;

        /// <summary>The configuration information in the PicoScope is corrupt or missing.</summary>
        public const uint PICO_CONFIG_FAIL = (uint)0x00000008UL;

        /// <summary>The picopp.sys file is too old to be used with the device driver.</summary>
        public const uint PICO_KERNEL_DRIVER_TOO_OLD = (uint)0x00000009UL;

        /// <summary>The EEPROM has become corrupt, so the device will use a default setting.</summary>
        public const uint PICO_EEPROM_CORRUPT = (uint)0x0000000AUL;

        /// <summary>The operating system on the PC is not supported by this driver.</summary>
        public const uint PICO_OS_NOT_SUPPORTED = (uint)0x0000000BUL;

        /// <summary>There is no device with the handle value passed.</summary>
        public const uint PICO_INVALID_HANDLE = (uint)0x0000000CUL;

        /// <summary>A parameter value is not valid.</summary>
        public const uint PICO_INVALID_PARAMETER = (uint)0x0000000DUL;

        /// <summary>The timebase is not supported or is invalid.</summary>
        public const uint PICO_INVALID_TIMEBASE = (uint)0x0000000EUL;

        /// <summary>The voltage range is not supported or is invalid.</summary>
        public const uint PICO_INVALID_VOLTAGE_RANGE = (uint)0x0000000FUL;

        /// <summary>The channel number is not valid on this device or no channels have been set.</summary>
        public const uint PICO_INVALID_CHANNEL = (uint)0x00000010UL;

        /// <summary>The channel set for a trigger is not available on this device.</summary>
        public const uint PICO_INVALID_TRIGGER_CHANNEL = (uint)0x00000011UL;

        /// <summary>The channel set for a condition is not available on this device.</summary>
        public const uint PICO_INVALID_CONDITION_CHANNEL = (uint)0x00000012UL;

        /// <summary>The device does not have a signal generator.</summary>
        public const uint PICO_NO_SIGNAL_GENERATOR = (uint)0x00000013UL;

        /// <summary>Streaming has failed to start or has stopped without user request.</summary>
        public const uint PICO_STREAMING_FAILED = (uint)0x00000014UL;

        /// <summary>Block failed to start - a parameter may have been set wrongly.</summary>
        public const uint PICO_BLOCK_MODE_FAILED = (uint)0x00000015UL;

        /// <summary>A parameter that was required is NULL.</summary>
        public const uint PICO_NULL_PARAMETER = (uint)0x00000016UL;

        /// <summary>The current functionality is not available while using ETS capture mode.</summary>
        public const uint PICO_ETS_MODE_SET = (uint)0x00000017UL;

        /// <summary>No data is available from a run block call.</summary>
        public const uint PICO_DATA_NOT_AVAILABLE = (uint)0x00000018UL;

        /// <summary>The buffer passed for the information was too small.</summary>
        public const uint PICO_STRING_BUFFER_TO_SMALL = (uint)0x00000019UL;

        /// <summary>ETS is not supported on this device.</summary>
        public const uint PICO_ETS_NOT_SUPPORTED = (uint)0x0000001AUL;

        /// <summary>The auto trigger time is less than the time it will take to collect the pre-trigger data.</summary>
        public const uint PICO_AUTO_TRIGGER_TIME_TO_SHORT = (uint)0x0000001BUL;

        /// <summary>The collection of data has stalled as unread data would be overwritten.</summary>
        public const uint PICO_BUFFER_STALL = (uint)0x0000001CUL;

        /// <summary>Number of samples requested is more than available in the current memory segment.</summary>
        public const uint PICO_TOO_MANY_SAMPLES = (uint)0x0000001DUL;

        /// <summary>Not possible to create number of segments requested.</summary>
        public const uint PICO_TOO_MANY_SEGMENTS = (uint)0x0000001EUL;

        /// <summary>
        /// A null pointer has been passed in the trigger function
        /// or one of the parameters is out of range.
        /// </summary>
        public const uint PICO_PULSE_WIDTH_QUALIFIER = (uint)0x0000001FUL;

        /// <summary>One or more of the hold-off parameters are out of range.</summary>
        public const uint PICO_DELAY = (uint)0x00000020UL;

        /// <summary>One or more of the source details are incorrect.</summary>
        public const uint PICO_SOURCE_DETAILS = (uint)0x00000021UL;

        /// <summary>One or more of the conditions are incorrect.</summary>
        public const uint PICO_CONDITIONS = (uint)0x00000022UL;

        /// <summary>
        /// The driver's thread is currently in the -API-Ready callback function
        /// and therefore the action cannot be carried out.
        /// </summary>
        public const uint PICO_USER_CALLBACK = (uint)0x00000023UL;

        /// <summary>
        /// An attempt is being made to get stored data while streaming.
        /// Either stop streaming by calling -API-Stop, or use -API-GetStreamingLatestValues.
        /// </summary>
        public const uint PICO_DEVICE_SAMPLING = (uint)0x00000024UL;

        /// <summary>Data is unavailable because a run has not been completed.</summary>
        public const uint PICO_NO_SAMPLES_AVAILABLE = (uint)0x00000025UL;

        /// <summary>The memory segment index is out of range.</summary>
        public const uint PICO_SEGMENT_OUT_OF_RANGE = (uint)0x00000026UL;

        /// <summary>The device is busy so data cannot be returned yet.</summary>
        public const uint PICO_BUSY = (uint)0x00000027UL;

        /// <summary>The start time to get stored data is out of range.</summary>
        public const uint PICO_STARTINDEX_INVALID = (uint)0x00000028UL;

        /// <summary>The information number requested is not a valid number.</summary>
        public const uint PICO_INVALID_INFO = (uint)0x00000029UL;

        /// <summary>
        /// The handle is invalid so no information is available about the device.
        /// Only PICO_DRIVER_VERSION is available
        /// </summary>
        public const uint PICO_INFO_UNAVAILABLE = (uint)0x0000002AUL;

        /// <summary>The sample interval selected for streaming is out of range.</summary>
        public const uint PICO_INVALID_SAMPLE_INTERVAL = (uint)0x0000002BUL;

        /// <summary>ETS is set but no trigger has been set. A trigger setting is required for ETS.</summary>
        public const uint PICO_TRIGGER_ERROR = (uint)0x0000002CUL;

        /// <summary>Driver cannot allocate memory.</summary>
        public const uint PICO_MEMORY = (uint)0x0000002DUL;

        /// <summary>Incorrect parameter passed to the signal generator.</summary>
        public const uint PICO_SIG_GEN_PARAM = (uint)0x0000002EUL;

        /// <summary>Conflict between the shots and sweeps parameters sent to the signal generator.</summary>
        public const uint PICO_SHOTS_SWEEPS_WARNING = (uint)0x0000002FUL;

        /// <summary>A software trigger has been sent but the trigger source is not a software trigger.</summary>
        public const uint PICO_SIGGEN_TRIGGER_SOURCE = (uint)0x00000030UL;

        /// <summary>
        /// An -API-SetTrigger call has found a conflict
        /// between the trigger source and the AUX output enable.
        /// </summary>
        public const uint PICO_AUX_OUTPUT_CONFLICT = (uint)0x00000031UL;

        /// <summary>ETS mode is being used and AUX is set as an input.</summary>
        public const uint PICO_AUX_OUTPUT_ETS_CONFLICT = (uint)0x00000032UL;

        /// <summary>Attempt to set different EXT input thresholds set
        /// for signal generator and oscilloscope trigger.
        /// </summary>
        public const uint PICO_WARNING_EXT_THRESHOLD_CONFLICT = (uint)0x00000033UL;

        /// <summary>An -API-SetTrigger... function has set AUX as an output
        /// and the signal generator is using it as a trigger.
        /// </summary>
        public const uint PICO_WARNING_AUX_OUTPUT_CONFLICT = (uint)0x00000034UL;

        /// <summary>
        /// The combined peak to peak voltage and the analog offset voltage
        /// exceed the maximum voltage the signal generator can produce.
        /// </summary>
        public const uint PICO_SIGGEN_OUTPUT_OVER_VOLTAGE = (uint)0x00000035UL;

        /// <summary>NULL pointer passed as delay parameter.</summary>
        public const uint PICO_DELAY_NULL = (uint)0x00000036UL;

        /// <summary>The buffers for overview data have not been set while streaming.</summary>
        public const uint PICO_INVALID_BUFFER = (uint)0x00000037UL;

        /// <summary>The analog offset voltage is out of range.</summary>
        public const uint PICO_SIGGEN_OFFSET_VOLTAGE = (uint)0x00000038UL;

        /// <summary>The analog peak-to-peak voltage is out of range.</summary>
        public const uint PICO_SIGGEN_PK_TO_PK = (uint)0x00000039UL;

        /// <summary>A block collection has been canceled.</summary>
        public const uint PICO_CANCELLED = (uint)0x0000003AUL;

        /// <summary>The segment index is not currently being used.</summary>
        public const uint PICO_SEGMENT_NOT_USED = (uint)0x0000003BUL;

        /// <summary>The wrong GetValues function has been called for the collection mode in use.</summary>
        public const uint PICO_INVALID_CALL = (uint)0x0000003CUL;

        /// <summary></summary>
        public const uint PICO_GET_VALUES_INTERRUPTED = (uint)0x0000003DUL;

        /// <summary>The function is not available.</summary>
        public const uint PICO_NOT_USED = (uint)0x0000003FUL;

        /// <summary>The aggregation ratio requested is out of range.</summary>
        public const uint PICO_INVALID_SAMPLERATIO = (uint)0x00000040UL;

        /// <summary>Device is in an invalid state.</summary>
        public const uint PICO_INVALID_STATE = (uint)0x00000041UL;

        /// <summary>The number of segments allocated is fewer than the number of captures requested.</summary>
        public const uint PICO_NOT_ENOUGH_SEGMENTS = (uint)0x00000042UL;

        /// <summary>
        /// A driver function has already been called and not yet finished.
        /// Only one call to the driver can be made at any one time.
        /// </summary>
        public const uint PICO_DRIVER_FUNCTION = (uint)0x00000043UL;

        /// <summary>Not used</summary>
        public const uint PICO_RESERVED = (uint)0x00000044UL;

        /// <summary>An invalid coupling type was specified in -API-SetChannel.</summary>
        public const uint PICO_INVALID_COUPLING = (uint)0x00000045UL;

        /// <summary>An attempt was made to get data before a data buffer was defined.</summary>
        public const uint PICO_BUFFERS_NOT_SET = (uint)0x00000046UL;

        /// <summary>The selected down sampling mode (used for data reduction) is not allowed.</summary>
        public const uint PICO_RATIO_MODE_NOT_SUPPORTED = (uint)0x00000047UL;

        /// <summary>Aggregation was requested in rapid block mode.</summary>
        public const uint PICO_RAPID_NOT_SUPPORT_AGGREGATION = (uint)0x00000048UL;

        /// <summary>An invalid parameter was passed to -API-SetTriggerChannelProperties.</summary>
        public const uint PICO_INVALID_TRIGGER_PROPERTY = (uint)0x00000049UL;

        /// <summary>The driver was unable to contact the oscilloscope.</summary>
        public const uint PICO_INTERFACE_NOT_CONNECTED = (uint)0x0000004AUL;

        /// <summary>Resistance-measuring mode is not allowed in conjunction with the specified probe.</summary>
        public const uint PICO_RESISTANCE_AND_PROBE_NOT_ALLOWED = (uint)0x0000004BUL;

        /// <summary>The device was unexpectedly powered down.</summary>
        public const uint PICO_POWER_FAILED = (uint)0x0000004CUL;

        /// <summary>A problem occurred in -API-SetSigGenBuiltIn or -API-SetSigGenArbitrary.</summary>
        public const uint PICO_SIGGEN_WAVEFORM_SETUP_FAILED = (uint)0x0000004DUL;

        /// <summary>FPGA not successfully set up.</summary>
        public const uint PICO_FPGA_FAIL = (uint)0x0000004EUL;

        /// <summary></summary>
        public const uint PICO_POWER_MANAGER = (uint)0x0000004FUL;

        /// <summary>An impossible analog offset value was specified in -API-SetChannel.</summary>
        public const uint PICO_INVALID_ANALOGUE_OFFSET = (uint)0x00000050UL;

        /// <summary>There is an error within the device hardware.</summary>
        public const uint PICO_PLL_LOCK_FAILED = (uint)0x00000051UL;

        /// <summary>There is an error within the device hardware.</summary>
        public const uint PICO_ANALOG_BOARD = (uint)0x00000052UL;

        /// <summary>Unable to configure the signal generator.</summary>
        public const uint PICO_CONFIG_FAIL_AWG = (uint)0x00000053UL;

        /// <summary>The FPGA cannot be initialized, so unit cannot be opened.</summary>
        public const uint PICO_INITIALISE_FPGA = (uint)0x00000054UL;

        /// <summary>The frequency for the external clock is not within 15% of the nominal value.</summary>
        public const uint PICO_EXTERNAL_FREQUENCY_INVALID = (uint)0x00000056UL;

        /// <summary>The FPGA could not lock the clock signal.</summary>
        public const uint PICO_CLOCK_CHANGE_ERROR = (uint)0x00000057UL;

        /// <summary>You are trying to configure the AUX input as both a trigger and a reference clock.</summary>
        public const uint PICO_TRIGGER_AND_EXTERNAL_CLOCK_CLASH = (uint)0x00000058UL;

        /// <summary>
        /// You are trying to configure the AUX input as both a pulse width qualifier
        /// and a reference clock.
        /// </summary>
        public const uint PICO_PWQ_AND_EXTERNAL_CLOCK_CLASH = (uint)0x00000059UL;

        /// <summary>The requested scaling file cannot be opened.</summary>
        public const uint PICO_UNABLE_TO_OPEN_SCALING_FILE = (uint)0x0000005AUL;

        /// <summary>The frequency of the memory is reporting incorrectly.</summary>
        public const uint PICO_MEMORY_CLOCK_FREQUENCY = (uint)0x0000005BUL;

        /// <summary>The I2C that is being actioned is not responding to requests.</summary>
        public const uint PICO_I2C_NOT_RESPONDING = (uint)0x0000005CUL;

        /// <summary>There are no captures available and therefore no data can be returned.</summary>
        public const uint PICO_NO_CAPTURES_AVAILABLE = (uint)0x0000005DUL;

        /// <summary>
        /// The number of trigger channels is greater than 4,
        /// except for a PS4824 where 8 channels are allowed for rising/falling/rising_or_falling trigger directions.
        /// </summary>
        public const uint PICO_TOO_MANY_TRIGGER_CHANNELS_IN_USE = (uint)0x0000005FUL;

        /// <summary>When more than 4 trigger channels are set on a PS4824 and the direction is out of range.</summary>
        public const uint PICO_INVALID_TRIGGER_DIRECTION = (uint)0x00000060UL;

        /// <summary>
        /// When more than 4 trigger channels are set
        /// and their trigger condition states are not -API-_CONDITION_TRUE.
        /// </summary>
        public const uint PICO_INVALID_TRIGGER_STATES = (uint)0x00000061UL;

        /// <summary>The capture mode the device is currently running in does not support the current request.</summary>
        public const uint PICO_NOT_USED_IN_THIS_CAPTURE_MODE = (uint)0x0000005EUL;

        /// <summary></summary>
        public const uint PICO_GET_DATA_ACTIVE = (uint)0x00000103UL;

        // Codes 104 to 10B are used by the PT104 (USB) when connected via the Network Socket.

        /// <summary>The device is currently connected via the IP Network socket
        /// and thus the call made is not supported.
        /// </summary>
        public const uint PICO_IP_NETWORKED = (uint)0x00000104UL;

        /// <summary>An incorrect IP address has been passed to the driver.</summary>
        public const uint PICO_INVALID_IP_ADDRESS = (uint)0x00000105UL;

        /// <summary>The IP socket has failed.</summary>
        public const uint PICO_IPSOCKET_FAILED = (uint)0x00000106UL;

        /// <summary>The IP socket has timed out.</summary>
        public const uint PICO_IPSOCKET_TIMEDOUT = (uint)0x00000107UL;

        /// <summary>Failed to apply the requested settings.</summary>
        public const uint PICO_SETTINGS_FAILED = (uint)0x00000108UL;

        /// <summary>The network connection has failed.</summary>
        public const uint PICO_NETWORK_FAILED = (uint)0x00000109UL;

        /// <summary>Unable to load the WS2 DLL.</summary>
        public const uint PICO_WS2_32_DLL_NOT_LOADED = (uint)0x0000010AUL;

        /// <summary>The specified IP port is invalid.</summary>
        public const uint PICO_INVALID_IP_PORT = (uint)0x0000010BUL;

        /// <summary>The type of coupling requested is not supported on the opened device.</summary>
        public const uint PICO_COUPLING_NOT_SUPPORTED = (uint)0x0000010CUL;

        /// <summary>Bandwidth limiting is not supported on the opened device.</summary>
        public const uint PICO_BANDWIDTH_NOT_SUPPORTED = (uint)0x0000010DUL;

        /// <summary>The value requested for the bandwidth limit is out of range.</summary>
        public const uint PICO_INVALID_BANDWIDTH = (uint)0x0000010EUL;

        /// <summary>The arbitrary waveform generator is not supported by the opened device.</summary>
        public const uint PICO_AWG_NOT_SUPPORTED = (uint)0x0000010FUL;

        /// <summary>
        /// Data has been requested with ETS mode set but run block has not been called,
        /// or stop has been called.
        /// </summary>
        public const uint PICO_ETS_NOT_RUNNING = (uint)0x00000110UL;

        /// <summary>White noise output is not supported on the opened device.</summary>
        public const uint PICO_SIG_GEN_WHITENOISE_NOT_SUPPORTED = (uint)0x00000111UL;

        /// <summary>The wave type requested is not supported by the opened device.</summary>
        public const uint PICO_SIG_GEN_WAVETYPE_NOT_SUPPORTED = (uint)0x00000112UL;

        /// <summary>The requested digital port number is out of range (MSOs only).</summary>
        public const uint PICO_INVALID_DIGITAL_PORT = (uint)0x00000113UL;

        /// <summary>
        /// The digital channel is not in the range -API-_DIGITAL_CHANNEL0 to -API-_DIGITAL_CHANNEL15,
        /// the digital channels that are supported.
        /// </summary>
        public const uint PICO_INVALID_DIGITAL_CHANNEL = (uint)0x00000114UL;

        /// <summary>
        /// The digital trigger direction is not a valid trigger direction and should be equal
        /// in value to one of the -API-_DIGITAL_DIRECTION enumerations.
        /// </summary>
        public const uint PICO_INVALID_DIGITAL_TRIGGER_DIRECTION = (uint)0x00000115UL;

        /// <summary>Signal generator does not generate pseudo-random binary sequence.</summary>
        public const uint PICO_SIG_GEN_PRBS_NOT_SUPPORTED = (uint)0x00000116UL;

        /// <summary>When a digital port is enabled, ETS sample mode is not available for use.</summary>
        public const uint PICO_ETS_NOT_AVAILABLE_WITH_LOGIC_CHANNELS = (uint)0x00000117UL;

        public const uint PICO_WARNING_REPEAT_VALUE = (uint)0x00000118UL;

        /// <summary>4-channel scopes only: The DC power supply is connected.</summary>
        public const uint PICO_POWER_SUPPLY_CONNECTED = (uint)0x00000119UL;

        /// <summary>4-channel scopes only: The DC power supply is not connected.</summary>
        public const uint PICO_POWER_SUPPLY_NOT_CONNECTED = (uint)0x0000011AUL;

        /// <summary>Incorrect power mode passed for current power source.</summary>
        public const uint PICO_POWER_SUPPLY_REQUEST_INVALID = (uint)0x0000011BUL;

        /// <summary>The supply voltage from the USB source is too low.</summary>
        public const uint PICO_POWER_SUPPLY_UNDERVOLTAGE = (uint)0x0000011CUL;

        /// <summary>The oscilloscope is in the process of capturing data.</summary>
        public const uint PICO_CAPTURING_DATA = (uint)0x0000011DUL;

        /// <summary>A USB 3.0 device is connected to a non-USB 3.0 port.</summary>
        public const uint PICO_USB3_0_DEVICE_NON_USB3_0_PORT = (uint)0x0000011EUL;

        /// <summary>A function has been called that is not supported by the current device.</summary>
        public const uint PICO_NOT_SUPPORTED_BY_THIS_DEVICE = (uint)0x0000011FUL;

        /// <summary>The device resolution is invalid (out of range).</summary>
        public const uint PICO_INVALID_DEVICE_RESOLUTION = (uint)0x00000120UL;

        /// <summary>
        /// The number of channels that can be enabled is limited in 15 and 16-bit modes.
        /// (Flexible Resolution Oscilloscopes only)
        /// </summary>
        public const uint PICO_INVALID_NUMBER_CHANNELS_FOR_RESOLUTION = (uint)0x00000121UL;

        /// <summary>USB power not sufficient for all requested channels.</summary>
        public const uint PICO_CHANNEL_DISABLED_DUE_TO_USB_POWERED = (uint)0x00000122UL;

        /// <summary>The signal generator does not have a configurable DC offset.</summary>
        public const uint PICO_SIGGEN_DC_VOLTAGE_NOT_CONFIGURABLE = (uint)0x00000123UL;

        /// <summary>An attempt has been made to define pre-trigger delay without first enabling a trigger.</summary>
        public const uint PICO_NO_TRIGGER_ENABLED_FOR_TRIGGER_IN_PRE_TRIG = (uint)0x00000124UL;

        /// <summary>An attempt has been made to define pre-trigger delay without first arming a trigger.</summary>
        public const uint PICO_TRIGGER_WITHIN_PRE_TRIG_NOT_ARMED = (uint)0x00000125UL;

        /// <summary>Pre-trigger delay and post-trigger delay cannot be used at the same time.</summary>
        public const uint PICO_TRIGGER_WITHIN_PRE_NOT_ALLOWED_WITH_DELAY = (uint)0x00000126UL;

        /// <summary>The array index points to a nonexistent trigger.</summary>
        public const uint PICO_TRIGGER_INDEX_UNAVAILABLE = (uint)0x00000127UL;

        /// <summary></summary>
        public const uint PICO_AWG_CLOCK_FREQUENCY = (uint)0x00000128UL;

        /// <summary>There are more 4 analog channels with a trigger condition set.</summary>
        public const uint PICO_TOO_MANY_CHANNELS_IN_USE = (uint)0x00000129UL;

        /// <summary>The condition parameter is a null pointer.</summary>
        public const uint PICO_NULL_CONDITIONS = (uint)0x0000012AUL;

        /// <summary>There is more than one condition pertaining to the same channel.</summary>
        public const uint PICO_DUPLICATE_CONDITION_SOURCE = (uint)0x0000012BUL;

        /// <summary>The parameter relating to condition information is out of range.</summary>
        public const uint PICO_INVALID_CONDITION_INFO = (uint)0x0000012CUL;

        /// <summary>Reading the metadata has failed.</summary>
        public const uint PICO_SETTINGS_READ_FAILED = (uint)0x0000012DUL;

        /// <summary>Writing the metadata has failed.</summary>
        public const uint PICO_SETTINGS_WRITE_FAILED = (uint)0x0000012EUL;

        /// <summary>A parameter has a value out of the expected range.</summary>
        public const uint PICO_ARGUMENT_OUT_OF_RANGE = (uint)0x0000012FUL;

        /// <summary>The driver does not support the hardware variant connected.</summary>
        public const uint PICO_HARDWARE_VERSION_NOT_SUPPORTED = (uint)0x00000130UL;

        /// <summary>The driver does not support the digital hardware variant connected.</summary>
        public const uint PICO_DIGITAL_HARDWARE_VERSION_NOT_SUPPORTED = (uint)0x00000131UL;

        /// <summary>The driver does not support the analog hardware variant connected.</summary>
        public const uint PICO_ANALOGUE_HARDWARE_VERSION_NOT_SUPPORTED = (uint)0x00000132UL;

        /// <summary>Converting a channel's ADC value to resistance has failed.</summary>
        public const uint PICO_UNABLE_TO_CONVERT_TO_RESISTANCE = (uint)0x00000133UL;

        /// <summary>The channel is listed more than once in the function call.</summary>
        public const uint PICO_DUPLICATED_CHANNEL = (uint)0x00000134UL;

        /// <summary>The range cannot have resistance conversion applied.</summary>
        public const uint PICO_INVALID_RESISTANCE_CONVERSION = (uint)0x00000135UL;

        /// <summary>An invalid value is in the max buffer.</summary>
        public const uint PICO_INVALID_VALUE_IN_MAX_BUFFER = (uint)0x00000136UL;

        /// <summary>An invalid value is in the min buffer.</summary>
        public const uint PICO_INVALID_VALUE_IN_MIN_BUFFER = (uint)0x00000137UL;

        /// <summary>
        /// When calculating the frequency for phase conversion,
        /// the frequency is greater than that supported by the current variant.
        /// </summary>
        public const uint PICO_SIGGEN_FREQUENCY_OUT_OF_RANGE = (uint)0x00000138UL;

        /// <summary>
        /// The device's EEPROM is corrupt.
        /// Contact Pico Technology support: https://www.picotech.com/tech-support.
        /// </summary>
        public const uint PICO_EEPROM2_CORRUPT = (uint)0x00000139UL;

        /// <summary>The EEPROM has failed.</summary>
        public const uint PICO_EEPROM2_FAIL = (uint)0x0000013AUL;

        /// <summary>The serial buffer is too small for the required information.</summary>
        public const uint PICO_SERIAL_BUFFER_TOO_SMALL = (uint)0x0000013BUL;

        /// <summary>
        /// The signal generator trigger and the external clock have both been set.
        /// This is not allowed.
        /// </summary>
        public const uint PICO_SIGGEN_TRIGGER_AND_EXTERNAL_CLOCK_CLASH = (uint)0x0000013CUL;

        /// <summary>
        /// The AUX trigger was enabled and the external clock has been enabled,
        /// so the AUX has been automatically disabled.
        /// </summary>
        public const uint PICO_WARNING_SIGGEN_AUXIO_TRIGGER_DISABLED = (uint)0x0000013DUL;

        /// <summary>
        /// The AUX I/O was set as a scope trigger and is now being set as a signal generator
        /// gating trigger. This is not allowed.
        /// </summary>
        public const uint PICO_SIGGEN_GATING_AUXIO_NOT_AVAILABLE = (uint)0x00000013EUL;

        /// <summary>
        /// The AUX I/O was set by the signal generator as a gating trigger and is now being set
        /// as a scope trigger. This is not allowed.
        /// </summary>
        public const uint PICO_SIGGEN_GATING_AUXIO_ENABLED = (uint)0x00000013FUL;

        /// <summary>A resource has failed to initialize</summary>
        public const uint PICO_RESOURCE_ERROR = (uint)0x00000140UL;

        /// <summary>The temperature type is out of range</summary>
        public const uint PICO_TEMPERATURE_TYPE_INVALID = (uint)0x000000141UL;

        /// <summary>A requested temperature type is not supported on this device</summary>
        public const uint PICO_TEMPERATURE_TYPE_NOT_SUPPORTED = (uint)0x000000142UL;

        /// <summary>A read/write to the device has timed out</summary>
        public const uint PICO_TIMEOUT = (uint)0x00000143UL;

        /// <summary>The device cannot be connected correctly</summary>
        public const uint PICO_DEVICE_NOT_FUNCTIONING = (uint)0x00000144UL;

        /// <summary>The driver has experienced an unknown error and is unable to recover from this error</summary>
        public const uint PICO_INTERNAL_ERROR = (uint)0x00000145UL;

        /// <summary>Used when opening units via IP and more than multiple units have the same ip address</summary>
        public const uint PICO_MULTIPLE_DEVICES_FOUND = (uint)0x00000146UL;

        /// <summary></summary>
        public const uint PICO_WARNING_NUMBER_OF_SEGMENTS_REDUCED = (uint)0x00000147UL;

        /// <summary>The calibration pin states argument is out of range</summary>
        public const uint PICO_CAL_PINS_STATES = (uint)0x00000148UL;

        /// <summary>The calibration pin frequency argument is out of range</summary>
        public const uint PICO_CAL_PINS_FREQUENCY = (uint)0x00000149UL;

        /// <summary>The calibration pin amplitude argument is out of range</summary>
        public const uint PICO_CAL_PINS_AMPLITUDE = (uint)0x0000014AUL;

        /// <summary>The calibration pin wavetype argument is out of range</summary>
        public const uint PICO_CAL_PINS_WAVETYPE = (uint)0x0000014BUL;

        /// <summary>The calibration pin offset argument is out of range</summary>
        public const uint PICO_CAL_PINS_OFFSET = (uint)0x0000014CUL;

        /// <summary>The probe's identity has a problem</summary>
        public const uint PICO_PROBE_FAULT = (uint)0x0000014DUL;

        /// <summary>The probe has not been identified</summary>
        public const uint PICO_PROBE_IDENTITY_UNKNOWN = (uint)0x0000014EUL;

        /// <summary>Enabling the probe would cause the device to exceed the allowable current limit</summary>
        public const uint PICO_PROBE_POWER_DC_POWER_SUPPLY_REQUIRED = (uint)0x0000014FUL;

        /// <summary>
        /// The DC power supply is connected; enabling the probe would cause the device to exceed the
        /// allowable current limit.
        /// </summary>
        public const uint PICO_PROBE_NOT_POWERED_WITH_DC_POWER_SUPPLY = (uint)0x00000150UL;

        /// <summary>Failed to complete probe configuration</summary>
        public const uint PICO_PROBE_CONFIG_FAILURE = (uint)0x00000151UL;

        /// <summary>Failed to set the callback function, as currently in current callback function</summary>
        public const uint PICO_PROBE_INTERACTION_CALLBACK = (uint)0x00000152UL;

        /// <summary>The probe has been verified but not know on this driver</summary>
        public const uint PICO_UNKNOWN_INTELLIGENT_PROBE = (uint)0x00000153UL;

        /// <summary>The intelligent probe cannot be verified</summary>
        public const uint PICO_INTELLIGENT_PROBE_CORRUPT = (uint)0x00000154UL;

        /// <summary>
        /// The callback is null, probe collection will only start when
        /// first callback is a none null pointer
        /// </summary>
        public const uint PICO_PROBE_COLLECTION_NOT_STARTED = (uint)0x00000155UL;

        /// <summary>The current drawn by the probe(s) has exceeded the allowed limit</summary>
        public const uint PICO_PROBE_POWER_CONSUMPTION_EXCEEDED = (uint)0x00000156UL;

        /// <summary>
        /// The channel range limits have changed due to connecting or disconnecting a probe
        /// the channel has been enabled
        /// </summary>
        public const uint PICO_WARNING_PROBE_CHANNEL_OUT_OF_SYNC = (uint)0x00000157UL;

        /// <summary>The time stamp per waveform segment has been reset.</summary>
        public const uint PICO_DEVICE_TIME_STAMP_RESET = (uint)0x01000000UL;

        /// <summary>An internal error has occurred and a watchdog timer has been called.</summary>
        public const uint PICO_WATCHDOGTIMER = (uint)0x10000000UL;

        /// <summary>The picoipp.dll has not been found.</summary>
        public const uint PICO_IPP_NOT_FOUND = (uint)0x10000001UL;

        /// <summary>A function in the picoipp.dll does not exist.</summary>
        public const uint PICO_IPP_NO_FUNCTION = (uint)0x10000002UL;

        /// <summary>The Pico IPP call has failed.</summary>
        public const uint PICO_IPP_ERROR = (uint)0x10000003UL;

        /// <summary>Shadow calibration is not available on this device.</summary>
        public const uint PICO_SHADOW_CAL_NOT_AVAILABLE = (uint)0x10000004UL;

        /// <summary>Shadow calibration is currently disabled.</summary>
        public const uint PICO_SHADOW_CAL_DISABLED = (uint)0x10000005UL;

        /// <summary>Shadow calibration error has occurred.</summary>
        public const uint PICO_SHADOW_CAL_ERROR = (uint)0x10000006UL;

        /// <summary>The shadow calibration is corrupt.</summary>
        public const uint PICO_SHADOW_CAL_CORRUPT = (uint)0x10000007UL;

        /// <summary>The memory onboard the device has overflowed</summary>
        public const uint PICO_DEVICE_MEMORY_OVERFLOW = (uint)0x10000008UL;

        /// <summary>Reserved</summary>
        public const uint PICO_RESERVED_1 = (uint)0x11000000UL;
    }
}

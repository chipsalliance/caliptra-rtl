/******************************************************************************
*
* Filename: PS3000AImports.cs
*  
* Description:
*  This file contains .NET wrapper calls corresponding to function calls 
*  defined in the ps3000aApi.h C header file. 
*  It also has the enums and structs required by the (wrapped) function calls.
*   
* Copyright © 2011-2018 Pico Technology Ltd. See LICENSE file for terms.
*
******************************************************************************/

using System;
using System.Runtime.InteropServices;
using System.Text;

namespace SAKURA
{
	class Imports3
	{
		#region Constants
		private const string _DRIVER_FILENAME = "ps3000a.dll";

		public const int MaxValue = 32512;
        public const int MaxLogicLevel = 32767;

        #endregion

        #region Driver Enums

        public enum Channel : int
		{
			ChannelA,
			ChannelB,
			ChannelC,
			ChannelD,
			External,
			Aux,
			None,
            PS3000A_DIGITAL_PORT0 = 0x80,    // digital channel 0 - 7
            PS3000A_DIGITAL_PORT1,			 // digital channel 8 - 15
            PS3000A_DIGITAL_PORT2,			 // digital channel 16 - 23
            PS3000A_DIGITAL_PORT3			 // digital channel 24 - 31
		}

		public enum Range : int
		{
			Range_10MV,
			Range_20MV,
			Range_50MV,
			Range_100MV,
			Range_200MV,
			Range_500MV,
			Range_1V,
			Range_2V,
			Range_5V,
			Range_10V,
			Range_20V,
			Range_50V,
            Range_MAX_RANGE
		}

		public enum ReportedTimeUnits : int
		{
			FemtoSeconds,
			PicoSeconds,
			NanoSeconds,
			MicroSeconds,
			MilliSeconds,
			Seconds,
		}

		public enum ThresholdMode : int
		{
			Level,
			Window
		}

		public enum ThresholdDirection : int
		{
			// Values for level threshold mode
			//
			Above,              // Using upper threshold
            Below,              // Using upper threshold
            Rising,             // Using upper threshold
            Falling,            // Using upper threshold
            RisingOrFalling,    // Using both thresholds
            AboveLower,         // Using lower threshold
            BelowLower,         // Using lower threshold
            RisingLower,        // Using lower threshold
            FallingLower,       // Using lower threshold

            // Values for window threshold mode
            //
            Inside = Above,
			Outside = Below,
			Enter = Rising,
			Exit = Falling,
			EnterOrExit = RisingOrFalling,
			PositiveRunt = 9,
			NegativeRunt,

			None = Rising,
		}

		public enum PulseWidthType : int
		{
			None,
			LessThan,
			GreaterThan,
			InRange,
			OutOfRange
		}

		public enum TriggerState : int
		{
			DontCare,
			True,
			False,
		}

        // Ratio Mode has Flags attribute set to enable bit-wise OR combinations
        [Flags]
        public enum RatioMode : int
        {
            None,
            Aggregate = 1,
            Decimate = 2,
            Average = 4
        }

        public enum DigitalDirection : int
        {
            PS3000A_DIGITAL_DONT_CARE,
            PS3000A_DIGITAL_DIRECTION_LOW,
            PS3000A_DIGITAL_DIRECTION_HIGH,
            PS3000A_DIGITAL_DIRECTION_RISING,
            PS3000A_DIGITAL_DIRECTION_FALLING,
            PS3000A_DIGITAL_DIRECTION_RISING_OR_FALLING,
            PS3000A_DIGITAL_MAX_DIRECTION
        }

        public enum Mode : int
        {
            ANALOGUE,
            DIGITAL,
            AGGREGATED,
            MIXED
        }

        public enum DigitalChannel : int
        {
            PS3000A_DIGITAL_CHANNEL_0,
            PS3000A_DIGITAL_CHANNEL_1,
            PS3000A_DIGITAL_CHANNEL_2,
            PS3000A_DIGITAL_CHANNEL_3,
            PS3000A_DIGITAL_CHANNEL_4,
            PS3000A_DIGITAL_CHANNEL_5,
            PS3000A_DIGITAL_CHANNEL_6,
            PS3000A_DIGITAL_CHANNEL_7,
            PS3000A_DIGITAL_CHANNEL_8,
            PS3000A_DIGITAL_CHANNEL_9,
            PS3000A_DIGITAL_CHANNEL_10,
            PS3000A_DIGITAL_CHANNEL_11,
            PS3000A_DIGITAL_CHANNEL_12,
            PS3000A_DIGITAL_CHANNEL_13,
            PS3000A_DIGITAL_CHANNEL_14,
            PS3000A_DIGITAL_CHANNEL_15,
            PS3000A_DIGITAL_CHANNEL_16,
            PS3000A_DIGITAL_CHANNEL_17,
            PS3000A_DIGITAL_CHANNEL_18,
            PS3000A_DIGITAL_CHANNEL_19,
            PS3000A_DIGITAL_CHANNEL_20,
            PS3000A_DIGITAL_CHANNEL_21,
            PS3000A_DIGITAL_CHANNEL_22,
            PS3000A_DIGITAL_CHANNEL_23,
            PS3000A_DIGITAL_CHANNEL_24,
            PS3000A_DIGITAL_CHANNEL_25,
            PS3000A_DIGITAL_CHANNEL_26,
            PS3000A_DIGITAL_CHANNEL_27,
            PS3000A_DIGITAL_CHANNEL_28,
            PS3000A_DIGITAL_CHANNEL_29,
            PS3000A_DIGITAL_CHANNEL_30,
            PS3000A_DIGITAL_CHANNEL_31
        }

        public enum SweepType : int
        {
            PS3000A_UP,
            PS3000A_DOWN,
            PS3000A_UPDOWN,
            PS3000A_DOWNUP,
            PS3000A_MAX_SWEEP_TYPES
        }

        public enum WaveType : int
        {
            PS3000A_SINE,
            PS3000A_SQUARE,
            PS3000A_TRIANGLE,
            PS3000A_RAMP_UP,
            PS3000A_RAMP_DOWN,
            PS3000A_SINC,
            PS3000A_GAUSSIAN,
            PS3000A_HALF_SINE,
            PS3000A_DC_VOLTAGE,
            PS3000A_MAX_WAVE_TYPES
        }

        public enum ExtraOperations : int
        {
            PS3000A_ES_OFF,
            PS3000A_WHITENOISE,
            PS3000A_PRBS // Pseudo-Random Bit Stream
        }

        public enum SigGenTrigType : int
        {
            PS3000A_SIGGEN_RISING,
            PS3000A_SIGGEN_FALLING,
            PS3000A_SIGGEN_GATE_HIGH,
            PS3000A_SIGGEN_GATE_LOW
        }

        public enum SigGenTrigSource : int
        {
            PS3000A_SIGGEN_NONE,
            PS3000A_SIGGEN_SCOPE_TRIG,
            PS3000A_SIGGEN_AUX_IN,
            PS3000A_SIGGEN_EXT_IN,
            PS3000A_SIGGEN_SOFT_TRIG
        }

        public enum IndexMode : int
        {
            PS3000A_SINGLE,
            PS3000A_DUAL,
            PS3000A_QUAD,
            PS3000A_MAX_INDEX_MODES
        }

        public enum Coupling : int
        {
            AC,
            DC
        }

        #endregion

        # region Driver Structs

        [StructLayout(LayoutKind.Sequential, Pack = 1)]
		public struct TriggerChannelProperties
		{
			public short ThresholdMajor;
			public ushort HysteresisMajor;
			public short ThresholdMinor;
			public ushort HysteresisMinor;
			public Channel Channel;
			public ThresholdMode ThresholdMode;


			public TriggerChannelProperties(
				short thresholdMajor,
				ushort hysteresisMajor,
				short thresholdMinor,
				ushort hysteresisMinor,
				Channel channel,
				ThresholdMode thresholdMode)
			{
				this.ThresholdMajor = thresholdMajor;
				this.HysteresisMajor = hysteresisMajor;
				this.ThresholdMinor = thresholdMinor;
				this.HysteresisMinor = hysteresisMinor;
				this.Channel = channel;
				this.ThresholdMode = thresholdMode;
			}
		}

		[StructLayout(LayoutKind.Sequential, Pack = 1)]
		public struct TriggerConditions
		{
			public TriggerState ChannelA;
			public TriggerState ChannelB;
			public TriggerState ChannelC;
			public TriggerState ChannelD;
			public TriggerState External;
			public TriggerState Aux;
			public TriggerState Pwq;

			public TriggerConditions(
				TriggerState channelA,
				TriggerState channelB,
				TriggerState channelC,
				TriggerState channelD,
				TriggerState external,
				TriggerState aux,
				TriggerState pwq)
			{
				this.ChannelA = channelA;
				this.ChannelB = channelB;
				this.ChannelC = channelC;
				this.ChannelD = channelD;
				this.External = external;
				this.Aux = aux;
				this.Pwq = pwq;
			}
		}

        [StructLayout(LayoutKind.Sequential, Pack = 1)]
        public struct TriggerConditionsV2
        {
            public TriggerState ChannelA;
            public TriggerState ChannelB;
            public TriggerState ChannelC;
            public TriggerState ChannelD;
            public TriggerState External;
            public TriggerState Aux;
            public TriggerState Pwq;
             public TriggerState Digital;

            public TriggerConditionsV2(
                TriggerState channelA,
                TriggerState channelB,
                TriggerState channelC,
                TriggerState channelD,
                TriggerState external,
                TriggerState aux,
                TriggerState pwq,
                TriggerState digital)
            {
                this.ChannelA = channelA;
                this.ChannelB = channelB;
                this.ChannelC = channelC;
                this.ChannelD = channelD;
                this.External = external;
                this.Aux = aux;
                this.Pwq = pwq;
                this.Digital = digital;
            }
        }

		[StructLayout(LayoutKind.Sequential, Pack = 1)]
		public struct PwqConditions
		{
			public TriggerState ChannelA;
			public TriggerState ChannelB;
			public TriggerState ChannelC;
			public TriggerState ChannelD;
			public TriggerState External;
			public TriggerState Aux;

			public PwqConditions(
				TriggerState channelA,
				TriggerState channelB,
				TriggerState channelC,
				TriggerState channelD,
				TriggerState external,
				TriggerState aux)
			{
				this.ChannelA = channelA;
				this.ChannelB = channelB;
				this.ChannelC = channelC;
				this.ChannelD = channelD;
				this.External = external;
				this.Aux = aux;
			}
		}

        [StructLayout(LayoutKind.Sequential, Pack = 1)]
        public struct DigitalChannelDirections
        {
            public DigitalChannel DigiPort;
            public DigitalDirection DigiDirection;

            public DigitalChannelDirections(
                DigitalChannel digiPort,
                DigitalDirection digiDirection)
            {
                this.DigiPort = digiPort;
                this.DigiDirection = digiDirection;
            }
        }

        [StructLayout(LayoutKind.Sequential, Pack = 1)]
        public struct TriggerInfo
        {
            public uint status;
            public uint segmentIndex;
            public uint reserved0;
            public Int64 triggerTime;
            public short timeUnits;
            public short reserved1;
            public UInt64 timeStampCounter;

            public TriggerInfo(
                uint status,
                uint segmentIndex,
                uint reserved0,
                Int64 triggerTime,
                short timeUnits,
                short reserved1,
                UInt64 timeStampCounter)
            {
                this.status = status;
                this.segmentIndex = segmentIndex;
                this.reserved0 = reserved0;
                this.triggerTime = triggerTime;
                this.timeUnits = timeUnits;
                this.reserved1 = reserved1;
                this.timeStampCounter = timeStampCounter;
            }
        }

        #endregion
        
        #region Driver Imports
        #region Callback delegates
        public delegate void ps3000aBlockReady(short handle, short status, IntPtr pVoid);
     
        public delegate void ps3000aStreamingReady(
												short handle,
												int noOfSamples,
												uint startIndex,
												short overflow,
												uint triggerAt,
												short triggered,
												short autoStop,
												IntPtr pVoid);

		public delegate void ps3000DataReady(
												short handle,
                                                short status,
												int noOfSamples,
												short overflow,
												IntPtr pVoid);
		#endregion

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aOpenUnit")]
		public static extern uint OpenUnit(out short handle, StringBuilder serial);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aCloseUnit")]
        public static extern uint CloseUnit(short handle);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aRunBlock")]
        public static extern uint RunBlock(
												short handle,
												int noOfPreTriggerSamples,
												int noOfPostTriggerSamples,
												uint timebase,
												short oversample,
												out int timeIndisposedMs,
												uint segmentIndex,
												ps3000aBlockReady lpps3000aBlockReady,
												IntPtr pVoid);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aIsReady")]
        public static extern short IsReady(short handle, out short ready);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aRunBlock2")]
        public static extern short RunBlock2(
                                                short handle,
                                                int no_of_samples,
                                                short timebase,
                                                short oversample,
                                                out int timeIndisposedMs);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aStop")]
        public static extern uint Stop(short handle);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetChannel")]
        public static extern uint SetChannel(
												short handle,
												Channel channel,
												short enabled,
												Coupling dc,
												Range range,
                                                float analogueOffset);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetDataBuffer")]
        public static extern uint SetDataBuffer(
												    short handle,
												    Channel channel,
												    short[] buffer,
												    int bufferLth,
                                                    uint segmentIndex,
                                                    RatioMode  ratioMode);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetDataBuffers")]
        public static extern uint SetDataBuffers(
                                                    short handle,
                                                    Channel channel,
                                                    short[] bufferMax,
                                                    short[] bufferMin,
                                                    int bufferLth,
                                                    uint segmentIndex,
                                                    RatioMode ratioMode);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetTimebase")]
        public static extern uint GetTimebase(
											     short handle,
											     uint timebase,
											     int noSamples,
											     out int timeIntervalNanoseconds,
											     short oversample,
											     out int maxSamples,
											     uint segmentIndex);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetTimebase2")]
        public static extern uint GetTimebase2(
                                                 short handle,
                                                 uint timebase,
                                                 int noSamples,
                                                 out float timeIntervalNanoseconds,
                                                 short oversample,
                                                 out int maxSamples,
                                                 uint segmentIndex);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetValues")]
        public static extern uint GetValues(
				                                short handle,
				                                uint startIndex,
				                                ref uint noOfSamples,
				                                uint downSampleRatio,
				                                RatioMode downSampleRatioMode,
				                                uint segmentIndex,
				                                out short overflow);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetSimpleTrigger")]
        public static extern uint SetSimpleTrigger(
            short handle,
            short enabled,
            Channel source,
            short threshold,
            ThresholdDirection direction,
            uint delay,
            short autoTriggerMs);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetPulseWidthQualifier")]
        public static extern uint SetPulseWidthQualifier(
			short handle,
			PwqConditions[] conditions,
			short nConditions,
			ThresholdDirection direction,
			uint lower,
			uint upper,
			PulseWidthType type);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetTriggerChannelProperties")]
        public static extern uint SetTriggerChannelProperties(
			short handle,
			TriggerChannelProperties[] channelProperties,
			short nChannelProperties,
			short auxOutputEnable,
			int autoTriggerMilliseconds);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetTriggerChannelConditions")]
        public static extern uint SetTriggerChannelConditions(
			short handle,
			TriggerConditions[] conditions,
			short nConditions);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetTriggerChannelConditionsV2")]
        public static extern uint SetTriggerChannelConditionsV2(
            short handle,
            TriggerConditionsV2[] conditions,
            short nConditions);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetTriggerChannelDirections")]
        public static extern uint SetTriggerChannelDirections(
                                                                short handle,
                                                                ThresholdDirection channelA,
                                                                ThresholdDirection channelB,
                                                                ThresholdDirection channelC,
                                                                ThresholdDirection channelD,
                                                                ThresholdDirection ext,
                                                                ThresholdDirection aux);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetTriggerDelay")]
        public static extern uint SetTriggerDelay(short handle, uint delay);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetUnitInfo")]
        public static extern uint GetUnitInfo(
            short handle, 
            StringBuilder infoString, 
            short stringLength, 
            out short requiredSize, 
            int info);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aRunStreaming")]
        public static extern uint RunStreaming(
			short handle,
			ref uint sampleInterval,
			ReportedTimeUnits sampleIntervalTimeUnits,
			uint maxPreTriggerSamples,
			uint maxPostPreTriggerSamples,
			bool autoStop,
			uint downSamplingRatio,
            RatioMode downSampleRatioMode,
			uint overviewBufferSize);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetStreamingLatestValues")]
        public static extern uint GetStreamingLatestValues(
		    short handle,
		    ps3000aStreamingReady lpps3000aStreamingReady,
		    IntPtr pVoid);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetNoOfCaptures")]
        public static extern uint SetNoOfRapidCaptures(
		    short handle,
		    uint nCaptures);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetNoOfCaptures")]
        public static extern uint GetNoOfRapidCaptures(
            short handle,
            out uint nCaptures);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aMemorySegments")]
        public static extern uint MemorySegments(
			short handle,
			uint nSegments,
			out int nMaxSamples);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetMaxSegments")]
        public static extern uint GetMaxSegments(
            short handle,
            out uint maxSegments);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetValuesBulk")]
        public static extern uint GetValuesRapid(
			short handle,
			ref uint noOfSamples,
			uint fromSegmentIndex,
			uint toSegmentIndex,
            uint downSampleRatio,
            RatioMode downSampleRatioMode,
			short[] overflow);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aGetTriggerInfoBulk")]
        public static extern uint GetTriggerInfoBulk(
            short handle,
            [Out] TriggerInfo[] triggerInfo,
            uint fromSegmentIndex,
            uint toSegmentIndex);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aChangePowerSource")]
        public static extern uint ChangePowerSource(
            short handle,
            uint status);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetDigitalPort")]
        public static extern uint SetDigitalPort(
            short handle,
            Channel digiPort,
            short enabled,
            short logicLevel);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetTriggerDigitalPortProperties")]
        public static extern uint SetTriggerDigitalPort(
            short handle,
            DigitalChannelDirections[] DigiChannelDirections,
            short nDigiChannelDirections);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aMaxDownSampleRatio")]
        public static extern uint MaxDownSampleRatio(
            short handle,
            uint numUnaggregatedSamples,
            out uint maxDownSampleRatio,
            RatioMode downSampleRatioMode,
            uint segmentIndex);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aEnumerateUnits")]
        public static extern uint EnumerateUnits(
                                                    out short count,
                                                    StringBuilder serials,
                                                    ref short serialLength
                                                  );

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetSigGenArbitrary")]
        public static extern uint SetSigGenArbitrary(
                                                        short handle,
                                                        int offsetVoltage,
                                                        uint pkTopk,
                                                        uint startDeltaPhase,
                                                        uint stopDeltaPhase,
                                                        uint deltaPhaseIncrement,
                                                        uint dwellCount,
                                                        short [] arbitaryWaveform,
                                                        int arbitaryWaveformSize,
                                                        SweepType sweepType,
                                                        ExtraOperations operation,
                                                        IndexMode indexMode,
                                                        uint shots,
                                                        uint sweeps,
                                                        SigGenTrigType triggerType,
                                                        SigGenTrigSource triggerSource,
                                                        short extInThreshold);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetSigGenPropertiesArbitrary")]
        public static extern uint SetSigGenPropertiesArbitrary(
                                                        short handle,
                                                        uint startDeltaPhase,
                                                        uint stopDeltaPhase,
                                                        uint deltaPhaseIncrement,
                                                        uint dwellCount,
                                                        SweepType sweepType,
                                                        uint shots,
                                                        uint sweeps,
                                                        SigGenTrigType triggerType,
                                                        SigGenTrigSource triggerSource,
                                                        short extInThreshold);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetSigGenPropertiesBuiltIn")]
        public static extern uint SetSigGenPropertiesBuiltIn(
                                                        short handle,
                                                        double startFrequency,
                                                        double stopFrequency,
                                                        double increment,
                                                        double dwellTime,
                                                        SweepType sweepType,
                                                        uint shots,
                                                        uint sweeps,
                                                        SigGenTrigType triggerType,
                                                        SigGenTrigSource triggerSource,
                                                        short extInThreshold);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSetSigGenBuiltInV2")]
        public static extern uint SetSigGenBuiltInV2(
                                                        short handle,
                                                        int offsetVoltage,
                                                        uint pkTopk,
                                                        WaveType waveType,
                                                        double startFrequency,
                                                        double stopFrequency,
                                                        double increment,
                                                        double dwellTime,
                                                        SweepType sweepType,
                                                        ExtraOperations operation,
                                                        uint shots,
                                                        uint sweeps,
                                                        SigGenTrigType triggerType,
                                                        SigGenTrigSource triggerSource,
                                                        short extInThreshold);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSigGenFrequencyToPhase")]
        public static extern uint SigGenFrequencyToPhase(
                                                                short handle,
                                                                double frequency,
                                                                IndexMode indexMode,
                                                                uint bufferLength,
                                                                out uint phase);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aSigGenArbitraryMinMaxValues")]
        public static extern uint SigGenArbitraryMinMaxValues(
                                                                short handle,
                                                                out short minArbitraryWaveformValue,
                                                                out short maxArbitraryWaveformValue,
                                                                out uint minArbitraryWaveformSize,
                                                                out uint maxArbitraryWaveformSize);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps3000aNoOfStreamingValues")]
        public static extern uint NoOfStreamingValues(
                                                        short handle,
                                                        out uint noOfValues);

        #endregion
    }
}

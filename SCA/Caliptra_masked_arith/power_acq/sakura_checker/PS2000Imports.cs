/**************************************************************************
 *
 *     ooooooooo.    o8o                       
 *     `888   `Y88.  `''                       
 *      888   .d88' oooo   .ooooo.   .ooooo.   
 *      888ooo88P'  `888  d88' `'Y8 d88' `88b  
 *      888          888  888       888   888  
 *      888          888  888   .o8 888   888  
 *     o888o        o888o `Y8bod8P' `Y8bod8P'  
 *
 *
 *    Copyright Pico Technology Ltd 1995-2015
 *
 * 
 *    For sales and general information visit
 *    https://www.picotech.com   https://www.picoauto.com
 *    
 *    For help and support visit
 *    https://www.picotech.com/tech-support
 * 
 *    If you have what it takes to join us visit
 *    http://pico.jobs/
 *
 * 
 * Description:
 *   This file contains all the .NET wrapper calls needed to support
 *   the console example. It also has the enums and structs required
 *   by the (wrapped) function calls.
 *
 **************************************************************************/

using System;
using System.Runtime.InteropServices;
using System.Text;

namespace SAKURA
{
	class Imports
	{
		#region constants
		private const string _DRIVER_FILENAME = "ps2000.dll";

        public const int MaxValue = 32767;
		#endregion

		#region Driver enums

        public enum WaveType : int
        {
            SINE,
            SQUARE,
            TRIANGLE,
            RAMP_UP,
            RAMP_DOWN,
            SINC,
            GAUSSIAN,
            HALF_SINE,
            DC_VOLTAGE,
            MAX_WAVE_TYPES
        }

        public enum ExtraOperations : int
        {
            ES_OFF,
            WHITENOISE,
            PRBS // Pseudo-Random Bit Stream 
        }

        public enum SweepType : int
        {
            UP,
            DOWN,
            UPDOWN,
            DOWNUP,
            MAX_SWEEP_TYPES
        } 

        public enum SigGenTrigType
        {
	        SIGGEN_RISING,
	        SIGGEN_FALLING,
	        SIGGEN_GATE_HIGH,
	        SIGGEN_GATE_LOW
        } 

        public enum SigGenTrigSource
        {
	        SIGGEN_NONE,
	        SIGGEN_SCOPE_TRIG,
	        SIGGEN_AUX_IN,
	        SIGGEN_EXT_IN,
	        SIGGEN_SOFT_TRIG
        }

		public enum Channel : short
		{
			ChannelA,
			ChannelB,
			ChannelC,
			ChannelD,
			External,
			Aux,
			None
		}

		public enum Range : short
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

        public enum PulseWidthType : int
        {
            None,
            LessThan,
            GreaterThan,
            InRange,
            OutOfRange
        }

		public enum ThresholdDirection : int
		{
			// Values for level threshold mode
			//
			Above,
			Below,
			Rising,
			Falling,
			RisingOrFalling,

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

		public enum DownSamplingMode : int
		{
			None,
			Aggregate
		}

		public enum TriggerState : int
		{
			DontCare,
			True,
			False,
		}

        public enum RatioMode : int
        {
            None,
            Aggregate,
            Average,
            Decimate
        }


#endregion

		[StructLayout(LayoutKind.Sequential, Pack = 1)]
		public struct TriggerChannelProperties
		{
			public short ThresholdMajor;
            public short ThresholdMinor;
			public ushort Hysteresis;
			public Channel Channel;
			public ThresholdMode ThresholdMode;


			public TriggerChannelProperties(
				short thresholdMajor,
                short thresholdMinor,
				ushort hysteresis,
				Channel channel,
				ThresholdMode thresholdMode)
			{
				this.ThresholdMajor = thresholdMajor;
                this.ThresholdMinor = thresholdMinor;
				this.Hysteresis = hysteresis;
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
            public TriggerState Pwq;

            public TriggerConditions(
                TriggerState channelA,
                TriggerState channelB,
                TriggerState channelC,
                TriggerState channelD,
                TriggerState external,
                TriggerState pwq)
            {
                this.ChannelA = channelA;
                this.ChannelB = channelB;
                this.ChannelC = channelC;
                this.ChannelD = channelD;
                this.External = external;
                this.Pwq = pwq;
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
 

            public PwqConditions(
                TriggerState channelA,
                TriggerState channelB,
                TriggerState channelC,
                TriggerState channelD,
                TriggerState external)
            {
                this.ChannelA = channelA;
                this.ChannelB = channelB;
                this.ChannelC = channelC;
                this.ChannelD = channelD;
                this.External = external;
            }
        }

		#region Driver Imports

        public unsafe delegate void ps2000StreamingReady(short** overviewBuffers,
                                        short overFlow,
                                        uint triggeredAt,
                                        short triggered,
                                        short auto_stop,
                                        uint nValues);
 
        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_open_unit")]
		public static extern short OpenUnit();

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_close_unit")]
		public static extern short CloseUnit(short handle);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_run_block")]
		public static extern short RunBlock(
												short handle,
												int no_of_samples,
												short timebase,
												short oversample,
												out int timeIndisposedMs);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_run_streaming")]
        public static extern short ps2000_run_streaming(
                                                short handle,
                                                short sample_interval_ms,
                                                int max_samples,
                                                short windowed);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_run_streaming_ns")]
        public static extern short ps2000_run_streaming_ns(
                                                short handle,
                                                uint sample_interval,
                                                ReportedTimeUnits time_units,
                                                uint max_samples,
                                                short autostop,
                                                uint noOfSamplesPerAggregate,
                                                uint overview_buffer_size);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_get_streaming_last_values")]
        public static extern short ps2000_get_streaming_last_values(
                                                short handle,
                                                ps2000StreamingReady lpGetOverviewBuffersMaxMin);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_stop")]
		public static extern short Stop(short handle);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_ready")]
        public static extern short Isready(short handle);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_set_channel")]
		public static extern short SetChannel(
												short handle,
												Channel channel,
												short enabled,
												short dc,
												Range range);


        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000SetAdvTriggerChannelDirections")]
		public static extern short SetTriggerChannelDirections(
												short handle,
												ThresholdDirection channelA,
												ThresholdDirection channelB,
            ThresholdDirection channelC,
                                                ThresholdDirection channelD,
                                                ThresholdDirection ext);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_get_timebase")]
        public static extern short GetTimebase(
                                             short handle,
                                             short timebase,
                                             int noSamples,
                                             out int timeInterval,
                                             out short time_units,
                                             short oversample,
                                             out int maxSamples);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_get_values")]
        public static extern short GetValues(
                short handle,
                short[] buffer_a,
                short[] buffer_b,
                short[] buffer_c,
                short[] buffer_d,
                out short overflow,
                int no_of_values);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000SetPulseWidthQualifier")]
        public static extern short SetPulseWidthQualifier(
            short handle,
            PwqConditions[] conditions,
            short nConditions,
            ThresholdDirection direction,
            uint lower,
            uint upper,
            PulseWidthType type);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000SetAdvTriggerChannelProperties")]
		public static extern short SetTriggerChannelProperties(
			short handle,
			TriggerChannelProperties[] channelProperties,
			short nChannelProperties,
			int autoTriggerMilliseconds);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000SetAdvTriggerChannelConditions")]
		public static extern short SetTriggerChannelConditions(
			short handle,
			TriggerConditions[] conditions,
			short nConditions);

        [DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000SetAdvTriggerDelay")]
		public static extern short SetTriggerDelay(short handle, uint delay, float preTriggerDelay);

		[DllImport(_DRIVER_FILENAME, EntryPoint = "ps2000_get_unit_info")]
		public static extern short GetUnitInfo(
            short handle, 
            StringBuilder infoString, 
            short stringLength, 
            short info); 

		#endregion
	}
}

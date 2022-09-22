/**************************************************************************
 *
 * Filename: PS3000ACSConsole.cs
 *
 * Description:
 *   This is a console-mode program that demonstrates how to use the
 *   PicoScope 3000 Series (ps3000a) driver functions. using .NET
 *
 * Supported PicoScope models:
 *
 *		PicoScope 3204A/B/D
 *		PicoScope 3205A/B/D
 *		PicoScope 3206A/B/D
 *		PicoScope 3207A/B
 *		PicoScope 3204 MSO & D MSO
 *		PicoScope 3205 MSO & D MSO
 *		PicoScope 3206 MSO & D MSO
 *		PicoScope 3404A/B/D/D MSO
 *		PicoScope 3405A/B/D/D MSO
 *		PicoScope 3406A/B/D/D MSO
 *		
 * Examples:
 *    Collect a block of Analogue samples immediately
 *    Collect a block of Analogue samples when a trigger event occurs
 *    Collect Analogue samples in rapid block mode when a trigger event occurs
 *    Collect a stream of Analogue data 
 *    Collect a stream of Analogue data and show when a trigger event occurs
 *   
 *    Collect a block of Digital Samples immediately
 *    Collect a block of Digital Samples when a Digital trigger event occurs
 *    Collect a block of Digital and Analogue Samples when an Analogue AND a Digital trigger event occurs
 *    Collect a block of Digital and Analogue Samples when an Analogue OR a Digital trigger event occurs
 *    Collect a stream of Digital Samples 
 *    Collect a stream of Digital Samples and show Aggregated results
 *
 * Copyright (C) 2011-2018 Pico Technology Ltd. See LICENSE file for terms.
 *  
 **************************************************************************/

using System;
using System.IO;
using System.Threading;
using System.Text;
using System.ComponentModel;

//using PS3000AImports;
using PicoPinnedArray;
using PicoStatus;
using SAKURA_Checker;

namespace SAKURA
{
	struct ChannelSettings3
	{
		public Imports3.Coupling DCcoupled;
		public Imports3.Range range;
		public bool enabled;
	}

	class Pwq3
	{
		public Imports3.PwqConditions[] conditions;
		public short nConditions;
		public Imports3.ThresholdDirection direction;
		public uint lower;
		public uint upper;
		public Imports3.PulseWidthType type;

		public Pwq3(Imports3.PwqConditions[] conditions,
			short nConditions,
			Imports3.ThresholdDirection direction,
			uint lower, uint upper,
			Imports3.PulseWidthType type)
		{
			this.conditions = conditions;
			this.nConditions = nConditions;
			this.direction = direction;
			this.lower = lower;
			this.upper = upper;
			this.type = type;
		}
	}

	class PS3000ACSConsole
	{
		public PS3000ACSConsole() { }
		private readonly short _handle;
		//public const int BUFFER_SIZE = 1188000; //Number of samples per waveform capture for block captures-masked for 7048 cycles
		//public const int BUFFER_SIZE = 528000; //Number of samples per waveform capture for block captures-unmasked for 3912 cycles using 4ns sampling interval
		//public const int BUFFER_SIZE = 140000/*165000*/; //Number of samples per waveform capture for block captures-unmasked for 3912 cycles using 16ns sampling interval
		//public const int BUFFER_SIZE = 42500/*165000*/; //Number of samples per waveform capture for block captures-unmasked for 3912 cycles using 2ns sampling interval
		//public const int BUFFER_SIZE = 2500; //Number of samples per waveform capture for block captures-masked for 7100 cycles using 2ns sampling interval --change
		public const int BUFFER_SIZE = 264000;
		public const int RAPID_BLOCK_BUFFER_SIZE = 100; // Number of samples per waveform capture for rapid block captures
		public const int MAX_CHANNELS = 4;
		public const int QUAD_SCOPE = 4;
		public const int DUAL_SCOPE = 2;
		private CipherModule sakuraRun;
		PinnedArray<short>[] Pinned = new PinnedArray<short>[4];
		bool _hasFastStreaming = false;
		public TVLA tvla;



		public void Open(uint index)
		{
			sakuraRun = new CipherModule(index);
		}

		public void Close()
		{
			sakuraRun.Dispose();
		}
		uint _timebase = 8;
		short _timebase2 = 8;
		short _oversample = 1;
		bool _scaleVoltages = true;

		ushort[] inputRanges = { 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000 };

		bool _ready = false;
		short _trig = 0;
		uint _trigAt = 0;
		int _sampleCount = 0;
		uint _startIndex = 0;
		bool _autoStop;
		short device_handle;

		// Buffers used for streaming data collection

		short[][] appBuffers;
		short[][] buffers;
		short[][] appDigiBuffers;
		short[][] digiBuffers;

		private ChannelSettings3[] _channelSettings;
		private int _channelCount;
		private Imports3.Range _firstRange;
		private Imports3.Range _lastRange;
		private int _digitalPorts;
		private Imports3.ps3000aBlockReady _callbackDelegate;

		private string StreamFile = "stream.txt";
		private string BlockFile = "block.txt";

		/****************************************************************************
		 * StreamingCallback
		 * Used by ps3000a data streaming collection calls, on receipt of data.
		 * Used to set global flags etc checked by user routines
		 ****************************************************************************/
		void StreamingCallback(short handle,
								int noOfSamples,
								uint startIndex,
								short ov,
								uint triggerAt,
								short triggered,
								short autoStop,
								IntPtr pVoid)
		{
			// used for streaming
			_sampleCount = noOfSamples;
			_startIndex = startIndex;
			_autoStop = autoStop != 0;

			// flag to say done reading data
			_ready = true;

			// flags to show if & where a trigger has occurred
			_trig = triggered;
			_trigAt = triggerAt;

			if (_sampleCount != 0)
			{
				switch ((Imports3.Mode)pVoid)
				{
					case Imports3.Mode.ANALOGUE:

						for (int ch = 0; ch < _channelCount * 2; ch += 2)
						{
							if (_channelSettings[(int)(Imports3.Channel.ChannelA + (ch / 2))].enabled)
							{
								Array.Copy(buffers[ch], _startIndex, appBuffers[ch], _startIndex, _sampleCount); //max
								Array.Copy(buffers[ch + 1], _startIndex, appBuffers[ch + 1], _startIndex, _sampleCount); //min
							}
						}
						break;

					case Imports3.Mode.DIGITAL:

						for (int port = 0; port < _digitalPorts; port++) // create data buffers
						{
							Array.Copy(digiBuffers[port], _startIndex, appDigiBuffers[port], _startIndex, _sampleCount); //no max or min
						}
						break;

					case Imports3.Mode.AGGREGATED:

						for (int port = 0; port < _digitalPorts * 2; port += 2) // create data buffers
						{
							Array.Copy(digiBuffers[port], _startIndex, appDigiBuffers[port], _startIndex, _sampleCount); //max
							Array.Copy(digiBuffers[port + 1], _startIndex, appDigiBuffers[port + 1], _startIndex, _sampleCount); //min
						}
						break;
				}
			}
		}

		/****************************************************************************
		 * BlockCallback
		 * used by ps3000a data block collection calls, on receipt of data.
		 * used to set global flags etc checked by user routines
		 ****************************************************************************/
		void BlockCallback(short handle, short status, IntPtr pVoid)
		{
			// flag to say done reading data
			if (status != (short)StatusCodes.PICO_CANCELLED)
			{
				_ready = true;
			}
		}

		/****************************************************************************
		 * SetDefaults - restore default settings
		 ****************************************************************************/
		void SetDefaults()
		{
			for (int i = 0; i < _channelCount; i++) // reset channels to most recent settings
			{
				Imports3.SetChannel(_handle, Imports3.Channel.ChannelA + i,
								   (short)(_channelSettings[(int)(Imports3.Channel.ChannelA + i)].enabled ? 1 : 0),
								   _channelSettings[(int)(Imports3.Channel.ChannelA + i)].DCcoupled,
								   _channelSettings[(int)(Imports3.Channel.ChannelA + i)].range,
								   (float)0.0);
			}
		}

		/****************************************************************************
		* SetDigitals - enable Digital Channels
		****************************************************************************/
		void SetDigitals()
		{
			Imports3.Channel port;
			uint status;
			short logicLevel;
			float logicVoltage = 1.5f;
			short maxLogicVoltage = 5;
			short enabled = 1;

			status = StatusCodes.PICO_OK;

			// Set logic threshold
			logicLevel = (short)((logicVoltage / maxLogicVoltage) * Imports3.MaxLogicLevel);

			// Enable Digital ports
			for (port = Imports3.Channel.PS3000A_DIGITAL_PORT0; port < Imports3.Channel.PS3000A_DIGITAL_PORT2; port++)
			{
				status = Imports3.SetDigitalPort(_handle, port, enabled, logicLevel);
			}
			Console.WriteLine(status != StatusCodes.PICO_OK ? "SetDigitals:Imports3.SetDigitalPort Status = 0x{0:X6}" : "", status);

		}


		/****************************************************************************
		 * DisableDigital - disable Digital Channels
		 ****************************************************************************/
		void DisableDigital()
		{
			Imports3.Channel port;
			uint status;

			status = StatusCodes.PICO_OK;

			// Disable Digital ports 
			for (port = Imports3.Channel.PS3000A_DIGITAL_PORT0; port <= Imports3.Channel.PS3000A_DIGITAL_PORT1; port++)
			{
				status = Imports3.SetDigitalPort(_handle, port, 0, 0);
			}

			Console.WriteLine(status != StatusCodes.PICO_OK ? "DisableDigital:Imports3.SetDigitalPort Status = 0x{0:X6}" : "", status);
		}


		/****************************************************************************
		* DisableAnalogue - disable analogue Channels
		****************************************************************************/
		void DisableAnalogue()
		{
			uint status;

			status = StatusCodes.PICO_OK;

			// Disable analogue ports
			for (int i = 0; i < _channelCount; i++)
			{
				status = Imports3.SetChannel(_handle, Imports3.Channel.ChannelA + i, 0, Imports3.Coupling.DC, 0, (float)0.0);
			}

			Console.WriteLine(status != StatusCodes.PICO_OK ? "DisableAnalogue:Imports3.SetChannel Status = 0x{0:X6}" : "", status);
		}


		/****************************************************************************
		 * adc_to_mv
		 *
		 * Convert an 16-bit ADC count into millivolts
		 ****************************************************************************/
		int adc_to_mv(int raw, int ch)
		{
			return (raw * inputRanges[ch]) / Imports3.MaxValue;
		}

		/****************************************************************************
		 * mv_to_adc
		 *
		 * Convert a millivolt value into a 16-bit ADC count
		 *
		 *  (useful for setting trigger thresholds)
		 ****************************************************************************/
		short mv_to_adc(short mv, short ch)
		{
			return (short)((mv * Imports3.MaxValue) / inputRanges[ch]);
		}

		/****************************************************************************
		 * BlockDataHandler
		 * - Used by all block data routines
		 * - acquires data (user sets trigger mode before calling), displays 10 items
		 *   and saves all to block.txt
		 * Input :
		 * - text : the text to display before the display of data slice
		 * - offset : the offset into the data buffer to start the display's slice.
		 ****************************************************************************/




		void BlockDataHandler(string text, int offset, ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond, ref CipherModule targetModule, Imports3.Mode mode, long curr_trace, int rnd_cnt, ref TVLA tvla_class)

		{
			uint status;
			bool retry;
			uint sampleCount = BUFFER_SIZE;
			uint segmentIndex = 0;




			PinnedArray<short>[] minPinned = new PinnedArray<short>[_channelCount];
			PinnedArray<short>[] maxPinned = new PinnedArray<short>[_channelCount];
			PinnedArray<short>[] digiPinned = new PinnedArray<short>[_digitalPorts];
			mode = Imports3.Mode.ANALOGUE;
			int timeIndisposed;

			if (mode == Imports3.Mode.ANALOGUE || mode == Imports3.Mode.MIXED)
			{

				// Set up data buffers for average data collection on analogue channels

				for (int i = 0; i < _channelCount; i++)
				{
					if (_channelSettings[i].enabled)
					{
						short[] minBuffers = new short[sampleCount];
						short[] maxBuffers = new short[sampleCount];
						minPinned[i] = new PinnedArray<short>(minBuffers);
						maxPinned[i] = new PinnedArray<short>(maxBuffers);

						status = Imports3.SetDataBuffers(_handle, (Imports3.Channel)i, maxBuffers, minBuffers, (int)sampleCount, segmentIndex, Imports3.RatioMode.Average);

						if (status != StatusCodes.PICO_OK)
						{
							Console.WriteLine("BlockDataHandler:Imports3.SetDataBuffers Channel {0} Status = 0x{1:X6}", (char)('A' + i), status);
						}
					}
				}
			}

			if (mode == Imports3.Mode.DIGITAL || mode == Imports3.Mode.MIXED)
			{
				for (int i = 0; i < _digitalPorts; i++)
				{
					short[] digiBuffer = new short[sampleCount];
					digiPinned[i] = new PinnedArray<short>(digiBuffer);

					status = Imports3.SetDataBuffer(_handle, i + Imports3.Channel.PS3000A_DIGITAL_PORT0, digiBuffer, (int)sampleCount, segmentIndex, Imports3.RatioMode.None);

					if (status != StatusCodes.PICO_OK)
					{
						Console.WriteLine("BlockDataHandler:Imports3.SetDataBuffer {0} Status = 0x{1,0:X6}", i + Imports3.Channel.PS3000A_DIGITAL_PORT0, status);
					}
				}
			}

			// Find the maximum number of samples and the time interval (in nanoseconds) at the current _timebase. 
			// Use downsampling as opposed to oversampling if required. 
			int timeInterval = 0;
			int maxSamples;

			while (Imports3.GetTimebase(_handle, _timebase, (int)sampleCount, out timeInterval, _oversample, out maxSamples, 0) != 0)
			{
				Console.WriteLine("Selected timebase {0} could not be used.\n", _timebase);
				_timebase++;

			}
			//Console.WriteLine("Timebase: {0}\t Sampling Interval (ns): {1}  maxSamples: {2}       \n", _timebase, timeInterval, maxSamples);

			// Start it collecting, then wait for completion
			_ready = false;
			// _callbackDelegate = BlockCallback;


			do
			{
				retry = false;

				status = Imports3.RunBlock(_handle, 0, (int)sampleCount, _timebase, _oversample, out timeIndisposed, 0, _callbackDelegate, IntPtr.Zero);
				//status = Imports3.RunBlock(_handle, 0, (int)sampleCount, 3 , 1, out timeIndisposed, 0, _callbackDelegate, IntPtr.Zero);


				if (status == StatusCodes.PICO_POWER_SUPPLY_CONNECTED || status == StatusCodes.PICO_POWER_SUPPLY_NOT_CONNECTED || status == StatusCodes.PICO_POWER_SUPPLY_UNDERVOLTAGE)
				{
					status = PowerSourceSwitch(_handle, status);
					retry = true;
				}
				else
				{
					if (status != (short)StatusCodes.PICO_OK)
					{
						Console.WriteLine("BlockDataHandler:Imports3.RunBlock Status = 0x{0:X6}");
					}
					else
					{
						// _ready = true;
						//Console.WriteLine("", status);
					}

				}
				//Thread.Sleep(1);
			}
			while (retry);

			//Console.WriteLine("Waiting for data...Press a key to abort");
			//Console.WriteLine();


			short ready = 0;
			short okay = 0;
			Imports3.IsReady(_handle, out ready);
			while (ready == 0)
			{
				targetModule.Run(ref HWOut, inputtext, wait, ref elapsedMillisecond);
				Thread.Sleep(1);
				Imports3.IsReady(_handle, out ready);
			}

			//       if (Console.KeyAvailable)
			//      {
			//          Console.ReadKey(true); // clear the key
			//     }

			//       Imports3.Stop(_handle);

			if (ready > 0)
			{
				short overflow;
				uint startIndex = 0;
				uint downSampleRatio = 0;
				string fname = "block.csv";
				string tvla_name = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project/data/tvla.csv";
				// Request data from the driver for analogue channels
				if (mode == Imports3.Mode.ANALOGUE || mode == Imports3.Mode.MIXED)
				{
					status = Imports3.GetValues(_handle, startIndex, ref sampleCount, downSampleRatio, Imports3.RatioMode.Average, segmentIndex, out overflow); // Average data collection
				}

				if (mode == Imports3.Mode.DIGITAL || mode == Imports3.Mode.MIXED)
				{
					status = Imports3.GetValues(_handle, startIndex, ref sampleCount, downSampleRatio, Imports3.RatioMode.None, segmentIndex, out overflow);
				}
				int page_number = rnd_cnt / 100000;
				string string1;
				string string2 = page_number.ToString();
				if (curr_trace == 0)
					string1 = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project/data/powertrace_fixed_";
				else
					string1 = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project/data/powertrace_rnd_";

				fname = string1 + string2 + ".csv";

				sampleCount = Math.Min(sampleCount, BUFFER_SIZE);

				if (rnd_cnt<50000)
				{ 
					using (StreamWriter writer = File.AppendText(fname))
					{
						for (int i = 0; i < sampleCount; i++)
						{
							for (int ch = 0; ch < 1; ch++)
							{
								if (_channelSettings[ch].enabled)
								{
									writer.Write(maxPinned[ch].Target[i] + ",");
								}
							}
						}
						writer.WriteLine();
						writer.Close();
					}
				}

				for (int ch = 0; ch < 1; ch++)
				{
					if (_channelSettings[ch].enabled)
					{
						tvla_class.keep_mean_var(maxPinned[ch].Target, (int)curr_trace);
					}
				}
				if (rnd_cnt % 100 == 99)
				{
					tvla_class.do_TVLA();
					using (StreamWriter writer = File.AppendText(tvla_name))
					{
						for (int i = 0; i < sampleCount; i++)
						{
							writer.Write(tvla_class.t_values[i] + ",");
						}
						writer.WriteLine();
						writer.Close();
					}
				}
			}
			else
			{
				Console.WriteLine("data collection aborted");
			}




			/*

            if (status == StatusCodes.PICO_OK)
                    {

                        // Print out the first 10 readings, converting the readings to mV if required 
                        Console.WriteLine(text);
                        Console.WriteLine();

                        if (mode == Imports3.Mode.ANALOGUE || mode == Imports3.Mode.MIXED)
                        {
                            Console.WriteLine("Value {0}", (_scaleVoltages) ? ("mV") : ("ADC Counts"));

                            for (int ch = 0; ch < _channelCount; ch++)
                            {
                                if (_channelSettings[ch].enabled)
                                {
                                    Console.Write("Channel {0}          ", (char)('A' + ch));
                                }
                            }
                        }
                        if (mode == Imports3.Mode.DIGITAL || mode == Imports3.Mode.MIXED)
                        {
                            Console.Write("DIGITAL VALUE");
                        }

                        Console.WriteLine();


                        for (int i = offset; i < offset + 10; i++)
                        {
                            if (mode == Imports3.Mode.ANALOGUE || mode == Imports3.Mode.MIXED)
                            {
                                for (int ch = 0; ch < _channelCount; ch++)
                                {
                                    if (_channelSettings[ch].enabled)
                                    {
                                        Console.Write("{0,8}          ", _scaleVoltages ?
                                            adc_to_mv(maxPinned[ch].Target[i], (int)_channelSettings[(int)(Imports3.Channel.ChannelA + ch)].range)  // If _scaleVoltages, show mV values
                                            : maxPinned[ch].Target[i]);                                                                           // else show ADC counts
                                    }
                                }
                            }
                            if (mode == Imports3.Mode.DIGITAL || mode == Imports3.Mode.MIXED)
                            {

                                short digiValue = (short) (0x00ff & digiPinned[1].Target[i]); // Mask lower 8-bits to get Port 1 data values
                                digiValue <<= 8;    // Shift by 8 bits
                                digiValue |= (short)(0x00ff & digiPinned[0].Target[i]); // Mask Port 0 values to get lower 8 bits and apply bitwise inclusive OR to combine with Port 1 values  
                                Console.Write("0x{0,4:X}", digiValue.ToString("X4"));
                            }
                            Console.WriteLine();
                        }

                        if (mode == Imports3.Mode.ANALOGUE || mode == Imports3.Mode.MIXED)
                        {
                            PrintBlockFile(Math.Min(sampleCount, BUFFER_SIZE), timeInterval, minPinned, maxPinned);                        
                        }
                    }
                    else
                    {
                        if (status == (short)StatusCodes.PICO_POWER_SUPPLY_CONNECTED || status == (short)StatusCodes.PICO_POWER_SUPPLY_NOT_CONNECTED || status == (short)StatusCodes.PICO_POWER_SUPPLY_UNDERVOLTAGE)
                        {
                            if (status == (short)StatusCodes.PICO_POWER_SUPPLY_UNDERVOLTAGE)
                            {
                                status = PowerSourceSwitch(_handle, status);
                            }
                            else
                            {
                                Console.WriteLine("Power source changed. Data collection aborted");
                            }
                        }
                        else
                        {
                            Console.WriteLine("BlockDataHandler:Imports3.GetValues Status = 0x{0:X6}", status);
                        }
                    }
                }
                else
                {
                    Console.WriteLine("Data collection aborted.");
                }
                */
			Imports3.Stop(_handle);

			if (mode == Imports3.Mode.ANALOGUE || mode == Imports3.Mode.MIXED)
			{
				foreach (PinnedArray<short> p in minPinned)
				{
					if (p != null)
					{
						p.Dispose();
					}
				}
				foreach (PinnedArray<short> p in maxPinned)
				{
					if (p != null)
					{
						p.Dispose();
					}
				}
			}

			if (mode == Imports3.Mode.DIGITAL || mode == Imports3.Mode.MIXED)
			{
				foreach (PinnedArray<short> p in digiPinned)
				{
					if (p != null)
					{
						p.Dispose();
					}
				}
			}
		}

		/// <summary>
		/// Print the block data capture to file 
		/// </summary>
		private void PrintBlockFile(uint sampleCount, int timeInterval, PinnedArray<short>[] minPinned, PinnedArray<short>[] maxPinned)
		{
			var sb = new StringBuilder();

			sb.AppendFormat("For each of the {0} Channels, results shown are....", _channelCount);
			sb.AppendLine();
			sb.AppendLine("Time interval Maximum Aggregated value ADC Count & mV, Minimum Aggregated value ADC Count & mV");
			sb.AppendLine();

			// Build Header
			string[] heading = { "Time", "Channel", "Max ADC", "Max mV", "Min ADC", "Min mV" };

			for (int i = 0; i < _channelCount; i++)
			{
				if (_channelSettings[i].enabled)
				{
					sb.AppendFormat("{0,10} {1,10} {2,10} {3,10} {4,10} {5,10}",
									heading[0],
									heading[1],
									heading[2],
									heading[3],
									heading[4],
									heading[5]);
				}
			}

			sb.AppendLine();

			// Build Body
			for (int i = 0; i < sampleCount; i++)
			{
				for (int ch = 0; ch < _channelCount; ch++)
				{
					if (_channelSettings[ch].enabled)
					{
						sb.AppendFormat("{0,10} {1,10} {2,10} {3,10} {4,10} {5,10}",
										i * timeInterval,
										(char)('A' + ch),
										maxPinned[ch].Target[i],
										adc_to_mv(maxPinned[ch].Target[i], (int)_channelSettings[(int)(Imports3.Channel.ChannelA + ch)].range),
										minPinned[ch].Target[i],
										adc_to_mv(minPinned[ch].Target[i], (int)_channelSettings[(int)(Imports3.Channel.ChannelA + ch)].range));
					}
				}

				sb.AppendLine();
			}

			// Print contents to file
			using (TextWriter writer = new StreamWriter(BlockFile, false))
			{
				writer.Write(sb.ToString());
				writer.Close();
			}
		}


		/****************************************************************************
		 * RapidBlockDataHandler
		 * - Used by the CollectRapidBlock routine
		 * - acquires data (user sets trigger mode before calling), displays 10 items
		 *   and saves all to data.txt
		 * Input :
		 * - nRapidCaptures : the user specified number of blocks to capture
		 ****************************************************************************/
		private void RapidBlockDataHandler(uint nRapidCaptures)
		{
			int numChannels = _channelCount;
			int chan = 0;

			uint status;
			uint numSamples = RAPID_BLOCK_BUFFER_SIZE;
			uint numActualCaptures = 0;
			bool isTriggerTimestampingSupported = false;

			UInt64 timeStamp = 0; // Displayed as a difference in nanoseconds

			// Ensure timebase is valid

			int timeInterval = 0;
			int maxSamples = 0;

			status = StatusCodes.PICO_INVALID_TIMEBASE;

			do
			{
				status = Imports3.GetTimebase(_handle, _timebase, (int)numSamples, out timeInterval, _oversample, out maxSamples, 0);

				if (status != StatusCodes.PICO_OK)
				{
					Console.WriteLine("Selected timebase {0} could not be used.\n", _timebase);
					_timebase++;
				}

			}
			while (status != StatusCodes.PICO_OK);

			Console.WriteLine("Timebase: {0}\t Sampling Interval (ns): {1}\nMax Samples per Channel per Segment: {2}\n", _timebase, timeInterval, maxSamples);


			// Run the rapid block capture
			int timeIndisposed = 0;
			_ready = false;

			_callbackDelegate = BlockCallback;

			Imports3.RunBlock(_handle,
						0,
						(int)numSamples,
						_timebase,
						_oversample,
						out timeIndisposed,
						0,
						_callbackDelegate,
						IntPtr.Zero);




			Console.WriteLine("Waiting for data... Press a key to abort.");

			while (!_ready && !Console.KeyAvailable)
			{
				Thread.Sleep(10);
			}

			if (Console.KeyAvailable)
			{
				Console.ReadKey(true); // clear the key
			}

			Imports3.Stop(_handle);

			if (!_ready)
			{
				// Obtain number of captures
				status = Imports3.GetNoOfRapidCaptures(_handle, out numActualCaptures);
				Console.WriteLine("Rapid capture aborted. {0} complete blocks were captured\n", numActualCaptures);

				if (numActualCaptures == 0)
				{
					return;
				}

				// Only display the blocks that were captured
				nRapidCaptures = numActualCaptures;
			}


			// Set up the data arrays and pin them
			short[][][] values = new short[nRapidCaptures][][];
			PinnedArray<short>[,] pinned = new PinnedArray<short>[nRapidCaptures, numChannels];

			for (uint segment = 0; segment < nRapidCaptures; segment++)
			{
				values[segment] = new short[numChannels][];

				for (short channel = 0; channel < numChannels; channel++)
				{
					if (_channelSettings[channel].enabled)
					{
						values[segment][channel] = new short[numSamples];
						pinned[segment, channel] = new PinnedArray<short>(values[segment][channel]);

						status = Imports3.SetDataBuffer(_handle, (Imports3.Channel)channel, values[segment][channel], (int)numSamples, segment, Imports3.RatioMode.None);

						if (status != StatusCodes.PICO_OK)
						{
							Console.WriteLine("RapidBlockDataHandler:Imports3.SetDataBuffer Channel {0} Status = 0x{1:X6}", (char)('A' + channel), status);
						}

					}
					else
					{
						status = Imports3.SetDataBuffer(_handle, (Imports3.Channel)channel, null, 0, segment, Imports3.RatioMode.None);

						if (status != StatusCodes.PICO_OK)
						{
							Console.WriteLine("RapidBlockDataHandler:Imports3.SetDataBuffer Channel {0} Status = 0x{1:X6}", (char)('A' + channel), status);
						}

					}
				}
			}

			// Setup array for overflow
			short[] overflows = new short[nRapidCaptures];

			// Allocate memory for structures to retrieve trigger timestamp information
			Imports3.TriggerInfo[] triggerInfo = new Imports3.TriggerInfo[nRapidCaptures];

			// Retrieve the data
			status = Imports3.GetValuesRapid(_handle, ref numSamples, 0, (nRapidCaptures - 1), 1, Imports3.RatioMode.None, overflows);

			// Obtain trigger timestamping information
			status = Imports3.GetTriggerInfoBulk(_handle, triggerInfo, 0, (nRapidCaptures - 1));

			if (status == StatusCodes.PICO_OK)
			{
				isTriggerTimestampingSupported = true;
			}
			else if (status == StatusCodes.PICO_NOT_SUPPORTED_BY_THIS_DEVICE)
			{
				Console.WriteLine("RapidBlockDataHandler:Trigger timestamping not supported by this device.");
				isTriggerTimestampingSupported = false;
			}
			else
			{
				Console.WriteLine("RapidBlockDataHandler:Imports3.GetTriggerInfoBulk Status = 0x{1:X6}", status);
			}

			/* Print out the first 10 readings, converting the readings to mV if required */
			Console.WriteLine("\nValues in {0}", (_scaleVoltages) ? ("mV") : ("ADC Counts"));
			Console.WriteLine();

			for (uint seg = 0; seg < nRapidCaptures; seg++)
			{
				Console.WriteLine("Capture {0}:\n", seg + 1);

				if (isTriggerTimestampingSupported == true)
				{
					// Trigger Info status & Timestamp 
					Console.WriteLine("Trigger Info:- Status: {0}  Timestamp Counter: {1}\n", triggerInfo[seg].status, triggerInfo[seg].timeStampCounter);

					// Calculate time between trigger events - the first timestamp is arbitrary so is only used to calculate offsets

					// The structure containing the status code with bit flag PICO_DEVICE_TIME_STAMP_RESET will have an arbitrary timeStampCounter value. 
					// This should be the first segment in each run, so in this case segment 0 will be ignored.

					if (seg == 0)
					{
						// Nothing to display
					}
					else if (seg > 0 && triggerInfo[seg].status == StatusCodes.PICO_OK)
					{
						timeStamp = triggerInfo[seg].timeStampCounter - triggerInfo[seg - 1].timeStampCounter;
						Console.WriteLine("Time since trigger for last segment: {0} ns\n", (timeStamp * (UInt64)timeInterval));
					}
					else
					{
						// Do nothing
					}
				}

				for (chan = 0; chan < _channelCount; chan++)
				{
					if (_channelSettings[chan].enabled)
					{
						Console.Write("Ch. {0}\t", (char)('A' + chan));
					}
				}

				Console.WriteLine("\n");

				for (int i = 0; i < 10; i++)
				{
					for (chan = 0; chan < _channelCount; chan++)
					{
						if (_channelSettings[chan].enabled)
						{
							Console.Write("{0}\t", _scaleVoltages ?
													adc_to_mv(pinned[seg, chan].Target[i], (int)_channelSettings[(int)(Imports3.Channel.ChannelA + chan)].range) // If _scaleVoltages, show mV values
													: pinned[seg, chan].Target[i]);                                                                             // else show ADC counts
						}
					}

					Console.WriteLine();
				}

				Console.WriteLine();
			}

			// Un-pin the arrays
			foreach (PinnedArray<short> p in pinned)
			{
				if (p != null)
				{
					p.Dispose();
				}
			}

			//TODO: Do what ever is required with the data here.
		}


		/****************************************************************************
		*  WaitForKey
		*  Wait for user's keypress
		****************************************************************************/
		private static void WaitForKey()
		{
			while (!Console.KeyAvailable)
			{
				Thread.Sleep(100);
			}

			if (Console.KeyAvailable)
			{
				Console.ReadKey(true); // clear the key
			}
		}

		/****************************************************************************
		*  SetTrigger  (Analogue Channels)
		*  This function sets all the required trigger parameters, and calls the 
		*  triggering functions
		****************************************************************************/
		uint SetTrigger(Imports3.TriggerChannelProperties[] channelProperties,
							short nChannelProperties,
							Imports3.TriggerConditions[] triggerConditions,
							short nTriggerConditions,
							Imports3.ThresholdDirection[] directions,
							Pwq3 pwq3,
							uint delay,
							short auxOutputEnabled,
							int autoTriggerMs)
		{
			uint status;

			if ((status = Imports3.SetTriggerChannelProperties(_handle, channelProperties, nChannelProperties, auxOutputEnabled,
																autoTriggerMs)) != 0)
			{
				return status;
			}

			if ((status = Imports3.SetTriggerChannelConditions(_handle, triggerConditions, nTriggerConditions)) != 0)
			{
				return status;
			}

			if (directions == null) directions = new Imports3.ThresholdDirection[] { Imports3.ThresholdDirection.None,
				Imports3.ThresholdDirection.None, Imports3.ThresholdDirection.None, Imports3.ThresholdDirection.None,
				Imports3.ThresholdDirection.None, Imports3.ThresholdDirection.None};

			if ((status = Imports3.SetTriggerChannelDirections(_handle,
															  directions[(int)Imports3.Channel.ChannelA],
															  directions[(int)Imports3.Channel.ChannelB],
															  directions[(int)Imports3.Channel.ChannelC],
															  directions[(int)Imports3.Channel.ChannelD],
															  directions[(int)Imports3.Channel.External],
															  directions[(int)Imports3.Channel.Aux])) != 0)
			{
				return status;
			}

			if ((status = Imports3.SetTriggerDelay(_handle, delay)) != 0)
			{
				return status;
			}

			if (pwq3 == null) pwq3 = new Pwq3(null, 0, Imports3.ThresholdDirection.None, 0, 0, Imports3.PulseWidthType.None);

			status = Imports3.SetPulseWidthQualifier(_handle, pwq3.conditions,
													pwq3.nConditions, pwq3.direction,
													pwq3.lower, pwq3.upper, pwq3.type);

			return status;
		}

		/****************************************************************************
	   *  SetTrigger
	   *  this overloaded version of SetTrigger includes digital parameters
	   ****************************************************************************/
		uint SetTrigger(Imports3.TriggerChannelProperties[] channelProperties,
							short nChannelProperties,
							Imports3.TriggerConditionsV2[] triggerConditions,
							short nTriggerConditions,
							Imports3.ThresholdDirection[] directions,
							Pwq3 pwq3,
							uint delay,
							short auxOutputEnabled,
							int autoTriggerMs,
							Imports3.DigitalChannelDirections[] digitalDirections,
							short nDigitalDirections)
		{
			uint status;

			if (
			  (status = Imports3.SetTriggerChannelProperties(_handle, channelProperties, nChannelProperties, auxOutputEnabled,
												   autoTriggerMs)) != 0)
			{
				return status;
			}

			if ((status = Imports3.SetTriggerChannelConditionsV2(_handle, triggerConditions, nTriggerConditions)) != 0)
			{
				return status;
			}

			if (directions == null)
			{
				directions = new Imports3.ThresholdDirection[] { Imports3.ThresholdDirection.None,
				Imports3.ThresholdDirection.None, Imports3.ThresholdDirection.None, Imports3.ThresholdDirection.None,
				Imports3.ThresholdDirection.None, Imports3.ThresholdDirection.None};
			}

			if ((status = Imports3.SetTriggerChannelDirections(_handle,
															  directions[(int)Imports3.Channel.ChannelA],
															  directions[(int)Imports3.Channel.ChannelB],
															  directions[(int)Imports3.Channel.ChannelC],
															  directions[(int)Imports3.Channel.ChannelD],
															  directions[(int)Imports3.Channel.External],
															  directions[(int)Imports3.Channel.Aux])) != 0)
			{
				return status;
			}

			if ((status = Imports3.SetTriggerDelay(_handle, delay)) != 0)
			{
				return status;
			}

			if (pwq3 == null)
			{
				pwq3 = new Pwq3(null, 0, Imports3.ThresholdDirection.None, 0, 0, Imports3.PulseWidthType.None);
			}

			status = Imports3.SetPulseWidthQualifier(_handle, pwq3.conditions,
													pwq3.nConditions, pwq3.direction,
													pwq3.lower, pwq3.upper, pwq3.type);

			if (_digitalPorts > 0)
			{
				status = Imports3.SetTriggerDigitalPort(_handle, digitalDirections, nDigitalDirections);

				if (status != 0)
				{
					return status;
				}
			}

			return status;
		}

		/****************************************************************************
		* CollectBlockImmediate
		*  this function demonstrates how to collect a single block of data
		*  from the unit (start collecting immediately)
		****************************************************************************/
		/*void CollectBlockImmediate()
		{
			Console.WriteLine("Collect block immediate...");
			Console.WriteLine("Press a key to start");
			WaitForKey();

			SetDefaults();

			// Trigger disabled	
			SetTrigger(null, 0, null, 0, null, null, 0, 0, 0);

			BlockDataHandler("First 10 readings", 0, Imports3.Mode.ANALOGUE);
		}
    */
		/****************************************************************************
		*  CollectRapidBlock
		*  this function demonstrates how to collect blocks of data
		* using the RapidCapture function
		****************************************************************************/
		/*
				void CollectRapidBlock()
				{

					uint numRapidCaptures = 1;
					uint status = StatusCodes.PICO_OK;
					uint maxSegments = 0;
					bool valid = false;

					Console.WriteLine("Collect data in rapid block mode...");

					status = Imports3.GetMaxSegments(_handle, out maxSegments);

					Console.WriteLine("Specify number of captures (max. {0}):", maxSegments);

					do
					{
						try
						{
							numRapidCaptures = uint.Parse(Console.ReadLine());
							valid = true;
						}
						catch
						{
							valid = false;
							Console.WriteLine("\nEnter numeric values only:");
						}

					} while (Imports3.SetNoOfRapidCaptures(_handle, numRapidCaptures) > 0 || !valid);



					int maxSamples;
					Imports3.MemorySegments(_handle, numRapidCaptures, out maxSamples);

					Console.WriteLine("Collecting {0} waveforms. Press a key to start.", numRapidCaptures);

					WaitForKey();

					SetDefaults();

					// Set simple trigger on Channel A

					short triggerVoltage = mv_to_adc(1000, (short)_channelSettings[(int)Imports3.Channel.ChannelA].range); // ChannelInfo stores ADC counts

					status = Imports3.SetSimpleTrigger(_handle, 1, Imports3.Channel.ChannelA, triggerVoltage, Imports3.ThresholdDirection.Rising, 0, 0);

					RapidBlockDataHandler(numRapidCaptures);
				}
				*/
		/****************************************************************************
	   * CollectBlockTriggered
	   *  this function demonstrates how to collect a single block of data from the
	   *  unit, when a trigger event occurs.
	   ****************************************************************************/
		void CollectBlockTriggered(ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond, ref CipherModule targetModule, long curr_trace, int rnd_cnt, ref TVLA tvla_class)
		{
			// short triggerVoltage = mv_to_adc(1000, (short)_channelSettings[(int)Imports3.Channel.ChannelA].range); // ChannelInfo stores ADC counts
			short triggerVoltage = mv_to_adc(150, (short)_channelSettings[(int)Imports3.Channel.ChannelB].range); // ChannelInfo stores ADC counts
			ushort triggerVoltageSame = (ushort)triggerVoltage;
			Imports3.TriggerChannelProperties[] sourceDetails = new Imports3.TriggerChannelProperties[] {
				new Imports3.TriggerChannelProperties(triggerVoltage,
														triggerVoltageSame,// 256*10,
                                                         triggerVoltage,
														 256*10,
														 Imports3.Channel.ChannelB,
														 Imports3.ThresholdMode.Level)};

			Imports3.TriggerConditions[] conditions = new Imports3.TriggerConditions[] {
			  new Imports3.TriggerConditions(Imports3.TriggerState.DontCare,// Channel A
                                            Imports3.TriggerState.True,// Channel B
                                            Imports3.TriggerState.DontCare,
											Imports3.TriggerState.DontCare,
											Imports3.TriggerState.DontCare, //External
                                            Imports3.TriggerState.DontCare,
											Imports3.TriggerState.DontCare)};

			Imports3.ThresholdDirection[] directions = new Imports3.ThresholdDirection[]
											{ Imports3.ThresholdDirection.None,
											Imports3.ThresholdDirection.Rising, //ChannelB
                                            Imports3.ThresholdDirection.None,
											Imports3.ThresholdDirection.None,
											Imports3.ThresholdDirection.None, //External
                                            Imports3.ThresholdDirection.None };

			SetDefaults();

			/* Trigger enabled
			 * Rising edge
			 * Threshold = 1000mV */
			SetTrigger(sourceDetails, 1, conditions, 1, directions, null, 0, 0, 0);

			// BlockDataHandler("Ten readings after trigger:", 0, Imports3.Mode.ANALOGUE);
			BlockDataHandler("", 0, ref HWOut, ref HWMask, inputtext, wait, ref elapsedMillisecond, ref targetModule, Imports3.Mode.ANALOGUE, curr_trace, rnd_cnt, ref tvla_class);
		}

		/****************************************************************************
		* Initialise unit' structure with Variant specific defaults
		****************************************************************************/
		void GetDeviceInfo()
		{
			_firstRange = Imports3.Range.Range_20MV;
			_lastRange = Imports3.Range.Range_20V;
			_channelCount = DUAL_SCOPE;
			string[] description = {
						   "Driver Version    ",
						   "USB Version       ",
						   "Hardware Version  ",
						   "Variant Info      ",
						   "Serial            ",
						   "Cal Date          ",
						   "Kernel Ver.       ",
						   "Digital Hardware  ",
						   "Analogue Hardware ",
						   "Firmware 1        ",
						   "Firmware 2        "
						 };

			System.Text.StringBuilder line = new System.Text.StringBuilder(80);
			if (_handle >= 0)
			{

				for (short i = 0; i < 9; i++)
				{
					short requiredSize;
					Imports3.GetUnitInfo(_handle, line, 80, out requiredSize, i);
					if (i == 3)
					{

						if ((_channelCount = Convert.ToInt16(line[1]) - 48) == 1)
						{
							_firstRange = Imports3.Range.Range_100MV;
						}
						else if ((Convert.ToInt16(line[3]) - 48) >= 3)
						{
							_hasFastStreaming = true;
						}

					}
					//Console.WriteLine("{0}: {1}", description[i], line);
				}
			}

			/*
                        if (_handle >= 0)
                        {
                            for (int i = 0; i < description.Length; i++)
                            {
                                short requiredSize;
                                Imports3.GetUnitInfo(_handle, line, 80, out requiredSize, i);

                                if (i == 3)
                                {
                                    if (line[1] == '4')  // PicoScope 3400 A/B/D/D MSO device
                                    {
                                        _channelCount = QUAD_SCOPE;
                                    }
                                    else
                                    {
                                        _channelCount = DUAL_SCOPE;
                                    }

                                    // Voltage range will depend on the variant - PicoScope 3000 A/B and 3204/5/6 MSO devices have a different lower range.

                                    if (line[4] == 'A' || line[4] == 'B' || (line.Length ==  7 && line[4] == 'M'))
                                    {
                                        _firstRange = Imports3.Range.Range_50MV;
                                    }
                                    else
                                    {
                                        _firstRange = Imports3.Range.Range_20MV;
                                    }

                                    // Check if device has digital channels
                                    if (line.ToString().EndsWith("MSO"))
                                    {
                                        _digitalPorts = 2;
                                    }
                                    else
                                    {
                                        _digitalPorts = 0;
                                    }

                                }

                                Console.WriteLine("{0}: {1}", description[i], line);
                            }

                            _lastRange = Imports3.Range.Range_20V;
                        }
                        */

		}

		/****************************************************************************
		 * Select input voltage ranges for analog channels
		 ****************************************************************************/
		void SetVoltages()
		{
			bool valid = false;
			short count = 0;

			/* See what ranges are available... */
			for (int i = (int)_firstRange; i <= (int)_lastRange; i++)
			{
				//	Console.WriteLine("{0} . {1} mV", i, inputRanges[i]);
			}
			uint range = 8;
			do
			{

				/* Ask the user to select a range */
				//Console.WriteLine("\nSpecify voltage range ({0}..{1})", _firstRange, _lastRange);
				//Console.WriteLine("99 - switches channel off");
				for (int ch = 0; ch < _channelCount; ch++)
				{
					do
					{
						try
						{
							//Console.WriteLine("Channel: {0}", (char)('A' + ch));
							//range = uint.Parse(Console.ReadLine());
							if (ch == 0)
								range = 5;
							else
								range = 6;

							valid = true;
						}
						catch (FormatException)
						{
							valid = false;
							Console.WriteLine("\nEnter numeric values only");
						}

					} while ((range != 99 && (range < (uint)_firstRange || range > (uint)_lastRange) || !valid));


					if (range != 99)
					{
						_channelSettings[ch].range = (Imports3.Range)range;
						//Console.WriteLine(" = {0} mV", inputRanges[range]);
						_channelSettings[ch].enabled = true;
						count++;
					}
					else
					{
						Console.WriteLine("Channel Switched off");
						_channelSettings[ch].enabled = false;
						//_channelSettings[ch].range = Imports3.Range.Range_MAX_RANGE - 1;
					}
				}
				Console.Write(count == 0 ? "\n*** At least 1 channel must be enabled *** \n" : "");
			}
			while (count == 0); // must have at least one channel enabled
								//Console.WriteLine("Range: {0}", range);
								//SetDefaults();  // Set defaults now, so that if all but 1 channels get switched off, timebase updates to timebase 0 will work
		}

		/****************************************************************************
		 * SetTimebase
		 * Select timebase and set _oversample to 1
		 *
		 ****************************************************************************/
		void SetTimebase()
		{
			int timeInterval;
			int maxSamples;
			bool valid = false;

			Console.WriteLine("Specify timebase index:");

			do
			{
				try
				{
					_timebase = uint.Parse(Console.ReadLine());
					valid = true;
				}
				catch
				{
					valid = false;
					Console.WriteLine("\nEnter numeric values only");
				}

			} while (!valid);

			while (Imports3.GetTimebase(_handle, _timebase, BUFFER_SIZE, out timeInterval, 1, out maxSamples, 0) != 0)
			{
				Console.WriteLine("Selected timebase index {0} could not be used", _timebase);
				_timebase++;
			}

			Console.WriteLine("Timebase index {0} - {1} ns", _timebase, timeInterval);
			_oversample = 1;//changed 1 to 0
		}


		/****************************************************************************
		* Stream Data Handler
		* - Used by the two stream data examples - untriggered and triggered
		* Inputs:
		* - preTrigger - the number of samples in the pre-trigger phase 
		*					(0 if no trigger has been set)
		*	mode  - ANALOGUE, 
		***************************************************************************/
		void StreamDataHandler(uint preTrigger, Imports3.Mode mode)
		{
			uint tempBufferSize = 50000; /*  Make sure buffer large enough to collect data on each iteration*/

			uint totalsamples = 0;
			uint triggeredAt = 0;
			uint status;

			uint downsampleRatio;
			Imports3.ReportedTimeUnits timeUnits;
			uint sampleInterval;
			Imports3.RatioMode ratioMode;
			uint postTrigger;
			bool autoStop;
			bool retry;
			bool powerChange = false;

			/* Use Pinned Arrays for the application buffers - data is copied from the driver 
				buffers into these buffers in the streaming callback function */
			PinnedArray<short>[] appBuffersPinned = new PinnedArray<short>[_channelCount * 2];
			PinnedArray<short>[] appDigiBuffersPinned = new PinnedArray<short>[_digitalPorts * 2];

			sampleInterval = 1;
			status = StatusCodes.PICO_OK;

			switch (mode)
			{
				case Imports3.Mode.ANALOGUE:

					appBuffers = new short[_channelCount * 2][];
					buffers = new short[_channelCount * 2][];

					for (int channel = 0; channel < _channelCount * 2; channel += 2) // create data buffers
					{
						if (_channelSettings[channel / 2].enabled)
						{
							appBuffers[channel] = new short[tempBufferSize];
							appBuffers[channel + 1] = new short[tempBufferSize];

							appBuffersPinned[channel] = new PinnedArray<short>(appBuffers[channel]);
							appBuffersPinned[channel + 1] = new PinnedArray<short>(appBuffers[channel + 1]);

							buffers[channel] = new short[tempBufferSize];
							buffers[channel + 1] = new short[tempBufferSize];

							status = Imports3.SetDataBuffers(_handle, (Imports3.Channel)(channel / 2), buffers[channel], buffers[channel + 1], (int)tempBufferSize, 0, Imports3.RatioMode.Aggregate);

							if (status != StatusCodes.PICO_OK)
							{
								Console.WriteLine("StreamDataHandler:Imports3.SetDataBuffers Channel {0} Status = 0x{1:X6}\n", (char)('A' + channel), status);
							}
						}
					}

					downsampleRatio = 1000;
					timeUnits = Imports3.ReportedTimeUnits.MicroSeconds;
					sampleInterval = 1;
					ratioMode = Imports3.RatioMode.Aggregate;
					postTrigger = 1000000;
					autoStop = true;
					break;

				case Imports3.Mode.AGGREGATED:

					appDigiBuffers = new short[_digitalPorts * 2][];
					digiBuffers = new short[_digitalPorts * 2][];

					for (int port = 0; port < _digitalPorts * 2; port += 2) // create data buffers
					{
						appDigiBuffers[port] = new short[tempBufferSize];
						appDigiBuffers[port + 1] = new short[tempBufferSize];

						appDigiBuffersPinned[port] = new PinnedArray<short>(appDigiBuffers[port]);
						appDigiBuffersPinned[port + 1] = new PinnedArray<short>(appDigiBuffers[port + 1]);

						digiBuffers[port] = new short[tempBufferSize];
						digiBuffers[port + 1] = new short[tempBufferSize];

						status = Imports3.SetDataBuffers(_handle, (Imports3.Channel)((port / 2) + Imports3.Channel.PS3000A_DIGITAL_PORT0), digiBuffers[port], digiBuffers[port + 1], (int)tempBufferSize, 0, Imports3.RatioMode.Aggregate);

						if (status != StatusCodes.PICO_OK)
						{
							Console.WriteLine("StreamDataHandler:Imports3.SetDataBuffers {0} Status = 0x{1:X6}", (Imports3.Channel)port + (short)Imports3.Channel.PS3000A_DIGITAL_PORT0, status);
						}
					}

					downsampleRatio = 10;
					timeUnits = Imports3.ReportedTimeUnits.MilliSeconds;
					sampleInterval = 10;
					ratioMode = Imports3.RatioMode.Aggregate;
					postTrigger = 10;
					autoStop = false;
					break;

				case Imports3.Mode.DIGITAL:

					appDigiBuffers = new short[_digitalPorts][];
					digiBuffers = new short[_digitalPorts][];

					for (int port = 0; port < _digitalPorts; port++) // create data buffers
					{
						appDigiBuffers[port] = new short[tempBufferSize];
						appDigiBuffersPinned[port] = new PinnedArray<short>(appDigiBuffers[port]);

						digiBuffers[port] = new short[tempBufferSize];

						Imports3.Channel channel = (Imports3.Channel)(port + 128);

						status = Imports3.SetDataBuffer(_handle, (Imports3.Channel)((port) + Imports3.Channel.PS3000A_DIGITAL_PORT0), digiBuffers[port], (int)tempBufferSize, 0, Imports3.RatioMode.None);

						if (status != StatusCodes.PICO_OK)
						{
							Console.WriteLine("StreamDataHandler:Imports3.SetDataBuffer {0} Status = 0x{1:X6}", (Imports3.Channel)port + (short)Imports3.Channel.PS3000A_DIGITAL_PORT0, status);
						}
					}

					downsampleRatio = 1;
					timeUnits = Imports3.ReportedTimeUnits.MilliSeconds;
					sampleInterval = 10;
					ratioMode = Imports3.RatioMode.None;
					postTrigger = 10;
					autoStop = false;
					break;

				default:

					downsampleRatio = 1;
					timeUnits = Imports3.ReportedTimeUnits.MilliSeconds;
					sampleInterval = 10;
					ratioMode = Imports3.RatioMode.None;
					postTrigger = 10;
					autoStop = false;
					break;
			}

			Console.WriteLine("Waiting for trigger...Press a key to abort");
			_autoStop = false;

			do
			{
				retry = false;

				// Start streaming data capture
				status = Imports3.RunStreaming(_handle, ref sampleInterval, timeUnits, preTrigger, postTrigger - preTrigger, autoStop, downsampleRatio, ratioMode, tempBufferSize);

				if (status == StatusCodes.PICO_POWER_SUPPLY_CONNECTED || status == StatusCodes.PICO_POWER_SUPPLY_NOT_CONNECTED || status == StatusCodes.PICO_POWER_SUPPLY_UNDERVOLTAGE)
				{
					status = PowerSourceSwitch(_handle, status);
					retry = true;
				}
			}
			while (retry);

			Console.WriteLine(status != (short)StatusCodes.PICO_OK ? "StreamDataHandler:Imports3.RunStreaming Status = 0x{0,0:X6}" : "", status);

			Console.WriteLine("Streaming data...Press a key to abort");

			var sb = new StringBuilder();

			if (mode == Imports3.Mode.ANALOGUE)
			{
				sb.AppendFormat("For each of the {0} Channels, results shown are....", _channelCount);
				sb.AppendLine();
				sb.AppendLine("Maximum Aggregated value ADC Count & mV, Minimum Aggregated value ADC Count & mV");
				sb.AppendLine();

				// Build File Header
				string[] heading = { "Channel", "Max ADC", "Max mV", "Min ADC", "Min mV" };

				for (int i = 0; i < _channelCount; i++)
				{
					if (_channelSettings[i].enabled)
					{
						sb.AppendFormat("{0,10} {1,10} {2,10} {3,10} {4,10}",
										heading[0],
										heading[1],
										heading[2],
										heading[3],
										heading[4]);
					}
				}

				sb.AppendLine();
			}

			while (!_autoStop && !Console.KeyAvailable && !powerChange)
			{
				/* Poll until data is received. Until then, GetStreamingLatestValues won't call the callback */
				Thread.Sleep(0);

				_ready = false;

				status = Imports3.GetStreamingLatestValues(_handle, StreamingCallback, (System.IntPtr)mode);

				if (status == StatusCodes.PICO_POWER_SUPPLY_CONNECTED || status == StatusCodes.PICO_POWER_SUPPLY_NOT_CONNECTED || status == StatusCodes.PICO_POWER_SUPPLY_UNDERVOLTAGE)
				{
					if (status == (short)StatusCodes.PICO_POWER_SUPPLY_UNDERVOLTAGE)
					{
						status = PowerSourceSwitch(_handle, status);
					}
					else
					{
						Console.WriteLine("\n\nPower source changed.");
					}

					powerChange = true;
				}

				if (_ready && _sampleCount > 0) /* can be ready and have no data, if autoStop has fired */
				{
					if (_trig > 0)
					{
						triggeredAt = totalsamples + _trigAt;
					}

					totalsamples += (uint)_sampleCount;

					Console.Write("Collected {0,4} samples, index = {1,5} Total = {2,5}", _sampleCount, _startIndex, totalsamples);

					if (_trig > 0)
					{
						Console.Write("\tTrig at Index {0}", triggeredAt);
					}

					Console.WriteLine();

					for (uint i = _startIndex; i < (_startIndex + _sampleCount); i++)
					{
						if (mode == Imports3.Mode.ANALOGUE)
						{
							// Build File Body
							for (int ch = 0; ch < _channelCount * 2; ch += 2)
							{
								if (_channelSettings[ch / 2].enabled)
								{
									sb.AppendFormat("{0,10} {1,10} {2,10} {3,10} {4,10}",
													(char)('A' + (ch / 2)),
													appBuffersPinned[ch].Target[i],
													adc_to_mv(appBuffersPinned[ch].Target[i], (int)_channelSettings[(int)(Imports3.Channel.ChannelA + (ch / 2))].range),
													appBuffersPinned[ch + 1].Target[i],
													adc_to_mv(appBuffersPinned[ch + 1].Target[i], (int)_channelSettings[(int)(Imports3.Channel.ChannelA + (ch / 2))].range));
								}
							}
							sb.AppendLine();
						}

						if (mode == Imports3.Mode.DIGITAL)
						{
							short digiValue = (short)(0x00ff & appDigiBuffersPinned[1].Target[i]); // Mask lower 8-bits to get Port 1 data values
							digiValue <<= 8; // Shift by 8 bits
							digiValue |= (short)(0x00ff & appDigiBuffersPinned[0].Target[i]); // Mask Port 0 values to get lower 8 bits and apply bitwise inclusive OR to combine with Port 1 values 
							Console.Write("Index={0,4:D}: Value = 0x{1,4:X}  =  ", i, digiValue.ToString("X4"));

							// Display as binary data values
							// Port 1 values are the most significant bits (on the left), and Port 0 values are on the right
							for (short bit = 0; bit < 16; bit++)
							{
								Console.Write(((0x8000 >> bit) & digiValue) != 0 ? "1 " : "0 ");
							}

							Console.WriteLine();
						}

						if (mode == Imports3.Mode.AGGREGATED)
						{
							short digiValueOR = (short)(0x00ff & appDigiBuffersPinned[2].Target[i]);
							digiValueOR <<= 8;
							digiValueOR |= (short)(0x00ff & appDigiBuffersPinned[0].Target[i]);
							Console.WriteLine("\nIndex={0,4:D}: Bitwise  OR of last {1} values = 0x{2,4:X}  ", i, downsampleRatio, digiValueOR.ToString("X4"));

							short digiValueAND = (short)(0x00ff & appDigiBuffersPinned[3].Target[i]);
							digiValueAND <<= 8;
							digiValueAND |= (short)(0x00ff & appDigiBuffersPinned[1].Target[i]);
							Console.WriteLine("Index={0,4:D}: Bitwise AND of last {1} values = 0x{2,4:X}  ", i, downsampleRatio, digiValueAND.ToString("X4"));
						}
					}
				}
			}

			if (Console.KeyAvailable)
			{
				Console.ReadKey(true); // clear the key
			}

			Imports3.Stop(_handle);

			// Print contents to file
			using (TextWriter writer = new StreamWriter(StreamFile, false))
			{
				writer.Write(sb.ToString());
				writer.Close();
			}

			if (!_autoStop)
			{
				Console.WriteLine("\nData collection aborted.");
			}
		}


		/****************************************************************************
		* CollectStreamingImmediate
		*  this function demonstrates how to collect a stream of data
		*  from the unit (start collecting immediately)
		***************************************************************************/
		void CollectStreamingImmediate()
		{
			SetDefaults();

			Console.WriteLine("Collect streaming...");
			Console.WriteLine("Data is written to disk file (stream.txt)");
			Console.WriteLine("Press a key to start");
			WaitForKey();

			/* Trigger disabled	*/
			SetTrigger(null, 0, null, 0, null, null, 0, 0, 0);

			StreamDataHandler(0, Imports3.Mode.ANALOGUE);
		}


		/****************************************************************************
		* CollectStreamingTriggered
		*  this function demonstrates how to collect a stream of data
		*  from the unit (start collecting on trigger)
		***************************************************************************/
		void CollectStreamingTriggered()
		{
			short triggerVoltage = mv_to_adc(1000, (short)_channelSettings[(int)Imports3.Channel.ChannelA].range); // ChannelInfo stores ADC counts

			Imports3.TriggerChannelProperties[] sourceDetails = new Imports3.TriggerChannelProperties[] {
				new Imports3.TriggerChannelProperties( triggerVoltage,
														256 * 10,
														triggerVoltage,
														256 * 10,
														Imports3.Channel.ChannelA,
														Imports3.ThresholdMode.Level )};

			Imports3.TriggerConditions[] conditions = new Imports3.TriggerConditions[] {
				new Imports3.TriggerConditions(Imports3.TriggerState.True,
												Imports3.TriggerState.DontCare,
												Imports3.TriggerState.DontCare,
												Imports3.TriggerState.DontCare,
												Imports3.TriggerState.DontCare,
												Imports3.TriggerState.DontCare,
												Imports3.TriggerState.DontCare)};

			Imports3.ThresholdDirection[] directions = new Imports3.ThresholdDirection[]
											{ Imports3.ThresholdDirection.Rising,
												Imports3.ThresholdDirection.None,
												Imports3.ThresholdDirection.None,
												Imports3.ThresholdDirection.None,
												Imports3.ThresholdDirection.None,
												Imports3.ThresholdDirection.None };

			Console.WriteLine("Collect streaming triggered...");
			Console.WriteLine("Data is written to disk file (stream.txt)");
			Console.WriteLine("Press a key to start");
			WaitForKey();
			SetDefaults();

			/* Trigger enabled
			 * Rising edge
			 * Threshold = 1000mV */

			SetTrigger(sourceDetails, 1, conditions, 1, directions, null, 0, 0, 0);

			StreamDataHandler(100000, Imports3.Mode.ANALOGUE);
		}

		/****************************************************************************
		* DisplaySettings 
		* Displays information about the user configurable settings in this example
		***************************************************************************/
		void DisplaySettings()
		{
			int ch;
			int voltage;

			Console.WriteLine("\n\nReadings will be scaled in {0}", (_scaleVoltages) ? ("mV") : ("ADC counts"));

			for (ch = 0; ch < _channelCount; ch++)
			{
				if (!_channelSettings[ch].enabled)
				{
					Console.WriteLine("Channel {0} Voltage Range = Off", (char)('A' + ch));
				}
				else
				{
					voltage = inputRanges[(int)_channelSettings[ch].range];
					Console.Write("Channel {0} Voltage Range = ", (char)('A' + ch));

					if (voltage < 1000)
					{
						Console.WriteLine("{0}mV", voltage);
					}
					else
					{
						Console.WriteLine("{0}V", voltage / 1000);
					}
				}
			}
			Console.WriteLine();
		}


		/****************************************************************************
		* DigitalBlockImmediate
		* Collect a block of data from the digital ports with triggering disabled
		***************************************************************************/
		/*
        void DigitalBlockImmediate()
		{

			Console.WriteLine("Digital Block Immediate");
			Console.WriteLine("Press a key to start...");
			WaitForKey();

			SetTrigger(null, 0, null, 0, null, null, 0, 0, 0, null, 0);

			BlockDataHandler("First 10 readings\n", 0, Imports3.Mode.DIGITAL);
		}
        */
		/****************************************************************************
	  * DigitalBlockTriggered
	  * Collect a block of data from the digital ports with triggering disabled
	  ***************************************************************************/
		/*		void DigitalBlockTriggered()
				{
					Console.WriteLine("Digital Block Triggered");
					Console.WriteLine("Collect block of data when the trigger occurs...");
					Console.WriteLine("Digital Channel   0   --- Rising");
					Console.WriteLine("Digital Channel   4   --- High");
					Console.WriteLine("Other Digital Channels - Don't Care");

					Console.WriteLine("Press a key to start...");
					WaitForKey();


					Imports3.TriggerConditionsV2[] conditions = new Imports3.TriggerConditionsV2[] {
					  new Imports3.TriggerConditionsV2(Imports3.TriggerState.DontCare,                // Channel A
													Imports3.TriggerState.DontCare,                  // Channel B
													Imports3.TriggerState.DontCare,                  // Channel C
													Imports3.TriggerState.DontCare,                  // Channel D
													Imports3.TriggerState.DontCare,                  // external
													Imports3.TriggerState.DontCare,                  // aux
													Imports3.TriggerState.DontCare,                  // pwq3
													Imports3.TriggerState.True                       // digital
													)};


					Imports3.DigitalChannelDirections[] digitalDirections = new Imports3.DigitalChannelDirections[2];

					digitalDirections[0].DigiPort = Imports3.DigitalChannel.PS3000A_DIGITAL_CHANNEL_0;
					digitalDirections[0].DigiDirection = Imports3.DigitalDirection.PS3000A_DIGITAL_DIRECTION_RISING;

					digitalDirections[1].DigiPort = Imports3.DigitalChannel.PS3000A_DIGITAL_CHANNEL_4;
					digitalDirections[1].DigiDirection = Imports3.DigitalDirection.PS3000A_DIGITAL_DIRECTION_HIGH;

					SetTrigger(null, 0, conditions, 1, null, null, 0, 0, 0, digitalDirections, 2);

					BlockDataHandler("First 10 readings\n", 0, Imports3.Mode.DIGITAL);
				}

		*/
		/****************************************************************************
		* ANDAnalogueDigitalTriggered
		*  this function demonstrates how to combine Digital AND Analogue triggers
		*  to collect a block of data.
		****************************************************************************/
		/*	void ANDAnalogueDigitalTriggered()
			{
				Console.WriteLine("Analogue AND Digital Triggered Block");


				short triggerVoltage = mv_to_adc(1000, (short)_channelSettings[(int)Imports3.Channel.ChannelA].range); // ChannelInfo stores ADC counts
				Imports3.TriggerChannelProperties[] sourceDetails = new Imports3.TriggerChannelProperties[] {
					new Imports3.TriggerChannelProperties(triggerVoltage,
												 256*10,
												 triggerVoltage,
												 256*10,
												 Imports3.Channel.ChannelA,
												 Imports3.ThresholdMode.Level)};


				Imports3.TriggerConditionsV2[] conditions = new Imports3.TriggerConditionsV2[] {
					new Imports3.TriggerConditionsV2(Imports3.TriggerState.True,                      // Channel A
												Imports3.TriggerState.DontCare,                  // Channel B
												Imports3.TriggerState.DontCare,                  // Channel C
												Imports3.TriggerState.DontCare,                  // Channel D
												Imports3.TriggerState.DontCare,                  // external
												Imports3.TriggerState.DontCare,                  // aux
												Imports3.TriggerState.DontCare,                  // pwq3
												Imports3.TriggerState.True                       // digital
												)};

				Imports3.ThresholdDirection[] directions = new Imports3.ThresholdDirection[]
												{ Imports3.ThresholdDirection.Above,            // Channel A
												Imports3.ThresholdDirection.None,                // Channel B
												Imports3.ThresholdDirection.None,                // Channel C
												Imports3.ThresholdDirection.None,                // Channel D
												Imports3.ThresholdDirection.None,                // ext
												Imports3.ThresholdDirection.None };              // aux


				Imports3.DigitalChannelDirections[] digitalDirections = new Imports3.DigitalChannelDirections[2];

				digitalDirections[0].DigiPort = Imports3.DigitalChannel.PS3000A_DIGITAL_CHANNEL_0;
				digitalDirections[0].DigiDirection = Imports3.DigitalDirection.PS3000A_DIGITAL_DIRECTION_RISING;

				digitalDirections[1].DigiPort = Imports3.DigitalChannel.PS3000A_DIGITAL_CHANNEL_4;
				digitalDirections[1].DigiDirection = Imports3.DigitalDirection.PS3000A_DIGITAL_DIRECTION_HIGH;


				Console.Write("Collect a block of data when value is above {0}", (_scaleVoltages) ?
							  adc_to_mv(sourceDetails[0].ThresholdMajor, (int)_channelSettings[(int)Imports3.Channel.ChannelA].range) : sourceDetails[0].ThresholdMajor);
				Console.WriteLine("{0}", (_scaleVoltages) ? ("mV ") : ("ADC Counts "));
				Console.WriteLine("AND ");
				Console.WriteLine("Digital Channel  0   --- Rising");
				Console.WriteLine("Digital Channel  4   --- High");
				Console.WriteLine("Other Digital Channels - Don't Care");
				Console.WriteLine();
				Console.WriteLine("Press a key to start...");
				WaitForKey();

				SetDefaults();

				// Trigger enabled
				// Channel A
				// Rising edge
				// Threshold = 1000mV 
				// Digial
				// Ch0 Rising
				// Ch4 High 

				SetTrigger(sourceDetails, 1, conditions, 1, directions, null, 0, 0, 0, digitalDirections, 2);

				BlockDataHandler("Ten readings after trigger", 0, Imports3.Mode.MIXED);

				DisableAnalogue();
			}

		*/
		/****************************************************************************
		* ORAnalogueDigitalTriggered
		*  this function demonstrates how to trigger off Digital OR Analogue signals
		*  to collect a block of data.
		****************************************************************************/
		/*		void ORAnalogueDigitalTriggered()
				{
					Console.WriteLine("Analogue OR Digital Triggered Block");
					Console.WriteLine("Collect block of data when an Analogue OR Digital triggers occurs...");

					short triggerVoltage = mv_to_adc(1000, (short)_channelSettings[(int)Imports3.Channel.ChannelA].range); // ChannelInfo stores ADC counts

					Imports3.TriggerChannelProperties[] sourceDetails = new Imports3.TriggerChannelProperties[] {
						new Imports3.TriggerChannelProperties(triggerVoltage,
													 256*10,
													 triggerVoltage,
													 256*10,
													 Imports3.Channel.ChannelA,
													 Imports3.ThresholdMode.Level)};


					Imports3.TriggerConditionsV2[] conditions = new Imports3.TriggerConditionsV2[2];

					conditions[0].ChannelA = Imports3.TriggerState.True;
					conditions[0].ChannelB = Imports3.TriggerState.DontCare;
					conditions[0].ChannelC = Imports3.TriggerState.DontCare;
					conditions[0].ChannelD = Imports3.TriggerState.DontCare;
					conditions[0].External = Imports3.TriggerState.DontCare;
					conditions[0].Aux = Imports3.TriggerState.DontCare;
					conditions[0].Pwq3 = Imports3.TriggerState.DontCare;
					conditions[0].Digital = Imports3.TriggerState.DontCare;

					conditions[1].ChannelA = Imports3.TriggerState.DontCare;
					conditions[1].ChannelB = Imports3.TriggerState.DontCare;
					conditions[1].ChannelC = Imports3.TriggerState.DontCare;
					conditions[1].ChannelD = Imports3.TriggerState.DontCare;
					conditions[1].External = Imports3.TriggerState.DontCare;
					conditions[1].Aux = Imports3.TriggerState.DontCare;
					conditions[1].Pwq3 = Imports3.TriggerState.DontCare;
					conditions[1].Digital = Imports3.TriggerState.True;




					Imports3.ThresholdDirection[] directions = new Imports3.ThresholdDirection[]
													{ Imports3.ThresholdDirection.Rising,            // Channel A
													Imports3.ThresholdDirection.None,                // Channel B
													Imports3.ThresholdDirection.None,                // Channel C
													Imports3.ThresholdDirection.None,                // Channel D
													Imports3.ThresholdDirection.None,                // ext
													Imports3.ThresholdDirection.None };              // aux


					Imports3.DigitalChannelDirections[] digitalDirections = new Imports3.DigitalChannelDirections[2];

					digitalDirections[0].DigiPort = Imports3.DigitalChannel.PS3000A_DIGITAL_CHANNEL_0;
					digitalDirections[0].DigiDirection = Imports3.DigitalDirection.PS3000A_DIGITAL_DIRECTION_RISING;

					digitalDirections[1].DigiPort = Imports3.DigitalChannel.PS3000A_DIGITAL_CHANNEL_4;
					digitalDirections[1].DigiDirection = Imports3.DigitalDirection.PS3000A_DIGITAL_DIRECTION_HIGH;


					Console.Write("Collect a block of data when value rises past {0}", (_scaleVoltages) ?
								adc_to_mv(sourceDetails[0].ThresholdMajor, (int)_channelSettings[(int)Imports3.Channel.ChannelA].range) : sourceDetails[0].ThresholdMajor);
					Console.WriteLine("{0}", (_scaleVoltages) ? ("mV ") : ("ADC Counts "));
					Console.WriteLine("OR");
					Console.WriteLine("Digital Channel  0   --- Rising");
					Console.WriteLine("Digital Channel  4   --- High");
					Console.WriteLine("Other Digital Channels - Don't Care");
					Console.WriteLine();
					Console.WriteLine("Press a key to start...");
					WaitForKey();

					SetDefaults();

					// Trigger enabled
					 // Channel A
					 // Rising edge
					 // Threshold = 1000mV 
					 // Digial
					 // Ch0 Rising
					 // Ch4 High 

					SetTrigger(sourceDetails, 1, conditions, 2, directions, null, 0, 0, 0, digitalDirections, 2);

					BlockDataHandler("Ten readings after trigger", 0, Imports3.Mode.MIXED);

					DisableAnalogue();
				}
			*/
		/****************************************************************************
		* DigitalStreamingImmediate
		* Streams data from the digital ports with triggering disabled
		***************************************************************************/
		void DigitalStreamingImmediate()
		{
			Console.WriteLine("Digital Streaming Immediate....");
			Console.WriteLine("Press a key to start");
			WaitForKey();

			SetTrigger(null, 0, null, 0, null, null, 0, 0, 0, null, 0);

			StreamDataHandler(0, Imports3.Mode.DIGITAL);
		}

		/****************************************************************************
		* DigitalStreamingImmediate
		* Streams data from the digital ports with triggering disabled
	 ***************************************************************************/
		void DigitalStreamingAggregated()
		{
			Console.WriteLine("Digital Streaming with Aggregation....");
			Console.WriteLine("Press a key to start");
			WaitForKey();

			SetTrigger(null, 0, null, 0, null, null, 0, 0, 0, null, 0);

			StreamDataHandler(0, Imports3.Mode.AGGREGATED);
		}

		/****************************************************************************
		 * DigitalMenu - Only shown for the MSO scopes
		 ****************************************************************************/
		/*	public void DigitalMenu()
			{
				char ch;

				DisableAnalogue();                  // Disable the analogue ports
				SetDigitals();                      // Enable digital ports & set logic level

				ch = ' ';
				while (ch != 'X')
				{
					Console.WriteLine();
					Console.WriteLine("Digital Port Menu");
					Console.WriteLine();
					Console.WriteLine("B - Digital Block Immediate");
					Console.WriteLine("T - Digital Block Triggered");
					Console.WriteLine("A - Analogue 'AND' Digital Triggered Block");
					Console.WriteLine("O - Analogue 'OR'  Digital Triggered Block");
					Console.WriteLine("S - Digital Streaming Mode");
					Console.WriteLine("V - Digital Streaming Aggregated");
					Console.WriteLine("X - Return to previous menu");
					Console.WriteLine();
					Console.WriteLine("Operation:");

					ch = char.ToUpper(Console.ReadKey(true).KeyChar);

					Console.WriteLine("\n\n");
					switch (ch)
					{
						case 'B':
							DigitalBlockImmediate();
							break;

						case 'T':
							DigitalBlockTriggered();
							break;

						case 'A':
							ANDAnalogueDigitalTriggered();
							break;

						case 'O':
							ORAnalogueDigitalTriggered();
							break;

						case 'S':
							DigitalStreamingImmediate();
							break;

						case 'V':
							DigitalStreamingAggregated();
							break;
					}
				}
				DisableDigital();       // disable the digital ports when we're finished
			}
	*/
		/****************************************************************************
		* Run - show menu and call user selected options
		****************************************************************************/
		public void RunPico(ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond, ref CipherModule targetModule, long curr_trace, int rnd_cnt, ref TVLA tvla_class)
		{
			// setup devices
			GetDeviceInfo();
			//_timebase = 2;//change 250MS/s
			_timebase = 4;//change   62.5MS/s

			_channelSettings = new ChannelSettings3[MAX_CHANNELS];

			for (int i = 0; i < MAX_CHANNELS; i++)
			{
				_channelSettings[i].enabled = true;
				_channelSettings[i].DCcoupled = Imports3.Coupling.AC; //Imports3.Coupling.DC;
				_channelSettings[i].range = Imports3.Range.Range_500MV;
			}

			SetDefaults();
			SetVoltages();

			CollectBlockTriggered(ref HWOut, ref HWMask, inputtext, wait, ref elapsedMillisecond, ref targetModule, curr_trace, rnd_cnt, ref tvla_class);

			// main loop - read key and call routine
			/*
            char ch = ' ';
			while (ch != 'X')
			{
				DisplaySettings();

				Console.WriteLine("");
				Console.WriteLine("B - Immediate block              V - Set voltages");
				Console.WriteLine("T - Triggered block              I - Set timebase");
				Console.WriteLine("R - Rapid block                  A - ADC counts/mV");
				Console.WriteLine("S - Immediate Streaming");
				Console.WriteLine("W - Triggered Streaming");
				Console.WriteLine(_digitalPorts > 0 ? "D - Digital Ports Menu" : "");
				Console.WriteLine("                                 X - Exit");
				Console.WriteLine("Operation:");

				ch = char.ToUpper(Console.ReadKey(true).KeyChar);

				Console.WriteLine("\n");
				switch (ch)
				{
					case 'B':
						CollectBlockImmediate();
						break;

					case 'T':
						CollectBlockTriggered();
						break;

					case 'R':
						CollectRapidBlock();
						break;

					case 'S':
						CollectStreamingImmediate();
						break;

					case 'W':
						CollectStreamingTriggered();
						break;

					case 'V':
						SetVoltages();
						break;

					case 'I':
						SetTimebase();
						break;

					case 'A':
						_scaleVoltages = !_scaleVoltages;
						break;

					case 'D':
						if (_digitalPorts > 0)
						{
							DigitalMenu();
						}
						break;

					case 'X':
						// Handled by outer loop 
						break;

					default:
						Console.WriteLine("Invalid operation");
						break;
				}
			}*/
		}


		private PS3000ACSConsole(short handle)
		{
			_handle = handle;
		}



		/****************************************************************************
		* PowerSourceSwitch - Handle status errors connected with the power source
		****************************************************************************/
		static uint PowerSourceSwitch(short handle, uint status)
		{
			char ch;

			switch (status)
			{
				case StatusCodes.PICO_POWER_SUPPLY_NOT_CONNECTED:
					do
					{
						Console.WriteLine("5V Power Supply not connected\nDo you want to run using power from the USB lead? Y\\N");
						ch = 'Y';
						if (ch == 'Y')
						{
							Console.WriteLine("Powering the unit via USB");
							status = Imports3.ChangePowerSource(handle, status);
						}
					}
					while (ch != 'Y' && ch != 'N');
					Console.WriteLine(ch == 'N' ? "Please use the 5V power supply to power this unit" : "");
					break;

				case StatusCodes.PICO_POWER_SUPPLY_CONNECTED:
					Console.WriteLine("Using 5V power supply voltage");
					status = Imports3.ChangePowerSource(handle, status);
					break;

				case StatusCodes.PICO_POWER_SUPPLY_UNDERVOLTAGE:
					do
					{
						Console.WriteLine("");
						Console.WriteLine("\nUSB not supplying required voltage");
						Console.WriteLine("\nPlease plug in the +5V power supply,");
						Console.WriteLine("then hit a key to continue, or Esc to exit...");
						ch = Console.ReadKey().KeyChar;

						if (ch == 0x1B)
						{
							Environment.Exit(0);
						}
						status = PowerSourceSwitch(handle, StatusCodes.PICO_POWER_SUPPLY_CONNECTED);
					}
					while (status == (short)StatusCodes.PICO_POWER_SUPPLY_REQUEST_INVALID);
					break;
			}
			return status;
		}

		public void DeviceClose()
		{
			Imports3.CloseUnit(device_handle);
		}
		public void deviceOpen()
		{
			Console.WriteLine("PicoScope 3000 Series (ps3000a) Driver C# Example Program");
			Console.WriteLine("Version 1.1\n\n");
			Console.WriteLine("Enumerating devices...\n");

			short count = 0;
			short serialsLength = 40;
			StringBuilder serials = new StringBuilder(serialsLength);

			uint status = Imports3.EnumerateUnits(out count, serials, ref serialsLength);

			if (status != StatusCodes.PICO_OK)
			{
				Console.WriteLine("No devices found.\n");
				Console.WriteLine("Error code : {0}", status);
				Console.WriteLine("Press any key to exit.\n");
				//	WaitForKey();
				//Environment.Exit(0);
			}
			else
			{
				if (count == 1)
				{
					Console.WriteLine("Found {0} device:", count);
				}
				else
				{
					Console.WriteLine("Found {0} devices", count);
				}

				Console.WriteLine("Serial(s) {0}", serials);

			}

			Console.WriteLine("\nOpening the device...");


			short handle1 = 1;

			status = Imports3.OpenUnit(out handle1, null);
			Thread.Sleep(10000);
			device_handle = handle1;
			if (status != StatusCodes.PICO_OK)
			{
				status = PowerSourceSwitch(handle1, status);

				if (status == StatusCodes.PICO_POWER_SUPPLY_UNDERVOLTAGE)
				{
					status = PowerSourceSwitch(handle1, status);
				}
				else if (status == StatusCodes.PICO_USB3_0_DEVICE_NON_USB3_0_PORT)
				{
					status = PowerSourceSwitch(handle1, StatusCodes.PICO_POWER_SUPPLY_NOT_CONNECTED);
				}
				else
				{
					// Do nothing
				}
			}


			if (status != StatusCodes.PICO_OK)
			{
				Console.WriteLine("Unable to open device");
				Console.WriteLine("Error code : 0x{0}", Convert.ToString(status, 16));
				//    WaitForKey();
			}
			else
			{
				Console.WriteLine("Handle: {0}", handle1);
			}

			//return status;

		}

		public void MainPico(ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond, ref CipherModule targetModule, long curr_trace, int rnd_cnt, ref TVLA tvla_class)
		{


			short handle = 16384;
			//tvla = new TVLA(BUFFER_SIZE);
			//tvla = tvla_class.ShallowCopy();

			//if (deviceOpen(out handle) == 0)
			//{
			//Console.WriteLine("Device opened successfully\n");

			PS3000ACSConsole consoleExample = new PS3000ACSConsole(handle);
			consoleExample.RunPico(ref HWOut, ref HWMask, inputtext, wait, ref elapsedMillisecond, ref targetModule, curr_trace, rnd_cnt, ref tvla_class);
			//tvla_class = tvla.ShallowCopy();



			//Imports3.CloseUnit(handle);
			//}
		}
	}
}
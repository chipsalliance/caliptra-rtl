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
 *   This is a program that demonstrates how to use the
 *   PS2000 driver using .NET
 *
 * Examples:
 *    Collect a block of samples immediately
 *    Collect a block of samples when a trigger event occurs
 *
 **************************************************************************/

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Threading;
using System.Runtime.InteropServices;

namespace SAKURA
{
    struct ChannelSettings
    {
        public short DCcoupled;
        public Imports.Range range;
        public short enabled;
        public short[] values;
    }

    class Pwq
    {
        public Imports.PwqConditions[] conditions;
        public short nConditions;
        public Imports.ThresholdDirection direction;
        public uint lower;
        public uint upper;
        public Imports.PulseWidthType type;

        public Pwq(Imports.PwqConditions[] conditions,
            short nConditions,
            Imports.ThresholdDirection direction,
            uint lower, uint upper,
            Imports.PulseWidthType type)
        {
            this.conditions = conditions;
            this.nConditions = nConditions;
            this.direction = direction;
            this.lower = lower;
            this.upper = upper;
            this.type = type;
        }
    }



    class PS2000ConsoleExample
    {
        public PS2000ConsoleExample()
        {
            //mlList = new List<MLArray>();
        }
        private readonly short _handle;
        public const int BUFFER_SIZE = 1024;
        public const int SINGLE_SCOPE = 1;
        public const int DUAL_SCOPE = 2;
        public const int QUAD_SCOPE = 4;
        public const int MAX_CHANNELS = 4;
        private CipherModule sakuraRun;

        public void Open(uint index)
        {
            sakuraRun = new CipherModule(index);
        }

        public void Close()
        {
            sakuraRun.Dispose();
        }

        short _timebase = 8;
        short _oversample = 0;
        bool _hasFastStreaming = false;

        uint _totalSampleCount = 0;
        uint _nValues = 0;
        bool _autoStop;
        short _trig;
        uint _trigAt;
        bool _appBufferFull;
        public short[][] _appBuffer = new short[2][];
        private uint _OverViewBufferSize = 150000;
        private uint _MaxSamples = 1000000;

        ushort[] inputRanges = { 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000 };
        private ChannelSettings[] _channelSettings;
        private int _channelCount = 2;
        private Imports.Range _firstRange;
        private Imports.Range _lastRange;
        PinnedArray<short>[] Pinned = new PinnedArray<short>[4];
        private string BlockFile = "block.txt";
        private string StreamFile = "stream.txt";
        
        /****************************************************************************
         * StreamingCallback
         * used by data streaming collection calls, on receipt of data.
         * used to set global flags etc checked by user routines
         ****************************************************************************/
        unsafe void StreamingCallback(short** overviewBuffers,
                                          short overFlow,
                                          uint triggeredAt,
                                          short triggered,
                                          short auto_stop,
                                          uint nValues)
        {
            // used for streaming
            _autoStop = auto_stop != 0;

            // flags to show if & where a trigger has occurred
            _trig = triggered;
            _trigAt = triggeredAt;
            _nValues = nValues;

            if (nValues > 0 && !_appBufferFull)
            {
                    try
                    {
                        for (int i = (int)_totalSampleCount; i < nValues + _totalSampleCount; i++)
                        {
                            for (int channel = 0; channel < _channelCount; channel++)
                            {
                                _appBuffer[channel][i] = overviewBuffers[channel * 2][i - _totalSampleCount]; //Only copying max data from 
                            }
                        }
                    }
                    catch (Exception) //if trying to place data 
                    {
                        _appBufferFull = true;
                        Console.WriteLine("Appbuffer full collection cancelled");
                    }                 
            }            
            _totalSampleCount += nValues;
        }

        /****************************************************************************
         * SetDefaults - restore default settings
         ****************************************************************************/
        void SetDefaults()
        {
            for (int i = 0; i < _channelCount; i++) // set channels to most recent settings
            {
                Imports.SetChannel(_handle, (Imports.Channel)(i),
                                   _channelSettings[i].enabled,
                                   _channelSettings[i].DCcoupled,
                                   _channelSettings[i].range);
            }

        }

        /****************************************************************************
         * adc_to_mv
         *
         * Convert an 16-bit ADC count into millivolts
         ****************************************************************************/
        int adc_to_mv(int raw, int ch)
        {
            return (raw * inputRanges[ch]) / Imports.MaxValue;
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
            return (short)((mv * Imports.MaxValue) / inputRanges[ch]);
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
        void BlockDataHandler(string text, int offset, ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond, ref CipherModule targetModule, long curr_trace)
        {
            int sampleCount = BUFFER_SIZE;
            short timeunit = 0;
            int timeIndisposed;



            for (int i = 0; i < _channelCount; i++)
            {
                short[] buffer = new short[sampleCount];
                Pinned[i] = new PinnedArray<short>(buffer);
            }

            /* find the maximum number of samples, the time interval (in timeUnits),
                * the most suitable time units, and the maximum _oversample at the current _timebase*/
            int timeInterval = 0;
            int maxSamples;
            while ((Imports.GetTimebase(_handle, _timebase, sampleCount, out timeInterval, out timeunit, _oversample, out maxSamples)) == 0)
            {
                Console.WriteLine("Selected timebase {0} could not be used\n", _timebase);
                _timebase++;

            }
            //Console.WriteLine("Timebase: {0}\toversample:{1}\n", _timebase, _oversample);

            /* Start it collecting, then wait for completion*/

            Imports.RunBlock(_handle, sampleCount, _timebase, _oversample, out timeIndisposed);

            //Console.WriteLine("Waiting for data...Press a key to abort");
            short ready = 0;
            while ((ready = Imports.Isready(_handle)) == 0)
            {
                //Thread.Sleep(50);
                targetModule.Run(ref HWOut, inputtext, wait, ref elapsedMillisecond);
                Thread.Sleep(1); 
            }


            if (ready > 0)
            {

                short overflow;
                string fname = "";
                //double[][] trace = new double[10000][];

                Imports.GetValues(_handle, Pinned[0], null, null, null, out overflow, sampleCount);

                sampleCount = Math.Min(sampleCount, BUFFER_SIZE);
                if (curr_trace % 2 == 0)
                    fname = "fixed_block_prngon_ps2000_12_19.csv";
                else
                    fname = "random_block_prngon_ps2000_12_19.csv";
                using (StreamWriter writer = File.AppendText(fname))
                {
                    for (int i = 0; i < sampleCount; i++)
                    {
                        writer.Write(Pinned[0].Target[i]+",");
                    }
                    writer.WriteLine();
                    writer.Close();
                }
            }
            else
            {
                Console.WriteLine("data collection aborted");
            }

            Imports.Stop(_handle);
        }

        /****************************************************************************
        *  SetTrigger
        *  this function sets all the required trigger parameters, and calls the 
        *  triggering functions
        ****************************************************************************/
        short SetTrigger(Imports.TriggerChannelProperties[] channelProperties,
                        short nChannelProperties,
                        Imports.TriggerConditions[] triggerConditions,
                        short nTriggerConditions,
                        Imports.ThresholdDirection[] directions,
                        Pwq pwq,
                        uint delay,
                        int autoTriggerMs)
        {
            short status;

            if ((status = Imports.SetTriggerChannelProperties(_handle, channelProperties, nChannelProperties, autoTriggerMs)) == 0)
            {
                return status;
            }

            if ((status = Imports.SetTriggerChannelConditions(_handle, triggerConditions, nTriggerConditions)) == 0)
            {
                return status;
            }

            if (directions == null) directions = new Imports.ThresholdDirection[] { Imports.ThresholdDirection.None, 
        Imports.ThresholdDirection.None, Imports.ThresholdDirection.None, Imports.ThresholdDirection.None, 
        Imports.ThresholdDirection.None, Imports.ThresholdDirection.None};

            if ((status = Imports.SetTriggerChannelDirections(_handle,
                                                              directions[(int)Imports.Channel.ChannelA],
                                                              directions[(int)Imports.Channel.ChannelB],
                                                              directions[(int)Imports.Channel.ChannelC],
                                                              directions[(int)Imports.Channel.ChannelD],
                                                              directions[(int)Imports.Channel.External])) == 0)
            {
                return status;
            }

            if ((status = Imports.SetTriggerDelay(_handle, delay, 0)) == 0)
            {
                return status;
            }

            if (pwq == null) pwq = new Pwq(null, 0, Imports.ThresholdDirection.None, 0, 0, Imports.PulseWidthType.None);

            status = Imports.SetPulseWidthQualifier(_handle, pwq.conditions,
                                                    pwq.nConditions, pwq.direction,
                                                    pwq.lower, pwq.upper, pwq.type);


            return status;
        }

        /****************************************************************************
       *  CollectBlockTriggered
       *  this function demonstrates how to collect a single block of data from the
       *  unit, when a trigger event occurs.
       ****************************************************************************/
        void CollectBlockTriggered(ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond, ref CipherModule targetModule,long curr_trace)
        {
            short triggerVoltage = mv_to_adc(150, (short)_channelSettings[(int)Imports.Channel.ChannelB].range); // ChannelInfo stores ADC counts
            Imports.TriggerChannelProperties[] sourceDetails = new Imports.TriggerChannelProperties[] {
                new Imports.TriggerChannelProperties(
                    triggerVoltage,
                    triggerVoltage,
                    256*10,
                    Imports.Channel.ChannelB,
                    Imports.ThresholdMode.Level
                    )
            };

            Imports.TriggerConditions[] conditions = new Imports.TriggerConditions[] 
            {
                new Imports.TriggerConditions(
                    Imports.TriggerState.DontCare,                      // Channel A
                    Imports.TriggerState.True,                  // Channel B
                    Imports.TriggerState.DontCare,                  // Channel C
                    Imports.TriggerState.DontCare,                  // Channel C
                    Imports.TriggerState.DontCare,                  // external
                    Imports.TriggerState.DontCare                  // pwq
                    )
            };

            Imports.ThresholdDirection[] directions = new Imports.ThresholdDirection[]
            {
                Imports.ThresholdDirection.None,            // Channel A
                Imports.ThresholdDirection.Rising,                // Channel B
                Imports.ThresholdDirection.None,                // Channel C
                Imports.ThresholdDirection.None,                // Channel D
                Imports.ThresholdDirection.None
            };              

            SetDefaults();

            /* Trigger enabled
             * Rising edge
             * Threshold = 150mV */
            SetTrigger(sourceDetails, 1, conditions, 1, directions, null, 0, 0);

            BlockDataHandler("", 0, ref HWOut, ref HWMask, inputtext, wait, ref elapsedMillisecond, ref targetModule, curr_trace);
        }

        /****************************************************************************
        * Initialise unit' structure with Variant specific defaults
        ****************************************************************************/
        void GetDeviceInfo()
        {
            _firstRange = Imports.Range.Range_50MV;
            _lastRange = Imports.Range.Range_20V;
            _channelCount = DUAL_SCOPE;

            string[] description = {
                           "Driver Version    ",
                           "USB Version       ",
                           "Hardware Version  ",
                           "Variant Info      ",
                           "Serial            ",
                           "Cal Date          ",
                           "Kernel Ver        ",
                           "Digital Hardware  ",
                           "Analogue Hardware "
                         };
            System.Text.StringBuilder line = new System.Text.StringBuilder(80);

            if (_handle >= 0)
            {

                for (short i = 0; i < 9; i++)
                {
                    Imports.GetUnitInfo(_handle, line, 80, i);
                    if (i == 3)
                    {

                        if ((_channelCount = Convert.ToInt16(line[1]) - 48) == 1)
                        {
                            _firstRange = Imports.Range.Range_100MV;
                        }
                        else if ((Convert.ToInt16(line[3]) - 48) >= 3)
                        {
                            _hasFastStreaming = true;
                        }

                    }
                }
            }
        }

        /****************************************************************************
         * Select input voltage ranges for channels A and B
         ****************************************************************************/
        void SetVoltages()
        {
            for (int ch = 0; ch < _channelCount; ch++)
            {
                uint range = 8;
                //set channel 0 to 100mV and channel 5 to 500mV
                if (ch == 0)
                {
                    range = 6;
                    _channelSettings[ch].enabled = 1;
                }
                else
                {
                    range = 6;
                    _channelSettings[ch].enabled = 1;
                }
                _channelSettings[ch].range = (Imports.Range)range;                
            }
            //SetDefaults();  // Set defaults now, so that if all but 1 channels get switched off, timebase updates to timebase 0 will work
        }

        /****************************************************************************
         *
         * Select _timebase, set _oversample to on and time units as nano seconds
         *
         ****************************************************************************/
        void SetTimebase()
        {
            int timeInterval;
            int maxSamples;
            short timeunit;
            bool valid = false;

            Console.WriteLine("Specify timebase");

            do
            {
                try
                {
                    _timebase = short.Parse(Console.ReadLine());
                    valid = true;
                }
                catch (FormatException)
                {
                    valid = false;
                    Console.WriteLine("\nEnter numeric values only");
                }

            } while (!valid);

            while ((Imports.GetTimebase(_handle, _timebase, BUFFER_SIZE, out timeInterval, out timeunit, _oversample, out maxSamples)) == 0)
            {
                Console.WriteLine("Selected timebase {0} could not be used", _timebase);
                _timebase++;
            }

            Console.WriteLine("Timebase {0} - {1} ns", _timebase, timeInterval);
            _oversample = 1;
        }



        /****************************************************************************
        * DisplaySettings 
        * Displays information about the user configurable settings in this example
        ***************************************************************************/
        void DisplaySettings()
        {
            int ch;
            int voltage;

            for (ch = 0; ch < _channelCount; ch++)
            {
                if (_channelSettings[ch].enabled == 0)
                    Console.WriteLine("Channel {0} Voltage Range = Off", (char)('A' + ch));
                else
                {
                    voltage = inputRanges[(int)_channelSettings[ch].range];
                    //Console.Write("Channel {0} Voltage Range = ", (char)('A' + ch));

                    /*
                    if (voltage < 1000)
                        Console.WriteLine("{0}mV", voltage);
                    else
                        Console.WriteLine("{0}V", voltage / 1000);
                    */
                }
            }
            //Console.WriteLine();
        }




        /****************************************************************************
         * Run - show menu and call user selected options
         ****************************************************************************/
        public void RunPico(ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond, ref CipherModule targetModule, long curr_trace)
        {
            // setup devices
            GetDeviceInfo();
            _timebase = 2;

            _channelSettings = new ChannelSettings[MAX_CHANNELS];

            for (int i = 0; i < _channelCount; i++)
            {
                _channelSettings[i].enabled = 1;
                _channelSettings[i].DCcoupled = 0; //DC coupled
                _channelSettings[i].range = Imports.Range.Range_5V;
            }

            SetDefaults();
            SetVoltages();
            CollectBlockTriggered(ref HWOut, ref HWMask, inputtext, wait, ref elapsedMillisecond, ref targetModule, curr_trace);
        }


        private PS2000ConsoleExample(short handle)
        {
            _handle = handle;
        }

        public void OpenPico()
        {
            Imports.OpenUnit();
            Thread.Sleep(10000);
        }

        public void ClosePico()
        {
            Imports.CloseUnit(1);
        }

        public void MainPico(ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond, ref CipherModule targetModule,long curr_trace)
        {
            short handle = 1;
            //Console.WriteLine("Device opened successfully\n");
            PS2000ConsoleExample consoleExample = new PS2000ConsoleExample(handle);
            consoleExample.RunPico(ref HWOut, ref HWMask, inputtext, wait, ref elapsedMillisecond, ref targetModule, curr_trace);            
            //Imports.CloseUnit(handle);
            
        }
    }
}


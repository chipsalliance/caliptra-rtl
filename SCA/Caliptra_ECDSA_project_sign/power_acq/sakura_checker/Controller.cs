using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.ComponentModel;
using System.IO;
using SAKURA_Checker;

namespace SAKURA
{
    class Controller
    {
        private BackgroundWorker worker;
        public static CipherModule targetModule;
        private AES pcModule;
        private PS2000ConsoleExample picoscope;
        private PS3000ACSConsole picoscope3;
        bool wavedump;
        uint PS;
        public TVLA tvla;

        public Controller()
        {
            worker = new BackgroundWorker();
            worker.WorkerReportsProgress = true;
            worker.WorkerSupportsCancellation = true;
            worker.DoWork += new DoWorkEventHandler(worker_DoWork);
            pcModule = new AES();
            
            picoscope = new PS2000ConsoleExample();
            picoscope3 = new PS3000ACSConsole();
            tvla = new TVLA(750);
            wavedump = false;
            wavedump = true;
            PS = 3;
        }

        public void Open(uint index)
        {
            targetModule = new CipherModule(index);
        }

        public void Close()
        {
            targetModule.Dispose();
        }

        public void AddCompletedEventHandler(RunWorkerCompletedEventHandler handler)
        {
            worker.RunWorkerCompleted += handler;
        }

        public void AddProgressChangedEventHandler(ProgressChangedEventHandler handler)
        {
            worker.ProgressChanged += handler;
        }

        public void Run(ControllerArgs args)
        {
            worker.RunWorkerAsync((object)args);
        }

        public void Cancel()
        {
            worker.CancelAsync();
        }

        private void worker_DoWork(object sender, DoWorkEventArgs e)
        {
            ControllerArgs args = (ControllerArgs)e.Argument;
            ControllerArgs res = args.Clone();
            int progress = 0;

            e.Cancel = false;
            if (wavedump)
            {
                if (PS==2)
                    picoscope.OpenPico();
                else
                    picoscope3.deviceOpen();
            }


            // initialize
            res.last = false;
            res.error = false;
            res.current_trace = 0;
            int trace_order;
            pcModule.SetKey(res.key);
            //0xf98297828e4c31684cc6345c11942ba8eac0022c12adf142ab3fd22828a8dbfc95c1a0cc64ad4b00b81f177b689417
            byte[] my_key = new byte[48] {0x0,0xf9,0x82,0x97,0x82,0x8e,0x4c,0x31,0x68,0x4c,0xc6,0x34,0x5c,0x11,0x94,0x2b,0xa8,0xea,0xc0,0x2,0x2c,0x12,0xad,0xf1,
                                            0x42,0xab,0x3f,0xd2,0x28,0x28,0xa8,0xdb,0xfc,0x95,0xc1,0xa0,0xcc,0x64,0xad,0x4b,0x0,0xb8,0x1f,0x17,0x7b,0x68,0x94,0x17};
            targetModule.Reset();
            targetModule.SetModeEncrypt(true);
            targetModule.SetKey(my_key);
            worker.ReportProgress(0, (object)res);
            string image_file2 = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project_sign/MM_vector.csv";
            string trace_order_file = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project_sign/data/trace_order.csv";
            //0xa81bf2ace3f2419f8b51dda340755ec84a8b4545a95554145d6ac79f87471165c253ef623c374e602661b723ffb5b685
            byte[] fixed_input = new byte[48] {0xa8,0x1b,0xf2,0xac,0xe3,0xf2,0x41,0x9f,0x8b,0x51,0xdd,0xa3,0x40,0x75,0x5e,0xc8,0x4a,0x8b,0x45,0x45,0xa9,0x55,0x54,0x14,
0x5d,0x6a,0xc7,0x9f,0x87,0x47,0x11,0x65,0xc2,0x53,0xef,0x62,0x3c,0x37,0x4e,0x60,0x26,0x61,0xb7,0x23,0xff,0xb5,0xb6,0x85};
            // 0x225a8eebbdd5b0633b5f42983b6a58fb62839b44e83377aba2f63652f833eb37853d13e5b5fd498e1e6a35df727a5c99
            byte[] fixed_output = new byte[48] {0x3e,0xd2,0xbe,0xba,0x83,0xbf,0xca,0xbf,0x12,0xd8,0xc3,0x93,0x76,0x24,0x98,0xf1,0xbf,0x92,0xf5,0xfa,0x7f,0x36,0x18,0xf3,
0x47,0xd7,0x8f,0xbc,0x04,0xd2,0x06,0x64,0x30,0xeb,0xd3,0xf6,0x2b,0x6c,0x31,0x1b,0x90,0x35,0x06,0x8d,0xc2,0x90,0x7c,0x19};
            int rnd_cnt = 0;
            res.plaintext = new byte[48];
            res.answer = new byte[48];

            using (StreamReader sr = new StreamReader(image_file2))
            {
                string currentLine;
                while (res.endless || res.current_trace < res.traces)
                {
                    res.ciphertext = null;
                    res.mask = null;
                    res.difference = null;
                    res.current_trace++;
                    targetModule.SetKey(my_key);

                    trace_order = res.rand.generateRndOrder();
                    using (StreamWriter writer = File.AppendText(trace_order_file))
                    {
                        writer.Write(trace_order.ToString() + "\n");
                        writer.Flush();
                    }

                    if (!res.endless)
                    {
                        progress = (int)(100 * res.current_trace / res.traces);
                    }

                    if (res.randomGeneration)
                    {
                        if (trace_order == 1 && ((currentLine = sr.ReadLine()) != null))
                        {
                            String[] numbers = currentLine.Split(',');
                            for (int i = 0; i < 96; i++)
                            {
                                if (i < 48)
                                    res.plaintext[i] = (byte)Convert.ToInt32(numbers[i]);
                                else
                                    res.answer[i - 48] = (byte)Convert.ToInt32(numbers[i]);
                            }

                        }
                        else
                        {
                            for (int i = 0; i < fixed_input.Length; i++)
                            {
                                res.plaintext[i] = fixed_input[i];
                            }
                            for (int i = 0; i < fixed_output.Length; i++)
                            {
                                res.answer[i] = fixed_output[i];
                            }
                        }

                    }

                    worker.ReportProgress(progress, (object)res);

                    if (wavedump)
                    {
                        if (PS == 2)
                            picoscope.MainPico(ref res.ciphertext, ref res.mask, res.plaintext, res.wait, ref res.elapsed, ref targetModule, trace_order);
                        else
                            picoscope3.MainPico(ref res.ciphertext, ref res.mask, res.plaintext, res.wait, ref res.elapsed, ref targetModule, trace_order, rnd_cnt, ref tvla);

                    }
                    else
                    {
                        targetModule.Run(ref res.ciphertext, res.plaintext, res.wait, ref res.elapsed);
                    }
                    res.diff = false;
                    if (trace_order == 0)
                        res.diff = Utils.differenceByteArray(ref res.difference, res.answer, res.ciphertext);

                    worker.ReportProgress(progress, (object)res);

                    if (res.diff)
                    {
                        res.error = true;
                        if (!res.continueIfError)
                        {
                            break;
                        }
                    }

                    if (worker.CancellationPending)
                    {
                        e.Cancel = true;
                        break;
                    }

                    if (res.single)
                    {
                        progress = 100;
                        break;
                    }
                    targetModule.Reset();

                    rnd_cnt++;

                }
            }

            res.last = true;
            worker.ReportProgress(progress, (object)res);
            e.Result = (object)res;
            picoscope.ClosePico();
        }
    }

    public struct ControllerArgs
    {
        public bool single;
        public long traces;
        public bool endless;
        public long current_trace;
        public byte[] key;
        public byte[] plaintext;
        public bool randomGeneration;
        public int wait;
        public byte[] ciphertext;
        public byte[] mask;
        public byte[] answer;
        public byte[] difference;
        public bool diff;
        public bool continueIfError;
        public bool enableMasking;
        public bool error;
        public double elapsed;
        public RandGen rand;
        public bool last;
        public static int textnum;

        public ControllerArgs Clone()
        {
            return (ControllerArgs)MemberwiseClone();
        }
    }
}
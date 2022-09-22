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
            tvla = new TVLA(264000);
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
            targetModule.Reset();
            targetModule.SetModeEncrypt(true);
            targetModule.SetKey(res.key);
            worker.ReportProgress(0, (object)res);
            string image_file = "plaintext.csv";
            string image_file2 = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project/data/ECDSA_Scalar_Vectors.csv";
            string trace_order_file = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project/data/trace_order.csv";
            byte[] fixed_input = new byte[52] {0xa8, 0x58, 0xa0, 0x64,
 0x73, 0xdc, 0x79, 0x55,
 0x05, 0x66, 0x86, 0xa4,
 0x2f, 0x20, 0xb6, 0xbf,
 0x6d, 0x99, 0xcf, 0x36,
 0x9e, 0x6d, 0x3b, 0xfc,
 0x65, 0x57, 0x1c, 0x48,
 0x5d, 0xfd, 0x8a, 0x79,
 0xfd, 0x12, 0x60, 0x71,
 0x44, 0xdd, 0x14, 0xe9,
 0x71, 0x66, 0x4a, 0xf2,
 0xd2, 0x73, 0x35, 0xea,
 0x00, 0x00, 0x00, 0x01};
            byte [] fixed_output = new byte[96] {0x7a, 0x8b, 0x8c, 0x66,
 0x7d, 0x01, 0x6f, 0xe2,
 0xd1, 0xfd, 0x77, 0x42,
 0x7e, 0x6a, 0x8e, 0xa9,
 0x3d, 0x62, 0x79, 0x54,
 0x0e, 0xe6, 0xb0, 0x40,
 0xf8, 0x20, 0x54, 0xd1,
 0xe0, 0x57, 0xab, 0x62,
 0x74, 0x41, 0x7d, 0x05,
 0xda, 0x4c, 0x6d, 0x90,
 0x78, 0x76, 0x34, 0xd5,
 0x79, 0x31, 0x48, 0xf1,
 0xa1, 0xa1, 0xd1, 0x28,
 0xba, 0xce, 0xd2, 0x14,
 0x23, 0xde, 0x3b, 0x67,
 0x8f, 0x7a, 0x68, 0x59,
 0xb2, 0x9e, 0x42, 0x36,
 0x6b, 0x8f, 0x39, 0x8b,
 0x94, 0xf4, 0xc3, 0xf0,
 0xc9, 0x47, 0x39, 0x2e,
 0x4c, 0xd4, 0x05, 0x04,
 0xf4, 0x80, 0xf4, 0xfb,
 0x33, 0x1d, 0x23, 0xe6,
 0xc6, 0xc4, 0x12, 0x94};
            int rnd_cnt = 0;
            res.plaintext = new byte[52];
            res.answer = new byte[96];
            using (StreamReader sr = new StreamReader(image_file2))
            {
                string currentLine;
                while ((res.endless || res.current_trace < res.traces))
                {
                    res.ciphertext = null;
                    res.mask = null;
                    res.difference = null;
                    res.current_trace++;

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
                            for (int i = 0; i < 148; i++)
                            {
                                if (i < 52)
                                    res.plaintext[i] = (byte)Convert.ToInt32(numbers[i]);
                                else
                                    res.answer[i-52] = (byte)Convert.ToInt32(numbers[i]);
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
                        for (int i = 0; i < 96; i++)
                        {
                            if (i % 2 == 1)
                                res.answer[i] = 0;
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
                        //targetModule.Run(ref res.ciphertext, res.plaintext, res.wait, ref res.elapsed);
                        targetModule.Run(ref res.ciphertext, res.plaintext, res.wait, ref res.elapsed);
                    }
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
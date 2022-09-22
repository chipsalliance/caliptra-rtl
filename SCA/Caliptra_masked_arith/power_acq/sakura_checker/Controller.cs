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
            tvla = new TVLA(1750);
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
            
            byte[] my_key = new byte[16] {0x0,0xf9,0x82,0x97,0x82,0x8e,0x4c,0x31,0x68,0x4c,0xc6, 0x4c, 0x31, 0x68, 0x4c, 0xc6 };
            targetModule.Reset();
            targetModule.SetModeEncrypt(true);
            targetModule.SetKey(my_key);
            worker.ReportProgress(0, (object)res);
            string image_file2 = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_masked_arith/MM_vector.csv";
            string trace_order_file = "C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_masked_arith/data/trace_order.csv";


            byte[] fixed_input = new byte[2] { 0x0, 0xf9};
            int rnd_cnt = 0;
            res.plaintext = new byte[16];
            res.answer = new byte[4];
            string currentLine;
            while (res.endless || res.current_trace < res.traces)
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
                res.plaintext = res.rand.generatePlaintext();
                

                if (res.randomGeneration)
                {
                    if (trace_order == 1)
                    {
                        for (int i = 0; i < 8; i++)
                        {
                            if (i != 6 && i != 7)
                                res.plaintext[i] = my_key[i];
                        }

                    }
                    else
                    {
                        for (int i = 0; i < 8; i++)
                        {
                            res.plaintext[i] = my_key[i];
                        }
                    }

                }
                targetModule.constraint(ref res.plaintext);

                UInt32 S_unprot = targetModule.signing(res.plaintext);

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

                UInt32 S_prot = targetModule.mergeResult(res.ciphertext);

                res.diff = Utils.differenceTwoS(ref res.difference, S_unprot, S_prot);

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
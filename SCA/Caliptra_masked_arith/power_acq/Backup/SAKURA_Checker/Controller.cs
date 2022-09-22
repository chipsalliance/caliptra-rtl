using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.ComponentModel;
using System.IO;
using System.Text;

namespace SAKURA
{
    class Controller
    {
        private BackgroundWorker worker;
        private CipherModule targetModule;
        private AES pcModule;

        public Controller()
        {
            worker = new BackgroundWorker();
            worker.WorkerReportsProgress = true;
            worker.WorkerSupportsCancellation = true;
            worker.DoWork += new DoWorkEventHandler(worker_DoWork);
            pcModule = new AES();
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

            


            // initialize
            res.last = false;
            res.error = false;
            res.current_trace = 0;
            pcModule.SetKey(res.key);
            targetModule.Reset();
            targetModule.SetModeEncrypt(true);
            //targetModule.SetKey(res.key, res.enableMasking);
            worker.ReportProgress(0, (object)res);

            ControllerArgs.textnum = ControllerArgs.textnum + 1;
            string FileName = @"C:\Lattice\UT Austin\Sakura-G-Masked\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\test.m";

            using (StreamWriter writer = File.AppendText("test_vectors.txt"))
            //string filename = ControllerArgs.textnum.ToString() + ".txt";
            //using (StreamWriter writer = new StreamWriter(filename))
            {
                while (res.endless || res.current_trace < res.traces)
                {
                    string tempFile1 = @"C:\Lattice\UT Austin\Sakura-G-BRLWE\DPA_attack\MeasurementDone.txt";
                    string tempFile2 = @"C:\Program Files\Pico Technology\SDK\src\MATLAB\ps2000\temp2.txt";
                    

                    System.Threading.Thread.Sleep(10);
                    //System.Threading.Thread.Sleep(500);
                    
                    //File.Delete(tempFile1);
                    //using (File.Create(tempFile1))
                    //{
                    //}

                    //File.Delete(tempFile1);                    
                    //File.Delete(tempFile2);
                    res.answer = null;
                    res.ciphertext = null;
                    res.mask = null;
                    res.difference = null;
                    res.current_trace++;

                    if (!res.endless)
                    {
                        progress = (int)(100 * res.current_trace / res.traces);
                    }

                    if (res.randomGeneration)
                    {
                        res.plaintext = res.rand.generatePlaintext();
                    }

                    pcModule.Encrypt(ref res.answer, res.key, res.plaintext);
                    worker.ReportProgress(progress, (object)res);

                    int print_text;

                    for (print_text = 0; print_text < 3; print_text++)
                    {
                        writer.Write(res.plaintext[print_text].ToString("X2"));
                    }
                    



                    targetModule.Run(ref res.ciphertext,ref res.mask, res.plaintext, res.wait, ref res.elapsed);
                    res.diff = Utils.differenceByteArray(ref res.difference, res.answer, res.ciphertext);

                    /*
                    for (print_text = 0; print_text < 16; print_text++)
                    {
                        writer.Write(res.ciphertext[print_text] + ",");
                    }
                    */
                    writer.Write("\n");

                    /*
                    for (print_text = 0; print_text < 32; print_text++)
                    {
                        writer.Write(res.mask[print_text].ToString("X2"));
                    }
                    */
                    writer.Write("\n");
                    writer.Flush();

                    //while (!File.Exists(tempFile1))
                    //{
                    //    System.Threading.Thread.Sleep(10);
                    //}
                    //File.Delete(tempFile1);
                    System.Threading.Thread.Sleep(10);
                    
                    ////SIGLENT INTERFACE
                    // Create the MATLAB instance 
                    //var activationContext = Type.GetTypeFromProgID("matlab.application.single");
                    //var matlab = (MLApp.MLApp)Activator.CreateInstance(activationContext);
                    //matlab.Visible = 0;
                    //string name = Openfile.FileName;

                    //MLApp.MLApp matlab = new MLApp.MLApp();

                    // Change to the directory where the function is located 
                    //matlab.Execute(@"cd C:\cmat");

                    // Define the output 
                    object matlabOut = null;
                    
                    // Call the MATLAB function myfunc
                    //matlab.Feval("openSiglent", 1, out matlabOut, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1);
                    //matlab.Feval("test", 2, out result, 3.14, 42.0, "world"); 

                    // Display result 

                    /*
                    object[] waveform = matlabOut as object[];
                    using (StreamWriter writer2 = File.AppendText("SiglentMeasurements.txt"))
                    {
                        for (print_text = 0; print_text < 7000; print_text++)
                        {
                            //writer2.Write(((sbyte[,])(waveform[0]))[0, print_text]);
                            writer2.Write("\n");
                        }

                        writer2.Flush();
                    }
                    */
                    
                    //Console.WriteLine(resout[0]);
                    //Console.WriteLine(resout[1]);
                    //Console.ReadLine(); 
                   
                
                    
                    //while (File.Exists(tempFile1))
                    //{
                        //while (!File.Exists(tempFile2))
                        //{
                        //    File.Delete(tempFile1);    
                        //}
                        //File.Delete(tempFile1);
                    //}


                    ////

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
                }
            }
            res.last = true;
            worker.ReportProgress(progress, (object)res);
            e.Result = (object)res;
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

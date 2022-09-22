using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.Diagnostics;
using SAKURA;

namespace SAKURA_Checker
{
    public partial class MainForm : Form
    {
        private appState state = appState.Idle;
        private RandGen rand;
        private Controller ctrl;
        private ControllerArgs args;
        private Stopwatch sw = new Stopwatch();

        public MainForm()
        {
            InitializeComponent();
            comboBox_target.SelectedIndex = 0;
            updateFormEnabling();
            ctrl = new Controller();
            rand = new RandGen(1, 0);
        }

        private void checkBox_56bitkey_CheckedChanged(object sender, EventArgs e)
        {
            if (checkBox_56bitkey.Checked)
            {
                byte[] key = Utils.stringToByteArray(textBox_key.Text);
                for (int i = 0; i <= 8; i++)
                {
                    key[i] = (byte)i;
                }
                textBox_key.Text = Utils.byteArrayToString(key);
            }
        }

        private void button_changekey_Click(object sender, EventArgs e)
        {
            textBox_key.Text = Utils.byteArrayToString(rand.generateKey(checkBox_56bitkey.Checked));
        }

        private void button_changeplaintext_Click(object sender, EventArgs e)
        {
            textBox_plaintext.Text = Utils.byteArrayToString(rand.generatePlaintext());
        }

        private void button_single_Click(object sender, EventArgs e)
        {
            state = appState.Running;
            updateFormEnabling();
            run(true);
        }

        private void button_start_Click(object sender, EventArgs e)
        {
            state = appState.Running;
            updateFormEnabling();
            run(false);
        }

        private void button_stop_Click(object sender, EventArgs e)
        {
            state = appState.Stop;
            updateFormEnabling();
            ctrl.Cancel();
        }

        private void textBox_key_Leave(object sender, EventArgs e)
        {
            textBox_key.Text = Utils.formHexlString(textBox_key.Text);
        }

        private void textBox_plaintext_Leave(object sender, EventArgs e)
        {
            textBox_plaintext.Text = Utils.formHexlString(textBox_plaintext.Text);
        }

        private void worker_ProgressChanged(object sender, ProgressChangedEventArgs e)
        {
            ControllerArgs args = (ControllerArgs)e.UserState;

            sw.Stop();
            if (args.current_trace == 1 | args.last || sw.ElapsedMilliseconds >= 30)
            {
                textBox_rtraces.Text = args.current_trace.ToString();
                textBox_relapsed.Text = args.elapsed.ToString("f3");
                textBox_rplaintext.Text = Utils.byteArrayToString(args.plaintext);
                textBox_ranswer.Text = Utils.byteArrayToString(args.answer);
                textBox_rciphertext.Text = Utils.byteArrayToString(args.ciphertext);
                textBox_rdifference.Text = Utils.byteArrayToString(args.difference);
                if (toolStripProgressBar_progress.ProgressBar != null)
                {
                    toolStripProgressBar_progress.Value = e.ProgressPercentage;
                }
                sw.Reset();

                textBox_rtraces.Update();
                textBox_relapsed.Update();
                textBox_rplaintext.Update();
                textBox_ranswer.Update();
                textBox_rciphertext.Update();
                textBox_rdifference.Update();
            }
            sw.Start();
        }

        private void worker_RunWorkerCompleted(object sender, RunWorkerCompletedEventArgs e)
        {
            if (e.Cancelled)
            {
                statusMessage("Cancelled.");
                toolStripProgressBar_progress.Value = 0;
            }
            else
            {
                ControllerArgs res = (ControllerArgs)e.Result;

                if (res.error)
                {
                    statusMessage("Error.");
                    toolStripProgressBar_progress.Value = 0;
                }
                else
                {
                    statusMessage("Completed.");
                }
            }

            if (!args.single)
            {
                rand.restartPlaintextPrng();
            }

            ctrl.Close();
            sw.Stop();
            state = appState.Idle;
            updateFormEnabling();
            toolStripProgressBar_progress.Style = ProgressBarStyle.Blocks;
        }

        private void updateFormEnabling()
        {
            switch (state)
            {
                case appState.Idle:
                    textBox_interface.Enabled = true;
                    comboBox_target.Enabled = true;
                    textBox_traces.Enabled = true;
                    checkBox_endless.Enabled = true;
                    textBox_key.Enabled = true;
                    button_changekey.Enabled = true;
                    checkBox_56bitkey.Enabled = true;
                    textBox_plaintext.Enabled = true;
                    button_changeplaintext.Enabled = true;
                    checkBox_randomgeneration.Enabled = true;
                    textBox_wait.Enabled = true;
                    button_single.Enabled = true;
                    button_start.Enabled = true;
                    button_stop.Enabled = false;
                    checkBox_continueiferror.Enabled = true;
                    break;

                case appState.Start:
                    textBox_interface.Enabled = false;
                    comboBox_target.Enabled = false;
                    textBox_traces.Enabled = false;
                    checkBox_endless.Enabled = false;
                    textBox_key.Enabled = false;
                    button_changekey.Enabled = false;
                    checkBox_56bitkey.Enabled = false;
                    textBox_plaintext.Enabled = false;
                    button_changeplaintext.Enabled = false;
                    checkBox_randomgeneration.Enabled = false;
                    textBox_wait.Enabled = false;
                    button_single.Enabled = false;
                    button_start.Enabled = false;
                    button_stop.Enabled = true;
                    checkBox_continueiferror.Enabled = false;
                    break;

                case appState.Running:
                    textBox_interface.Enabled = false;
                    comboBox_target.Enabled = false;
                    textBox_traces.Enabled = false;
                    checkBox_endless.Enabled = false;
                    textBox_key.Enabled = false;
                    button_changekey.Enabled = false;
                    checkBox_56bitkey.Enabled = false;
                    textBox_plaintext.Enabled = false;
                    button_changeplaintext.Enabled = false;
                    checkBox_randomgeneration.Enabled = false;
                    textBox_wait.Enabled = false;
                    button_single.Enabled = false;
                    button_start.Enabled = false;
                    button_stop.Enabled = true;
                    checkBox_continueiferror.Enabled = false;
                    break;

                case appState.Stop:
                    textBox_interface.Enabled = false;
                    comboBox_target.Enabled = false;
                    textBox_traces.Enabled = false;
                    checkBox_endless.Enabled = false;
                    textBox_key.Enabled = false;
                    button_changekey.Enabled = false;
                    checkBox_56bitkey.Enabled = false;
                    textBox_plaintext.Enabled = false;
                    button_changeplaintext.Enabled = false;
                    checkBox_randomgeneration.Enabled = false;
                    textBox_wait.Enabled = false;
                    button_single.Enabled = false;
                    button_start.Enabled = false;
                    button_stop.Enabled = false;
                    checkBox_continueiferror.Enabled = false;
                    break;
            }
        }

        private void statusMessage(string message)
        {
            toolStripStatusLabel_message.Text = message;
        }

        private enum appState : int
        {
            Idle = 0,
            Start,
            Running,
            Stop
        }

        private void run(bool single)
        {
            args = new ControllerArgs();

            try
            {
                uint port = 0;
                if (String.Compare("USB", textBox_interface.Text.Substring(0, 3), true) == 0)
                {
                    if (!uint.TryParse(textBox_interface.Text.Substring(3), out port))
                    {
                        throw new Exception("Error: Invalid Interface.");
                    }
                }
                else
                {
                    throw new Exception("Error: Invalid Interface.");
                }

                ctrl.Open(port);
                ctrl.AddProgressChangedEventHandler(new ProgressChangedEventHandler(worker_ProgressChanged));
                ctrl.AddCompletedEventHandler(new RunWorkerCompletedEventHandler(worker_RunWorkerCompleted));

                args.single = single;
                args.traces = Convert.ToInt64(textBox_traces.Text);
                args.endless = checkBox_endless.Checked;
                if (!args.single)
                {
                    rand.restartPlaintextPrng();
                }

                sw.Start();
                statusMessage("Running...");

                toolStripProgressBar_progress.Value = 0;
                if (args.endless)
                {
                    toolStripProgressBar_progress.Style = ProgressBarStyle.Marquee;
                }
                else
                {
                    toolStripProgressBar_progress.Style = ProgressBarStyle.Blocks;
                }

                args.key = Utils.stringToByteArray(textBox_key.Text);
                args.plaintext = Utils.stringToByteArray(textBox_plaintext.Text);
                args.randomGeneration = checkBox_randomgeneration.Checked;
                args.wait = Convert.ToInt32(textBox_wait.Text);
                args.continueIfError = checkBox_continueiferror.Checked;
                args.rand = rand;
                ctrl.Run(args);
            }
            catch (Exception ex)
            {
                statusMessage(ex.Message);
                toolStripProgressBar_progress.Value = 0;
                toolStripProgressBar_progress.Style = ProgressBarStyle.Blocks;
                state = appState.Idle;
                updateFormEnabling();
            }
        }
    }
}

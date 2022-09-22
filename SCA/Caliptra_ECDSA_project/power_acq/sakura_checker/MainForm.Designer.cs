namespace SAKURA_Checker
{
    partial class MainForm
    {
        /// <summary>
        /// 必要なデザイナ変数です。
        /// </summary>
        private System.ComponentModel.IContainer components = null;

        /// <summary>
        /// 使用中のリソースをすべてクリーンアップします。
        /// </summary>
        /// <param name="disposing">マネージ リソースが破棄される場合 true、破棄されない場合は false です。</param>
        protected override void Dispose(bool disposing)
        {
            if (disposing && (components != null))
            {
                components.Dispose();
            }
            base.Dispose(disposing);
        }

        #region Windows フォーム デザイナで生成されたコード

        /// <summary>
        /// デザイナ サポートに必要なメソッドです。このメソッドの内容を
        /// コード エディタで変更しないでください。
        /// </summary>
        private void InitializeComponent()
        {
            System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(MainForm));
            this.comboBox_target = new System.Windows.Forms.ComboBox();
            this.label_interface = new System.Windows.Forms.Label();
            this.label_target = new System.Windows.Forms.Label();
            this.label_traces = new System.Windows.Forms.Label();
            this.textBox_traces = new System.Windows.Forms.TextBox();
            this.label_key = new System.Windows.Forms.Label();
            this.label_plaintext = new System.Windows.Forms.Label();
            this.checkBox_endless = new System.Windows.Forms.CheckBox();
            this.textBox_key = new System.Windows.Forms.TextBox();
            this.button_changekey = new System.Windows.Forms.Button();
            this.textBox_plaintext = new System.Windows.Forms.TextBox();
            this.button_changeplaintext = new System.Windows.Forms.Button();
            this.checkBox_randomgeneration = new System.Windows.Forms.CheckBox();
            this.label_wait = new System.Windows.Forms.Label();
            this.textBox_wait = new System.Windows.Forms.TextBox();
            this.button_single = new System.Windows.Forms.Button();
            this.button_start = new System.Windows.Forms.Button();
            this.button_stop = new System.Windows.Forms.Button();
            this.checkBox_continueiferror = new System.Windows.Forms.CheckBox();
            this.label_rtraces = new System.Windows.Forms.Label();
            this.textBox_rtraces = new System.Windows.Forms.TextBox();
            this.label_rplaintext = new System.Windows.Forms.Label();
            this.label_rciphertext = new System.Windows.Forms.Label();
            this.label_ranswer = new System.Windows.Forms.Label();
            this.label_rdifference = new System.Windows.Forms.Label();
            this.label_relapsed = new System.Windows.Forms.Label();
            this.textBox_rplaintext = new System.Windows.Forms.TextBox();
            this.textBox_rciphertext = new System.Windows.Forms.TextBox();
            this.textBox_ranswer = new System.Windows.Forms.TextBox();
            this.textBox_rdifference = new System.Windows.Forms.TextBox();
            this.checkBox_56bitkey = new System.Windows.Forms.CheckBox();
            this.textBox_relapsed = new System.Windows.Forms.TextBox();
            this.label_waitms = new System.Windows.Forms.Label();
            this.label_relapsed_ms = new System.Windows.Forms.Label();
            this.textBox_interface = new System.Windows.Forms.TextBox();
            this.statusStrip_status = new System.Windows.Forms.StatusStrip();
            this.toolStripProgressBar_progress = new System.Windows.Forms.ToolStripProgressBar();
            this.toolStripStatusLabel_message = new System.Windows.Forms.ToolStripStatusLabel();
            this.statusStrip_status.SuspendLayout();
            this.SuspendLayout();
            // 
            // comboBox_target
            // 
            this.comboBox_target.DropDownStyle = System.Windows.Forms.ComboBoxStyle.DropDownList;
            this.comboBox_target.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.comboBox_target.FormattingEnabled = true;
            this.comboBox_target.Items.AddRange(new object[] {
            "SAKURA-G Quick Start"});
            this.comboBox_target.Location = new System.Drawing.Point(91, 34);
            this.comboBox_target.Name = "comboBox_target";
            this.comboBox_target.Size = new System.Drawing.Size(336, 23);
            this.comboBox_target.TabIndex = 3;
            // 
            // label_interface
            // 
            this.label_interface.AutoSize = true;
            this.label_interface.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_interface.Location = new System.Drawing.Point(8, 12);
            this.label_interface.Name = "label_interface";
            this.label_interface.Size = new System.Drawing.Size(70, 15);
            this.label_interface.TabIndex = 0;
            this.label_interface.Text = "Interface";
            // 
            // label_target
            // 
            this.label_target.AutoSize = true;
            this.label_target.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_target.Location = new System.Drawing.Point(8, 37);
            this.label_target.Name = "label_target";
            this.label_target.Size = new System.Drawing.Size(49, 15);
            this.label_target.TabIndex = 2;
            this.label_target.Text = "Target";
            // 
            // label_traces
            // 
            this.label_traces.AutoSize = true;
            this.label_traces.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_traces.Location = new System.Drawing.Point(8, 62);
            this.label_traces.Name = "label_traces";
            this.label_traces.Size = new System.Drawing.Size(56, 15);
            this.label_traces.TabIndex = 4;
            this.label_traces.Text = "#Traces";
            // 
            // textBox_traces
            // 
            this.textBox_traces.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_traces.Location = new System.Drawing.Point(91, 59);
            this.textBox_traces.Name = "textBox_traces";
            this.textBox_traces.Size = new System.Drawing.Size(100, 23);
            this.textBox_traces.TabIndex = 5;
            this.textBox_traces.Text = "1000";
            this.textBox_traces.TextAlign = System.Windows.Forms.HorizontalAlignment.Right;
            // 
            // label_key
            // 
            this.label_key.AutoSize = true;
            this.label_key.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_key.Location = new System.Drawing.Point(8, 87);
            this.label_key.Name = "label_key";
            this.label_key.Size = new System.Drawing.Size(28, 15);
            this.label_key.TabIndex = 7;
            this.label_key.Text = "Key";
            // 
            // label_plaintext
            // 
            this.label_plaintext.AutoSize = true;
            this.label_plaintext.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_plaintext.Location = new System.Drawing.Point(8, 112);
            this.label_plaintext.Name = "label_plaintext";
            this.label_plaintext.Size = new System.Drawing.Size(70, 15);
            this.label_plaintext.TabIndex = 11;
            this.label_plaintext.Text = "Plaintext";
            // 
            // checkBox_endless
            // 
            this.checkBox_endless.AutoSize = true;
            this.checkBox_endless.Checked = true;
            this.checkBox_endless.CheckState = System.Windows.Forms.CheckState.Checked;
            this.checkBox_endless.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.checkBox_endless.Location = new System.Drawing.Point(197, 61);
            this.checkBox_endless.Name = "checkBox_endless";
            this.checkBox_endless.Size = new System.Drawing.Size(75, 19);
            this.checkBox_endless.TabIndex = 6;
            this.checkBox_endless.Text = "Endless";
            this.checkBox_endless.UseVisualStyleBackColor = true;
            // 
            // textBox_key
            // 
            this.textBox_key.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_key.Location = new System.Drawing.Point(91, 84);
            this.textBox_key.Name = "textBox_key";
            this.textBox_key.Size = new System.Drawing.Size(336, 23);
            this.textBox_key.TabIndex = 8;
            this.textBox_key.Text = "00 01 02 03 04 05 06 07 08 09 0A 0B 0C 0D 0E 0F";
            this.textBox_key.Leave += new System.EventHandler(this.textBox_key_Leave);
            // 
            // button_changekey
            // 
            this.button_changekey.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_changekey.Location = new System.Drawing.Point(433, 83);
            this.button_changekey.Name = "button_changekey";
            this.button_changekey.Size = new System.Drawing.Size(58, 23);
            this.button_changekey.TabIndex = 9;
            this.button_changekey.Text = "Change";
            this.button_changekey.UseVisualStyleBackColor = true;
            this.button_changekey.Click += new System.EventHandler(this.button_changekey_Click);
            // 
            // textBox_plaintext
            // 
            this.textBox_plaintext.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_plaintext.Location = new System.Drawing.Point(91, 109);
            this.textBox_plaintext.Name = "textBox_plaintext";
            this.textBox_plaintext.Size = new System.Drawing.Size(336, 23);
            this.textBox_plaintext.TabIndex = 12;
            this.textBox_plaintext.Text = "00 11 22 33 44 55 66 77 88 99 AA BB CC DD EE FF";
            this.textBox_plaintext.Leave += new System.EventHandler(this.textBox_plaintext_Leave);
            // 
            // button_changeplaintext
            // 
            this.button_changeplaintext.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_changeplaintext.Location = new System.Drawing.Point(433, 108);
            this.button_changeplaintext.Name = "button_changeplaintext";
            this.button_changeplaintext.Size = new System.Drawing.Size(58, 23);
            this.button_changeplaintext.TabIndex = 13;
            this.button_changeplaintext.Text = "Change";
            this.button_changeplaintext.UseVisualStyleBackColor = true;
            this.button_changeplaintext.Click += new System.EventHandler(this.button_changeplaintext_Click);
            // 
            // checkBox_randomgeneration
            // 
            this.checkBox_randomgeneration.AutoSize = true;
            this.checkBox_randomgeneration.Checked = true;
            this.checkBox_randomgeneration.CheckState = System.Windows.Forms.CheckState.Checked;
            this.checkBox_randomgeneration.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.checkBox_randomgeneration.Location = new System.Drawing.Point(497, 111);
            this.checkBox_randomgeneration.Name = "checkBox_randomgeneration";
            this.checkBox_randomgeneration.Size = new System.Drawing.Size(145, 19);
            this.checkBox_randomgeneration.TabIndex = 14;
            this.checkBox_randomgeneration.Text = "Random Generation";
            this.checkBox_randomgeneration.UseVisualStyleBackColor = true;
            // 
            // label_wait
            // 
            this.label_wait.AutoSize = true;
            this.label_wait.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_wait.Location = new System.Drawing.Point(8, 137);
            this.label_wait.Name = "label_wait";
            this.label_wait.Size = new System.Drawing.Size(35, 15);
            this.label_wait.TabIndex = 15;
            this.label_wait.Text = "Wait";
            // 
            // textBox_wait
            // 
            this.textBox_wait.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_wait.Location = new System.Drawing.Point(91, 134);
            this.textBox_wait.Name = "textBox_wait";
            this.textBox_wait.Size = new System.Drawing.Size(100, 23);
            this.textBox_wait.TabIndex = 16;
            this.textBox_wait.Text = "0";
            this.textBox_wait.TextAlign = System.Windows.Forms.HorizontalAlignment.Right;
            // 
            // button_single
            // 
            this.button_single.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_single.Location = new System.Drawing.Point(10, 163);
            this.button_single.Name = "button_single";
            this.button_single.Size = new System.Drawing.Size(75, 23);
            this.button_single.TabIndex = 18;
            this.button_single.Text = "Single";
            this.button_single.UseVisualStyleBackColor = true;
            this.button_single.Click += new System.EventHandler(this.button_single_Click);
            // 
            // button_start
            // 
            this.button_start.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_start.Location = new System.Drawing.Point(91, 163);
            this.button_start.Name = "button_start";
            this.button_start.Size = new System.Drawing.Size(75, 23);
            this.button_start.TabIndex = 19;
            this.button_start.Text = "Start";
            this.button_start.UseVisualStyleBackColor = true;
            this.button_start.Click += new System.EventHandler(this.button_start_Click);
            // 
            // button_stop
            // 
            this.button_stop.Enabled = false;
            this.button_stop.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_stop.Location = new System.Drawing.Point(172, 163);
            this.button_stop.Name = "button_stop";
            this.button_stop.Size = new System.Drawing.Size(75, 23);
            this.button_stop.TabIndex = 20;
            this.button_stop.Text = "Stop";
            this.button_stop.UseVisualStyleBackColor = true;
            this.button_stop.Click += new System.EventHandler(this.button_stop_Click);
            // 
            // checkBox_continueiferror
            // 
            this.checkBox_continueiferror.AutoSize = true;
            this.checkBox_continueiferror.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.checkBox_continueiferror.Location = new System.Drawing.Point(253, 166);
            this.checkBox_continueiferror.Name = "checkBox_continueiferror";
            this.checkBox_continueiferror.Size = new System.Drawing.Size(145, 19);
            this.checkBox_continueiferror.TabIndex = 21;
            this.checkBox_continueiferror.Text = "Continue if error";
            this.checkBox_continueiferror.UseVisualStyleBackColor = true;
            // 
            // label_rtraces
            // 
            this.label_rtraces.AutoSize = true;
            this.label_rtraces.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_rtraces.Location = new System.Drawing.Point(8, 195);
            this.label_rtraces.Name = "label_rtraces";
            this.label_rtraces.Size = new System.Drawing.Size(56, 15);
            this.label_rtraces.TabIndex = 22;
            this.label_rtraces.Text = "#Traces";
            // 
            // textBox_rtraces
            // 
            this.textBox_rtraces.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_rtraces.Location = new System.Drawing.Point(91, 192);
            this.textBox_rtraces.Name = "textBox_rtraces";
            this.textBox_rtraces.ReadOnly = true;
            this.textBox_rtraces.Size = new System.Drawing.Size(100, 23);
            this.textBox_rtraces.TabIndex = 23;
            this.textBox_rtraces.Text = "0";
            this.textBox_rtraces.TextAlign = System.Windows.Forms.HorizontalAlignment.Right;
            // 
            // label_rplaintext
            // 
            this.label_rplaintext.AutoSize = true;
            this.label_rplaintext.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_rplaintext.Location = new System.Drawing.Point(8, 245);
            this.label_rplaintext.Name = "label_rplaintext";
            this.label_rplaintext.Size = new System.Drawing.Size(70, 15);
            this.label_rplaintext.TabIndex = 27;
            this.label_rplaintext.Text = "Plaintext";
            // 
            // label_rciphertext
            // 
            this.label_rciphertext.AutoSize = true;
            this.label_rciphertext.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_rciphertext.Location = new System.Drawing.Point(8, 270);
            this.label_rciphertext.Name = "label_rciphertext";
            this.label_rciphertext.Size = new System.Drawing.Size(77, 15);
            this.label_rciphertext.TabIndex = 29;
            this.label_rciphertext.Text = "Ciphertext";
            // 
            // label_ranswer
            // 
            this.label_ranswer.AutoSize = true;
            this.label_ranswer.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_ranswer.Location = new System.Drawing.Point(8, 295);
            this.label_ranswer.Name = "label_ranswer";
            this.label_ranswer.Size = new System.Drawing.Size(49, 15);
            this.label_ranswer.TabIndex = 31;
            this.label_ranswer.Text = "Answer";
            // 
            // label_rdifference
            // 
            this.label_rdifference.AutoSize = true;
            this.label_rdifference.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_rdifference.Location = new System.Drawing.Point(8, 320);
            this.label_rdifference.Name = "label_rdifference";
            this.label_rdifference.Size = new System.Drawing.Size(77, 15);
            this.label_rdifference.TabIndex = 33;
            this.label_rdifference.Text = "Difference";
            // 
            // label_relapsed
            // 
            this.label_relapsed.AutoSize = true;
            this.label_relapsed.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_relapsed.Location = new System.Drawing.Point(8, 220);
            this.label_relapsed.Name = "label_relapsed";
            this.label_relapsed.Size = new System.Drawing.Size(56, 15);
            this.label_relapsed.TabIndex = 24;
            this.label_relapsed.Text = "Elapsed";
            // 
            // textBox_rplaintext
            // 
            this.textBox_rplaintext.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_rplaintext.Location = new System.Drawing.Point(91, 242);
            this.textBox_rplaintext.Name = "textBox_rplaintext";
            this.textBox_rplaintext.ReadOnly = true;
            this.textBox_rplaintext.Size = new System.Drawing.Size(336, 23);
            this.textBox_rplaintext.TabIndex = 28;
            // 
            // textBox_rciphertext
            // 
            this.textBox_rciphertext.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_rciphertext.Location = new System.Drawing.Point(91, 267);
            this.textBox_rciphertext.Name = "textBox_rciphertext";
            this.textBox_rciphertext.ReadOnly = true;
            this.textBox_rciphertext.Size = new System.Drawing.Size(336, 23);
            this.textBox_rciphertext.TabIndex = 30;
            // 
            // textBox_ranswer
            // 
            this.textBox_ranswer.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_ranswer.Location = new System.Drawing.Point(91, 292);
            this.textBox_ranswer.Name = "textBox_ranswer";
            this.textBox_ranswer.ReadOnly = true;
            this.textBox_ranswer.Size = new System.Drawing.Size(336, 23);
            this.textBox_ranswer.TabIndex = 32;
            // 
            // textBox_rdifference
            // 
            this.textBox_rdifference.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_rdifference.Location = new System.Drawing.Point(91, 317);
            this.textBox_rdifference.Name = "textBox_rdifference";
            this.textBox_rdifference.ReadOnly = true;
            this.textBox_rdifference.Size = new System.Drawing.Size(336, 23);
            this.textBox_rdifference.TabIndex = 34;
            // 
            // checkBox_56bitkey
            // 
            this.checkBox_56bitkey.AutoSize = true;
            this.checkBox_56bitkey.Font = new System.Drawing.Font("Consolas", 9.75F);
            this.checkBox_56bitkey.Location = new System.Drawing.Point(497, 88);
            this.checkBox_56bitkey.Name = "checkBox_56bitkey";
            this.checkBox_56bitkey.Size = new System.Drawing.Size(89, 19);
            this.checkBox_56bitkey.TabIndex = 10;
            this.checkBox_56bitkey.Text = "56bit Key";
            this.checkBox_56bitkey.UseVisualStyleBackColor = true;
            this.checkBox_56bitkey.CheckedChanged += new System.EventHandler(this.checkBox_56bitkey_CheckedChanged);
            // 
            // textBox_relapsed
            // 
            this.textBox_relapsed.Font = new System.Drawing.Font("Consolas", 9.75F);
            this.textBox_relapsed.Location = new System.Drawing.Point(91, 217);
            this.textBox_relapsed.Name = "textBox_relapsed";
            this.textBox_relapsed.ReadOnly = true;
            this.textBox_relapsed.Size = new System.Drawing.Size(100, 23);
            this.textBox_relapsed.TabIndex = 25;
            this.textBox_relapsed.TextAlign = System.Windows.Forms.HorizontalAlignment.Right;
            // 
            // label_waitms
            // 
            this.label_waitms.AutoSize = true;
            this.label_waitms.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_waitms.Location = new System.Drawing.Point(197, 137);
            this.label_waitms.Name = "label_waitms";
            this.label_waitms.Size = new System.Drawing.Size(21, 15);
            this.label_waitms.TabIndex = 17;
            this.label_waitms.Text = "ms";
            // 
            // label_relapsed_ms
            // 
            this.label_relapsed_ms.AutoSize = true;
            this.label_relapsed_ms.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_relapsed_ms.Location = new System.Drawing.Point(197, 220);
            this.label_relapsed_ms.Name = "label_relapsed_ms";
            this.label_relapsed_ms.Size = new System.Drawing.Size(21, 15);
            this.label_relapsed_ms.TabIndex = 26;
            this.label_relapsed_ms.Text = "ms";
            // 
            // textBox_interface
            // 
            this.textBox_interface.Font = new System.Drawing.Font("Consolas", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_interface.Location = new System.Drawing.Point(91, 9);
            this.textBox_interface.Name = "textBox_interface";
            this.textBox_interface.Size = new System.Drawing.Size(100, 23);
            this.textBox_interface.TabIndex = 1;
            this.textBox_interface.Text = "USB0";
            // 
            // statusStrip_status
            // 
            this.statusStrip_status.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.toolStripProgressBar_progress,
            this.toolStripStatusLabel_message});
            this.statusStrip_status.Location = new System.Drawing.Point(0, 343);
            this.statusStrip_status.Name = "statusStrip_status";
            this.statusStrip_status.Size = new System.Drawing.Size(643, 22);
            this.statusStrip_status.SizingGrip = false;
            this.statusStrip_status.TabIndex = 35;
            this.statusStrip_status.Text = "statusStrip1";
            // 
            // toolStripProgressBar_progress
            // 
            this.toolStripProgressBar_progress.MarqueeAnimationSpeed = 20;
            this.toolStripProgressBar_progress.Name = "toolStripProgressBar_progress";
            this.toolStripProgressBar_progress.Size = new System.Drawing.Size(50, 16);
            this.toolStripProgressBar_progress.Step = 1;
            // 
            // toolStripStatusLabel_message
            // 
            this.toolStripStatusLabel_message.Font = new System.Drawing.Font("Consolas", 9.75F);
            this.toolStripStatusLabel_message.Name = "toolStripStatusLabel_message";
            this.toolStripStatusLabel_message.Size = new System.Drawing.Size(0, 17);
            // 
            // MainForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 12F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.ClientSize = new System.Drawing.Size(643, 365);
            this.Controls.Add(this.statusStrip_status);
            this.Controls.Add(this.textBox_interface);
            this.Controls.Add(this.label_relapsed_ms);
            this.Controls.Add(this.label_waitms);
            this.Controls.Add(this.textBox_relapsed);
            this.Controls.Add(this.checkBox_56bitkey);
            this.Controls.Add(this.textBox_rdifference);
            this.Controls.Add(this.textBox_ranswer);
            this.Controls.Add(this.textBox_rciphertext);
            this.Controls.Add(this.textBox_rplaintext);
            this.Controls.Add(this.label_relapsed);
            this.Controls.Add(this.label_rdifference);
            this.Controls.Add(this.label_ranswer);
            this.Controls.Add(this.label_rciphertext);
            this.Controls.Add(this.label_rplaintext);
            this.Controls.Add(this.textBox_rtraces);
            this.Controls.Add(this.label_rtraces);
            this.Controls.Add(this.checkBox_continueiferror);
            this.Controls.Add(this.button_stop);
            this.Controls.Add(this.button_start);
            this.Controls.Add(this.button_single);
            this.Controls.Add(this.textBox_wait);
            this.Controls.Add(this.label_wait);
            this.Controls.Add(this.checkBox_randomgeneration);
            this.Controls.Add(this.button_changeplaintext);
            this.Controls.Add(this.textBox_plaintext);
            this.Controls.Add(this.button_changekey);
            this.Controls.Add(this.textBox_key);
            this.Controls.Add(this.checkBox_endless);
            this.Controls.Add(this.label_plaintext);
            this.Controls.Add(this.label_key);
            this.Controls.Add(this.textBox_traces);
            this.Controls.Add(this.label_traces);
            this.Controls.Add(this.label_target);
            this.Controls.Add(this.label_interface);
            this.Controls.Add(this.comboBox_target);
            this.FormBorderStyle = System.Windows.Forms.FormBorderStyle.FixedSingle;
            this.Icon = ((System.Drawing.Icon)(resources.GetObject("$this.Icon")));
            this.MaximizeBox = false;
            this.Name = "MainForm";
            this.Text = "SAKURA Checker";
            this.statusStrip_status.ResumeLayout(false);
            this.statusStrip_status.PerformLayout();
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.ComboBox comboBox_target;
        private System.Windows.Forms.Label label_interface;
        private System.Windows.Forms.Label label_target;
        private System.Windows.Forms.Label label_traces;
        private System.Windows.Forms.TextBox textBox_traces;
        private System.Windows.Forms.Label label_key;
        private System.Windows.Forms.Label label_plaintext;
        private System.Windows.Forms.CheckBox checkBox_endless;
        private System.Windows.Forms.TextBox textBox_key;
        private System.Windows.Forms.Button button_changekey;
        private System.Windows.Forms.TextBox textBox_plaintext;
        private System.Windows.Forms.Button button_changeplaintext;
        private System.Windows.Forms.CheckBox checkBox_randomgeneration;
        private System.Windows.Forms.Label label_wait;
        private System.Windows.Forms.TextBox textBox_wait;
        private System.Windows.Forms.Button button_single;
        private System.Windows.Forms.Button button_start;
        private System.Windows.Forms.Button button_stop;
        private System.Windows.Forms.CheckBox checkBox_continueiferror;
        private System.Windows.Forms.Label label_rtraces;
        private System.Windows.Forms.TextBox textBox_rtraces;
        private System.Windows.Forms.Label label_rplaintext;
        private System.Windows.Forms.Label label_rciphertext;
        private System.Windows.Forms.Label label_ranswer;
        private System.Windows.Forms.Label label_rdifference;
        private System.Windows.Forms.Label label_relapsed;
        private System.Windows.Forms.TextBox textBox_rplaintext;
        private System.Windows.Forms.TextBox textBox_rciphertext;
        private System.Windows.Forms.TextBox textBox_ranswer;
        private System.Windows.Forms.TextBox textBox_rdifference;
        private System.Windows.Forms.CheckBox checkBox_56bitkey;
        private System.Windows.Forms.TextBox textBox_relapsed;
        private System.Windows.Forms.Label label_waitms;
        private System.Windows.Forms.Label label_relapsed_ms;
        private System.Windows.Forms.TextBox textBox_interface;
        private System.Windows.Forms.StatusStrip statusStrip_status;
        private System.Windows.Forms.ToolStripProgressBar toolStripProgressBar_progress;
        private System.Windows.Forms.ToolStripStatusLabel toolStripStatusLabel_message;
    }
}


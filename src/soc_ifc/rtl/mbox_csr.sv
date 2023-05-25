// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

module mbox_csr (
        input wire clk,
        input wire rst,

        input wire s_cpuif_req,
        input wire s_cpuif_req_is_wr,
        input wire [5:0] s_cpuif_addr,
        input wire [31:0] s_cpuif_wr_data,
        input wire [31:0] s_cpuif_wr_biten,
        output wire s_cpuif_req_stall_wr,
        output wire s_cpuif_req_stall_rd,
        output wire s_cpuif_rd_ack,
        output wire s_cpuif_rd_err,
        output wire [31:0] s_cpuif_rd_data,
        output wire s_cpuif_wr_ack,
        output wire s_cpuif_wr_err,

        input mbox_csr_pkg::mbox_csr__in_t hwif_in,
        output mbox_csr_pkg::mbox_csr__out_t hwif_out
    );

    //--------------------------------------------------------------------------
    // CPU Bus interface logic
    //--------------------------------------------------------------------------
    logic cpuif_req;
    logic cpuif_req_is_wr;
    logic [5:0] cpuif_addr;
    logic [31:0] cpuif_wr_data;
    logic [31:0] cpuif_wr_biten;
    logic cpuif_req_stall_wr;
    logic cpuif_req_stall_rd;

    logic cpuif_rd_ack;
    logic cpuif_rd_err;
    logic [31:0] cpuif_rd_data;

    logic cpuif_wr_ack;
    logic cpuif_wr_err;

    assign cpuif_req = s_cpuif_req;
    assign cpuif_req_is_wr = s_cpuif_req_is_wr;
    assign cpuif_addr = s_cpuif_addr;
    assign cpuif_wr_data = s_cpuif_wr_data;
    assign cpuif_wr_biten = s_cpuif_wr_biten;
    assign s_cpuif_req_stall_wr = cpuif_req_stall_wr;
    assign s_cpuif_req_stall_rd = cpuif_req_stall_rd;
    assign s_cpuif_rd_ack = cpuif_rd_ack;
    assign s_cpuif_rd_err = cpuif_rd_err;
    assign s_cpuif_rd_data = cpuif_rd_data;
    assign s_cpuif_wr_ack = cpuif_wr_ack;
    assign s_cpuif_wr_err = cpuif_wr_err;

    logic cpuif_req_masked;

    // Read & write latencies are balanced. Stalls not required
    assign cpuif_req_stall_rd = '0;
    assign cpuif_req_stall_wr = '0;
    assign cpuif_req_masked = cpuif_req;

    //--------------------------------------------------------------------------
    // Address Decode
    //--------------------------------------------------------------------------
    typedef struct packed{
        logic mbox_lock;
        logic mbox_user;
        logic mbox_cmd;
        logic mbox_dlen;
        logic mbox_datain;
        logic mbox_dataout;
        logic mbox_execute;
        logic mbox_status;
        logic mbox_unlock;
    } decoded_reg_strb_t;
    decoded_reg_strb_t decoded_reg_strb;
    logic decoded_req;
    logic decoded_req_is_wr;
    logic [31:0] decoded_wr_data;
    logic [31:0] decoded_wr_biten;

    always_comb begin
        decoded_reg_strb.mbox_lock = cpuif_req_masked & (cpuif_addr == 'h0);
        decoded_reg_strb.mbox_user = cpuif_req_masked & (cpuif_addr == 'h4);
        decoded_reg_strb.mbox_cmd = cpuif_req_masked & (cpuif_addr == 'h8);
        decoded_reg_strb.mbox_dlen = cpuif_req_masked & (cpuif_addr == 'hc);
        decoded_reg_strb.mbox_datain = cpuif_req_masked & (cpuif_addr == 'h10);
        decoded_reg_strb.mbox_dataout = cpuif_req_masked & (cpuif_addr == 'h14);
        decoded_reg_strb.mbox_execute = cpuif_req_masked & (cpuif_addr == 'h18);
        decoded_reg_strb.mbox_status = cpuif_req_masked & (cpuif_addr == 'h1c);
        decoded_reg_strb.mbox_unlock = cpuif_req_masked & (cpuif_addr == 'h20);
    end

    // Pass down signals to next stage
    assign decoded_req = cpuif_req_masked;
    assign decoded_req_is_wr = cpuif_req_is_wr;
    assign decoded_wr_data = cpuif_wr_data;
    assign decoded_wr_biten = cpuif_wr_biten;


    // Writes are always granted with no error response
    assign cpuif_wr_ack = decoded_req & decoded_req_is_wr;
    assign cpuif_wr_err = '0;
    //--------------------------------------------------------------------------
    // Field logic
    //--------------------------------------------------------------------------
    typedef struct packed{
        struct packed{
            struct packed{
                logic next;
                logic load_next;
            } lock;
        } mbox_lock;
        struct packed{
            struct packed{
                logic [31:0] next;
                logic load_next;
            } user;
        } mbox_user;
        struct packed{
            struct packed{
                logic [31:0] next;
                logic load_next;
            } command;
        } mbox_cmd;
        struct packed{
            struct packed{
                logic [31:0] next;
                logic load_next;
            } length;
        } mbox_dlen;
        struct packed{
            struct packed{
                logic [31:0] next;
                logic load_next;
            } datain;
        } mbox_datain;
        struct packed{
            struct packed{
                logic [31:0] next;
                logic load_next;
            } dataout;
        } mbox_dataout;
        struct packed{
            struct packed{
                logic next;
                logic load_next;
            } execute;
        } mbox_execute;
        struct packed{
            struct packed{
                logic [3:0] next;
                logic load_next;
            } status;
            struct packed{
                logic next;
                logic load_next;
            } ecc_single_error;
            struct packed{
                logic next;
                logic load_next;
            } ecc_double_error;
            struct packed{
                logic [2:0] next;
                logic load_next;
            } mbox_fsm_ps;
            struct packed{
                logic next;
                logic load_next;
            } soc_has_lock;
        } mbox_status;
        struct packed{
            struct packed{
                logic next;
                logic load_next;
            } unlock;
        } mbox_unlock;
    } field_combo_t;
    field_combo_t field_combo;

    typedef struct packed{
        struct packed{
            struct packed{
                logic value;
            } lock;
        } mbox_lock;
        struct packed{
            struct packed{
                logic [31:0] value;
            } user;
        } mbox_user;
        struct packed{
            struct packed{
                logic [31:0] value;
            } command;
        } mbox_cmd;
        struct packed{
            struct packed{
                logic [31:0] value;
            } length;
        } mbox_dlen;
        struct packed{
            struct packed{
                logic [31:0] value;
            } datain;
        } mbox_datain;
        struct packed{
            struct packed{
                logic [31:0] value;
            } dataout;
        } mbox_dataout;
        struct packed{
            struct packed{
                logic value;
            } execute;
        } mbox_execute;
        struct packed{
            struct packed{
                logic [3:0] value;
            } status;
            struct packed{
                logic value;
            } ecc_single_error;
            struct packed{
                logic value;
            } ecc_double_error;
            struct packed{
                logic [2:0] value;
            } mbox_fsm_ps;
            struct packed{
                logic value;
            } soc_has_lock;
        } mbox_status;
        struct packed{
            struct packed{
                logic value;
            } unlock;
        } mbox_unlock;
    } field_storage_t;
    field_storage_t field_storage;

    // Field: mbox_csr.mbox_lock.lock
    always_comb begin
        automatic logic [0:0] next_c = field_storage.mbox_lock.lock.value;
        automatic logic load_next_c = '0;
        if(hwif_in.mbox_lock.lock.hwclr) begin // HW Clear
            next_c = '0;
            load_next_c = '1;
        end else if(decoded_reg_strb.mbox_lock && !decoded_req_is_wr) begin // SW set on read
            next_c = '1;
            load_next_c = '1;
        end
        field_combo.mbox_lock.lock.next = next_c;
        field_combo.mbox_lock.lock.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_lock.lock.value <= 'h0;
        end else if(field_combo.mbox_lock.lock.load_next) begin
            field_storage.mbox_lock.lock.value <= field_combo.mbox_lock.lock.next;
        end
    end
    assign hwif_out.mbox_lock.lock.value = field_storage.mbox_lock.lock.value;
    assign hwif_out.mbox_lock.lock.swmod = decoded_reg_strb.mbox_lock && !decoded_req_is_wr;
    // Field: mbox_csr.mbox_user.user
    always_comb begin
        automatic logic [31:0] next_c = field_storage.mbox_user.user.value;
        automatic logic load_next_c = '0;
        if(hwif_in.lock_set) begin // HW Write - we
            next_c = hwif_in.mbox_user.user.next;
            load_next_c = '1;
        end
        field_combo.mbox_user.user.next = next_c;
        field_combo.mbox_user.user.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_user.user.value <= 'h0;
        end else if(field_combo.mbox_user.user.load_next) begin
            field_storage.mbox_user.user.value <= field_combo.mbox_user.user.next;
        end
    end
    assign hwif_out.mbox_user.user.value = field_storage.mbox_user.user.value;
    // Field: mbox_csr.mbox_cmd.command
    always_comb begin
        automatic logic [31:0] next_c = field_storage.mbox_cmd.command.value;
        automatic logic load_next_c = '0;
        if(decoded_reg_strb.mbox_cmd && decoded_req_is_wr && hwif_in.valid_requester) begin // SW write
            next_c = (field_storage.mbox_cmd.command.value & ~decoded_wr_biten[31:0]) | (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
            load_next_c = '1;
        end
        field_combo.mbox_cmd.command.next = next_c;
        field_combo.mbox_cmd.command.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_cmd.command.value <= 'h0;
        end else if(field_combo.mbox_cmd.command.load_next) begin
            field_storage.mbox_cmd.command.value <= field_combo.mbox_cmd.command.next;
        end
    end
    assign hwif_out.mbox_cmd.command.swmod = decoded_reg_strb.mbox_cmd && decoded_req_is_wr;
    // Field: mbox_csr.mbox_dlen.length
    always_comb begin
        automatic logic [31:0] next_c = field_storage.mbox_dlen.length.value;
        automatic logic load_next_c = '0;
        if(decoded_reg_strb.mbox_dlen && decoded_req_is_wr && hwif_in.valid_requester) begin // SW write
            next_c = (field_storage.mbox_dlen.length.value & ~decoded_wr_biten[31:0]) | (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
            load_next_c = '1;
        end
        field_combo.mbox_dlen.length.next = next_c;
        field_combo.mbox_dlen.length.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_dlen.length.value <= 'h0;
        end else if(field_combo.mbox_dlen.length.load_next) begin
            field_storage.mbox_dlen.length.value <= field_combo.mbox_dlen.length.next;
        end
    end
    assign hwif_out.mbox_dlen.length.value = field_storage.mbox_dlen.length.value;
    assign hwif_out.mbox_dlen.length.swmod = decoded_reg_strb.mbox_dlen && decoded_req_is_wr;
    // Field: mbox_csr.mbox_datain.datain
    always_comb begin
        automatic logic [31:0] next_c = field_storage.mbox_datain.datain.value;
        automatic logic load_next_c = '0;
        if(decoded_reg_strb.mbox_datain && decoded_req_is_wr && hwif_in.valid_requester) begin // SW write
            next_c = (field_storage.mbox_datain.datain.value & ~decoded_wr_biten[31:0]) | (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
            load_next_c = '1;
        end
        field_combo.mbox_datain.datain.next = next_c;
        field_combo.mbox_datain.datain.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_datain.datain.value <= 'h0;
        end else if(field_combo.mbox_datain.datain.load_next) begin
            field_storage.mbox_datain.datain.value <= field_combo.mbox_datain.datain.next;
        end
    end
    assign hwif_out.mbox_datain.datain.swmod = decoded_reg_strb.mbox_datain && decoded_req_is_wr;
    // Field: mbox_csr.mbox_dataout.dataout
    always_comb begin
        automatic logic [31:0] next_c = field_storage.mbox_dataout.dataout.value;
        automatic logic load_next_c = '0;
        if(decoded_reg_strb.mbox_dataout && decoded_req_is_wr && hwif_in.mbox_dataout.dataout.swwe) begin // SW write
            next_c = (field_storage.mbox_dataout.dataout.value & ~decoded_wr_biten[31:0]) | (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
            load_next_c = '1;
        end else if(hwif_in.mbox_dataout.dataout.we) begin // HW Write - we
            next_c = hwif_in.mbox_dataout.dataout.next;
            load_next_c = '1;
        end
        field_combo.mbox_dataout.dataout.next = next_c;
        field_combo.mbox_dataout.dataout.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_dataout.dataout.value <= 'h0;
        end else if(field_combo.mbox_dataout.dataout.load_next) begin
            field_storage.mbox_dataout.dataout.value <= field_combo.mbox_dataout.dataout.next;
        end
    end
    assign hwif_out.mbox_dataout.dataout.value = field_storage.mbox_dataout.dataout.value;
    assign hwif_out.mbox_dataout.dataout.swacc = decoded_reg_strb.mbox_dataout;
    // Field: mbox_csr.mbox_execute.execute
    always_comb begin
        automatic logic [0:0] next_c = field_storage.mbox_execute.execute.value;
        automatic logic load_next_c = '0;
        if(hwif_in.mbox_execute.execute.hwclr) begin // HW Clear
            next_c = '0;
            load_next_c = '1;
        end else if(decoded_reg_strb.mbox_execute && decoded_req_is_wr && hwif_in.valid_requester) begin // SW write
            next_c = (field_storage.mbox_execute.execute.value & ~decoded_wr_biten[0:0]) | (decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
            load_next_c = '1;
        end
        field_combo.mbox_execute.execute.next = next_c;
        field_combo.mbox_execute.execute.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_execute.execute.value <= 'h0;
        end else if(field_combo.mbox_execute.execute.load_next) begin
            field_storage.mbox_execute.execute.value <= field_combo.mbox_execute.execute.next;
        end
    end
    assign hwif_out.mbox_execute.execute.value = field_storage.mbox_execute.execute.value;
    assign hwif_out.mbox_execute.execute.swmod = decoded_reg_strb.mbox_execute && decoded_req_is_wr;
    // Field: mbox_csr.mbox_status.status
    always_comb begin
        automatic logic [3:0] next_c = field_storage.mbox_status.status.value;
        automatic logic load_next_c = '0;
        if(hwif_in.mbox_status.status.hwclr) begin // HW Clear
            next_c = '0;
            load_next_c = '1;
        end else if(decoded_reg_strb.mbox_status && decoded_req_is_wr && hwif_in.valid_receiver) begin // SW write
            next_c = (field_storage.mbox_status.status.value & ~decoded_wr_biten[3:0]) | (decoded_wr_data[3:0] & decoded_wr_biten[3:0]);
            load_next_c = '1;
        end
        field_combo.mbox_status.status.next = next_c;
        field_combo.mbox_status.status.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_status.status.value <= 'h0;
        end else if(field_combo.mbox_status.status.load_next) begin
            field_storage.mbox_status.status.value <= field_combo.mbox_status.status.next;
        end
    end
    assign hwif_out.mbox_status.status.value = field_storage.mbox_status.status.value;
    assign hwif_out.mbox_status.status.swmod = decoded_reg_strb.mbox_status && decoded_req_is_wr;
    // Field: mbox_csr.mbox_status.ecc_single_error
    always_comb begin
        automatic logic [0:0] next_c = field_storage.mbox_status.ecc_single_error.value;
        automatic logic load_next_c = '0;
        if(!field_storage.mbox_execute.execute.value) begin // HW Write - wel
            next_c = field_storage.mbox_execute.execute.value;
            load_next_c = '1;
        end else if(hwif_in.mbox_status.ecc_single_error.hwset) begin // HW Set
            next_c = '1;
            load_next_c = '1;
        end
        field_combo.mbox_status.ecc_single_error.next = next_c;
        field_combo.mbox_status.ecc_single_error.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_status.ecc_single_error.value <= 'h0;
        end else if(field_combo.mbox_status.ecc_single_error.load_next) begin
            field_storage.mbox_status.ecc_single_error.value <= field_combo.mbox_status.ecc_single_error.next;
        end
    end
    assign hwif_out.mbox_status.ecc_single_error.value = field_storage.mbox_status.ecc_single_error.value;
    // Field: mbox_csr.mbox_status.ecc_double_error
    always_comb begin
        automatic logic [0:0] next_c = field_storage.mbox_status.ecc_double_error.value;
        automatic logic load_next_c = '0;
        if(!field_storage.mbox_execute.execute.value) begin // HW Write - wel
            next_c = field_storage.mbox_execute.execute.value;
            load_next_c = '1;
        end else if(hwif_in.mbox_status.ecc_double_error.hwset) begin // HW Set
            next_c = '1;
            load_next_c = '1;
        end
        field_combo.mbox_status.ecc_double_error.next = next_c;
        field_combo.mbox_status.ecc_double_error.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_status.ecc_double_error.value <= 'h0;
        end else if(field_combo.mbox_status.ecc_double_error.load_next) begin
            field_storage.mbox_status.ecc_double_error.value <= field_combo.mbox_status.ecc_double_error.next;
        end
    end
    assign hwif_out.mbox_status.ecc_double_error.value = field_storage.mbox_status.ecc_double_error.value;
    // Field: mbox_csr.mbox_status.mbox_fsm_ps
    always_comb begin
        automatic logic [2:0] next_c = field_storage.mbox_status.mbox_fsm_ps.value;
        automatic logic load_next_c = '0;
        if(1) begin // HW Write
            next_c = hwif_in.mbox_status.mbox_fsm_ps.next;
            load_next_c = '1;
        end
        field_combo.mbox_status.mbox_fsm_ps.next = next_c;
        field_combo.mbox_status.mbox_fsm_ps.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_status.mbox_fsm_ps.value <= 'h0;
        end else if(field_combo.mbox_status.mbox_fsm_ps.load_next) begin
            field_storage.mbox_status.mbox_fsm_ps.value <= field_combo.mbox_status.mbox_fsm_ps.next;
        end
    end
    assign hwif_out.mbox_status.mbox_fsm_ps.value = field_storage.mbox_status.mbox_fsm_ps.value;
    // Field: mbox_csr.mbox_status.soc_has_lock
    always_comb begin
        automatic logic [0:0] next_c = field_storage.mbox_status.soc_has_lock.value;
        automatic logic load_next_c = '0;
        if(1) begin // HW Write
            next_c = hwif_in.mbox_status.soc_has_lock.next;
            load_next_c = '1;
        end
        field_combo.mbox_status.soc_has_lock.next = next_c;
        field_combo.mbox_status.soc_has_lock.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_status.soc_has_lock.value <= 'h0;
        end else if(field_combo.mbox_status.soc_has_lock.load_next) begin
            field_storage.mbox_status.soc_has_lock.value <= field_combo.mbox_status.soc_has_lock.next;
        end
    end
    assign hwif_out.mbox_status.soc_has_lock.value = field_storage.mbox_status.soc_has_lock.value;
    // Field: mbox_csr.mbox_unlock.unlock
    always_comb begin
        automatic logic [0:0] next_c = field_storage.mbox_unlock.unlock.value;
        automatic logic load_next_c = '0;
        if(decoded_reg_strb.mbox_unlock && decoded_req_is_wr && !(hwif_in.soc_req)) begin // SW write
            next_c = (field_storage.mbox_unlock.unlock.value & ~decoded_wr_biten[0:0]) | (decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
            load_next_c = '1;
        end else if(1) begin // singlepulse clears back to 0
            next_c = '0;
            load_next_c = '1;
        end
        field_combo.mbox_unlock.unlock.next = next_c;
        field_combo.mbox_unlock.unlock.load_next = load_next_c;
    end
    always_ff @(posedge clk or negedge hwif_in.cptra_rst_b) begin
        if(~hwif_in.cptra_rst_b) begin
            field_storage.mbox_unlock.unlock.value <= 'h0;
        end else if(field_combo.mbox_unlock.unlock.load_next) begin
            field_storage.mbox_unlock.unlock.value <= field_combo.mbox_unlock.unlock.next;
        end
    end
    assign hwif_out.mbox_unlock.unlock.value = field_storage.mbox_unlock.unlock.value;
    //--------------------------------------------------------------------------
    // Readback
    //--------------------------------------------------------------------------
    logic readback_err;
    logic readback_done;
    logic [31:0] readback_data;
    
    // Assign readback values to a flattened array
    logic [9-1:0][31:0] readback_array;
    assign readback_array[0][0:0] = (decoded_reg_strb.mbox_lock && !decoded_req_is_wr) ? field_storage.mbox_lock.lock.value : '0;
    assign readback_array[0][31:1] = '0;
    assign readback_array[1][31:0] = (decoded_reg_strb.mbox_user && !decoded_req_is_wr) ? field_storage.mbox_user.user.value : '0;
    assign readback_array[2][31:0] = (decoded_reg_strb.mbox_cmd && !decoded_req_is_wr) ? field_storage.mbox_cmd.command.value : '0;
    assign readback_array[3][31:0] = (decoded_reg_strb.mbox_dlen && !decoded_req_is_wr) ? field_storage.mbox_dlen.length.value : '0;
    assign readback_array[4][31:0] = (decoded_reg_strb.mbox_datain && !decoded_req_is_wr) ? field_storage.mbox_datain.datain.value : '0;
    assign readback_array[5][31:0] = (decoded_reg_strb.mbox_dataout && !decoded_req_is_wr) ? field_storage.mbox_dataout.dataout.value : '0;
    assign readback_array[6][0:0] = (decoded_reg_strb.mbox_execute && !decoded_req_is_wr) ? field_storage.mbox_execute.execute.value : '0;
    assign readback_array[6][31:1] = '0;
    assign readback_array[7][3:0] = (decoded_reg_strb.mbox_status && !decoded_req_is_wr) ? field_storage.mbox_status.status.value : '0;
    assign readback_array[7][4:4] = (decoded_reg_strb.mbox_status && !decoded_req_is_wr) ? field_storage.mbox_status.ecc_single_error.value : '0;
    assign readback_array[7][5:5] = (decoded_reg_strb.mbox_status && !decoded_req_is_wr) ? field_storage.mbox_status.ecc_double_error.value : '0;
    assign readback_array[7][8:6] = (decoded_reg_strb.mbox_status && !decoded_req_is_wr) ? field_storage.mbox_status.mbox_fsm_ps.value : '0;
    assign readback_array[7][9:9] = (decoded_reg_strb.mbox_status && !decoded_req_is_wr) ? field_storage.mbox_status.soc_has_lock.value : '0;
    assign readback_array[7][31:10] = '0;
    assign readback_array[8][0:0] = (decoded_reg_strb.mbox_unlock && !decoded_req_is_wr) ? field_storage.mbox_unlock.unlock.value : '0;
    assign readback_array[8][31:1] = '0;

    // Reduce the array
    always_comb begin
        automatic logic [31:0] readback_data_var;
        readback_done = decoded_req & ~decoded_req_is_wr;
        readback_err = '0;
        readback_data_var = '0;
        for(int i=0; i<9; i++) readback_data_var |= readback_array[i];
        readback_data = readback_data_var;
    end

    assign cpuif_rd_ack = readback_done;
    assign cpuif_rd_data = readback_data;
    assign cpuif_rd_err = readback_err;
endmodule
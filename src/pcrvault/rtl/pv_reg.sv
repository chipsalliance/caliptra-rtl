// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

module pv_reg (
        input wire clk,
        input wire rst,

        input wire s_cpuif_req,
        input wire s_cpuif_req_is_wr,
        input wire [11:0] s_cpuif_addr,
        input wire [31:0] s_cpuif_wr_data,
        input wire [31:0] s_cpuif_wr_biten,
        output wire s_cpuif_req_stall_wr,
        output wire s_cpuif_req_stall_rd,
        output wire s_cpuif_rd_ack,
        output wire s_cpuif_rd_err,
        output wire [31:0] s_cpuif_rd_data,
        output wire s_cpuif_wr_ack,
        output wire s_cpuif_wr_err,

        input pv_reg_pkg::pv_reg__in_t hwif_in,
        output pv_reg_pkg::pv_reg__out_t hwif_out
    );

    //--------------------------------------------------------------------------
    // CPU Bus interface logic
    //--------------------------------------------------------------------------
    logic cpuif_req;
    logic cpuif_req_is_wr;
    logic [11:0] cpuif_addr;
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
        logic [32-1:0]PCR_CTRL;
        logic [32-1:0][12-1:0]PCR_ENTRY;
    } decoded_reg_strb_t;
    decoded_reg_strb_t decoded_reg_strb;
    logic decoded_req;
    logic decoded_req_is_wr;
    logic [31:0] decoded_wr_data;
    logic [31:0] decoded_wr_biten;

    always_comb begin
        for(int i0=0; i0<32; i0++) begin
            decoded_reg_strb.PCR_CTRL[i0] = cpuif_req_masked & (cpuif_addr == 'h0 + i0*'h4);
        end
        for(int i0=0; i0<32; i0++) begin
            for(int i1=0; i1<12; i1++) begin
                decoded_reg_strb.PCR_ENTRY[i0][i1] = cpuif_req_masked & (cpuif_addr == 'h600 + i0*'h30 + i1*'h4);
            end
        end
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
            struct packed{
                logic next;
                logic load_next;
            } clear;
            struct packed{
                logic next;
                logic load_next;
            } rsvd0;
            struct packed{
                logic [4:0] next;
                logic load_next;
            } rsvd1;
        } [32-1:0]PCR_CTRL;
        struct packed{
            struct packed{
                logic [31:0] next;
                logic load_next;
            } data;
        } [32-1:0][12-1:0]PCR_ENTRY;
    } field_combo_t;
    field_combo_t field_combo;

    typedef struct packed{
        struct packed{
            struct packed{
                logic value;
            } lock;
            struct packed{
                logic value;
            } clear;
            struct packed{
                logic value;
            } rsvd0;
            struct packed{
                logic [4:0] value;
            } rsvd1;
        } [32-1:0]PCR_CTRL;
        struct packed{
            struct packed{
                logic [31:0] value;
            } data;
        } [32-1:0][12-1:0]PCR_ENTRY;
    } field_storage_t;
    field_storage_t field_storage;

    for(genvar i0=0; i0<32; i0++) begin
        // Field: pv_reg.PCR_CTRL[].lock
        always_comb begin
            automatic logic [0:0] next_c = field_storage.PCR_CTRL[i0].lock.value;
            automatic logic load_next_c = '0;
            if(decoded_reg_strb.PCR_CTRL[i0] && decoded_req_is_wr && !(hwif_in.PCR_CTRL[i0].lock.swwel)) begin // SW write
                next_c = (field_storage.PCR_CTRL[i0].lock.value & ~decoded_wr_biten[0:0]) | (decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
                load_next_c = '1;
            end
            field_combo.PCR_CTRL[i0].lock.next = next_c;
            field_combo.PCR_CTRL[i0].lock.load_next = load_next_c;
        end
        always_ff @(posedge clk or negedge hwif_in.core_only_rst_b) begin
            if(~hwif_in.core_only_rst_b) begin
                field_storage.PCR_CTRL[i0].lock.value <= 'h0;
            end else if(field_combo.PCR_CTRL[i0].lock.load_next) begin
                field_storage.PCR_CTRL[i0].lock.value <= field_combo.PCR_CTRL[i0].lock.next;
            end
        end
        assign hwif_out.PCR_CTRL[i0].lock.value = field_storage.PCR_CTRL[i0].lock.value;
        // Field: pv_reg.PCR_CTRL[].clear
        always_comb begin
            automatic logic [0:0] next_c = field_storage.PCR_CTRL[i0].clear.value;
            automatic logic load_next_c = '0;
            if(decoded_reg_strb.PCR_CTRL[i0] && decoded_req_is_wr && !(hwif_in.PCR_CTRL[i0].clear.swwel)) begin // SW write
                next_c = (field_storage.PCR_CTRL[i0].clear.value & ~decoded_wr_biten[1:1]) | (decoded_wr_data[1:1] & decoded_wr_biten[1:1]);
                load_next_c = '1;
            end else if(1) begin // singlepulse clears back to 0
                next_c = '0;
                load_next_c = '1;
            end
            field_combo.PCR_CTRL[i0].clear.next = next_c;
            field_combo.PCR_CTRL[i0].clear.load_next = load_next_c;
        end
        always_ff @(posedge clk or negedge hwif_in.reset_b) begin
            if(~hwif_in.reset_b) begin
                field_storage.PCR_CTRL[i0].clear.value <= 'h0;
            end else if(field_combo.PCR_CTRL[i0].clear.load_next) begin
                field_storage.PCR_CTRL[i0].clear.value <= field_combo.PCR_CTRL[i0].clear.next;
            end
        end
        assign hwif_out.PCR_CTRL[i0].clear.value = field_storage.PCR_CTRL[i0].clear.value;
        // Field: pv_reg.PCR_CTRL[].rsvd0
        always_comb begin
            automatic logic [0:0] next_c = field_storage.PCR_CTRL[i0].rsvd0.value;
            automatic logic load_next_c = '0;
            if(decoded_reg_strb.PCR_CTRL[i0] && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.PCR_CTRL[i0].rsvd0.value & ~decoded_wr_biten[2:2]) | (decoded_wr_data[2:2] & decoded_wr_biten[2:2]);
                load_next_c = '1;
            end else if(hwif_in.PCR_CTRL[i0].rsvd0.hwclr) begin // HW Clear
                next_c = '0;
                load_next_c = '1;
            end
            field_combo.PCR_CTRL[i0].rsvd0.next = next_c;
            field_combo.PCR_CTRL[i0].rsvd0.load_next = load_next_c;
        end
        always_ff @(posedge clk or negedge hwif_in.reset_b) begin
            if(~hwif_in.reset_b) begin
                field_storage.PCR_CTRL[i0].rsvd0.value <= 'h0;
            end else if(field_combo.PCR_CTRL[i0].rsvd0.load_next) begin
                field_storage.PCR_CTRL[i0].rsvd0.value <= field_combo.PCR_CTRL[i0].rsvd0.next;
            end
        end
        assign hwif_out.PCR_CTRL[i0].rsvd0.value = field_storage.PCR_CTRL[i0].rsvd0.value;
        // Field: pv_reg.PCR_CTRL[].rsvd1
        always_comb begin
            automatic logic [4:0] next_c = field_storage.PCR_CTRL[i0].rsvd1.value;
            automatic logic load_next_c = '0;
            if(decoded_reg_strb.PCR_CTRL[i0] && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.PCR_CTRL[i0].rsvd1.value & ~decoded_wr_biten[7:3]) | (decoded_wr_data[7:3] & decoded_wr_biten[7:3]);
                load_next_c = '1;
            end
            field_combo.PCR_CTRL[i0].rsvd1.next = next_c;
            field_combo.PCR_CTRL[i0].rsvd1.load_next = load_next_c;
        end
        always_ff @(posedge clk or negedge hwif_in.reset_b) begin
            if(~hwif_in.reset_b) begin
                field_storage.PCR_CTRL[i0].rsvd1.value <= 'h0;
            end else if(field_combo.PCR_CTRL[i0].rsvd1.load_next) begin
                field_storage.PCR_CTRL[i0].rsvd1.value <= field_combo.PCR_CTRL[i0].rsvd1.next;
            end
        end
        assign hwif_out.PCR_CTRL[i0].rsvd1.value = field_storage.PCR_CTRL[i0].rsvd1.value;
    end
    for(genvar i0=0; i0<32; i0++) begin
        for(genvar i1=0; i1<12; i1++) begin
            // Field: pv_reg.PCR_ENTRY[][].data
            always_comb begin
                automatic logic [31:0] next_c = field_storage.PCR_ENTRY[i0][i1].data.value;
                automatic logic load_next_c = '0;
                if(hwif_in.PCR_ENTRY[i0][i1].data.we) begin // HW Write - we
                    next_c = hwif_in.PCR_ENTRY[i0][i1].data.next;
                    load_next_c = '1;
                end else if(hwif_in.PCR_ENTRY[i0][i1].data.hwclr) begin // HW Clear
                    next_c = '0;
                    load_next_c = '1;
                end
                field_combo.PCR_ENTRY[i0][i1].data.next = next_c;
                field_combo.PCR_ENTRY[i0][i1].data.load_next = load_next_c;
            end
            always_ff @(posedge clk or negedge hwif_in.hard_reset_b) begin
                if(~hwif_in.hard_reset_b) begin
                    field_storage.PCR_ENTRY[i0][i1].data.value <= 'h0;
                end else if(field_combo.PCR_ENTRY[i0][i1].data.load_next) begin
                    field_storage.PCR_ENTRY[i0][i1].data.value <= field_combo.PCR_ENTRY[i0][i1].data.next;
                end
            end
            assign hwif_out.PCR_ENTRY[i0][i1].data.value = field_storage.PCR_ENTRY[i0][i1].data.value;
        end
    end
    //--------------------------------------------------------------------------
    // Readback
    //--------------------------------------------------------------------------
    logic readback_err;
    logic readback_done;
    logic [31:0] readback_data;
    
    // Assign readback values to a flattened array
    logic [416-1:0][31:0] readback_array;
    for(genvar i0=0; i0<32; i0++) begin
        assign readback_array[i0*1 + 0][0:0] = (decoded_reg_strb.PCR_CTRL[i0] && !decoded_req_is_wr) ? field_storage.PCR_CTRL[i0].lock.value : '0;
        assign readback_array[i0*1 + 0][1:1] = (decoded_reg_strb.PCR_CTRL[i0] && !decoded_req_is_wr) ? field_storage.PCR_CTRL[i0].clear.value : '0;
        assign readback_array[i0*1 + 0][2:2] = (decoded_reg_strb.PCR_CTRL[i0] && !decoded_req_is_wr) ? field_storage.PCR_CTRL[i0].rsvd0.value : '0;
        assign readback_array[i0*1 + 0][7:3] = (decoded_reg_strb.PCR_CTRL[i0] && !decoded_req_is_wr) ? field_storage.PCR_CTRL[i0].rsvd1.value : '0;
        assign readback_array[i0*1 + 0][31:8] = '0;
    end
    for(genvar i0=0; i0<32; i0++) begin
        for(genvar i1=0; i1<12; i1++) begin
            assign readback_array[i0*12 + i1*1 + 32][31:0] = (decoded_reg_strb.PCR_ENTRY[i0][i1] && !decoded_req_is_wr) ? field_storage.PCR_ENTRY[i0][i1].data.value : '0;
        end
    end

    // Reduce the array
    always_comb begin
        automatic logic [31:0] readback_data_var;
        readback_done = decoded_req & ~decoded_req_is_wr;
        readback_err = '0;
        readback_data_var = '0;
        for(int i=0; i<416; i++) readback_data_var |= readback_array[i];
        readback_data = readback_data_var;
    end

    assign cpuif_rd_ack = readback_done;
    assign cpuif_rd_data = readback_data;
    assign cpuif_rd_err = readback_err;

`CALIPTRA_ASSERT_KNOWN(ERR_HWIF_IN, hwif_in, clk, hwif_in.hard_reset_b)

endmodule
//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
//    This interface performs the ECC_in signal driving.  It is
//     accessed by the uvm ECC_in driver through a virtual interface
//     handle in the ECC_in configuration.  It drives the singals passed
//     in through the port connection named bus of type ECC_in_if.
//
//     Input signals from the ECC_in_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within ECC_in_if based on INITIATOR/RESPONDER and/or
//     ARBITRATION/GRANT status.  
//
//     The output signal connections are as follows:
//        signal_o -> bus.signal
//
//                                                                                           
//      Interface functions and tasks used by UVM components:
//
//             configure:
//                   This function gets configuration attributes from the
//                   UVM driver to set any required BFM configuration
//                   variables such as 'initiator_responder'.                                       
//                                                                                           
//             initiate_and_get_response:
//                   This task is used to perform signaling activity for initiating
//                   a protocol transfer.  The task initiates the transfer, using
//                   input data from the initiator struct.  Then the task captures
//                   response data, placing the data into the response struct.
//                   The response struct is returned to the driver class.
//
//             respond_and_wait_for_next_transfer:
//                   This task is used to complete a current transfer as a responder
//                   and then wait for the initiator to start the next transfer.
//                   The task uses data in the responder struct to drive protocol
//                   signals to complete the transfer.  The task then waits for 
//                   the next transfer.  Once the next transfer begins, data from
//                   the initiator is placed into the initiator struct and sent
//                   to the responder sequence for processing to determine 
//                   what data to respond with.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import ECC_in_pkg_hdl::*;
`include "src/ECC_in_macros.svh"

interface ECC_in_driver_bfm #(
  int AHB_ADDR_WIDTH = 32,
  int AHB_DATA_WIDTH = 64
  )

  (ECC_in_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute ECC_in_driver_bfm partition_interface_xif

`ifndef XRTL
// This code is to aid in debugging parameter mismatches between the BFM and its corresponding agent.
// Enable this debug by setting UVM_VERBOSITY to UVM_DEBUG
// Setting UVM_VERBOSITY to UVM_DEBUG causes all BFM's and all agents to display their parameter settings.
// All of the messages from this feature have a UVM messaging id value of "CFG"
// The transcript or run.log can be parsed to ensure BFM parameter settings match its corresponding agents parameter settings.
import uvm_pkg::*;
`include "uvm_macros.svh"
initial begin : bfm_vs_agent_parameter_debug
  `uvm_info("CFG", 
      $psprintf("The BFM at '%m' has the following parameters: AHB_ADDR_WIDTH=%x AHB_DATA_WIDTH=%x ", AHB_ADDR_WIDTH,AHB_DATA_WIDTH),
      UVM_DEBUG)
end
`endif

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri rst_n_i;

  // Signal list (all signals are capable of being inputs and outputs for the sake
  // of supporting both INITIATOR and RESPONDER mode operation. Expectation is that 
  // directionality in the config file was from the point-of-view of the INITIATOR

  // INITIATOR mode input signals
  tri [AHB_DATA_WIDTH-1:0] hrdata_i;
  reg [AHB_DATA_WIDTH-1:0] hrdata_o = 'bz;
  tri  hreadyout_i;
  reg  hreadyout_o = 'bz;

  // INITIATOR mode output signals
  tri  ecc_rst_n_i;
  reg  ecc_rst_n_o = 'bz;
  tri [AHB_ADDR_WIDTH-1:0] haddr_i;
  reg [AHB_ADDR_WIDTH-1:0] haddr_o = 'bz;
  tri [AHB_DATA_WIDTH-1:0] hwdata_i;
  reg [AHB_DATA_WIDTH-1:0] hwdata_o = 'bz;
  tri  hsel_i;
  reg  hsel_o = 'bz;
  tri  hwrite_i;
  reg  hwrite_o = 'bz;
  tri  hready_i;
  reg  hready_o = 'bz;
  tri [1:0] htrans_i;
  reg [1:0] htrans_o = 'bz;
  tri [2:0] hsize_i;
  reg [2:0] hsize_o = 'bz;
  tri  transaction_flag_out_monitor_i;
  reg  transaction_flag_out_monitor_o = 'bz;
  tri [1:0] test_i;
  reg [1:0] test_o = 'bz;
  tri [1:0] op_i;
  reg [1:0] op_o = 'bz;

  // Bi-directional signals
  

  assign clk_i = bus.clk;
  assign rst_n_i = bus.rst_n;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)
  assign hrdata_i = bus.hrdata;
  assign bus.hrdata = (initiator_responder == RESPONDER) ? hrdata_o : 'bz;
  assign hreadyout_i = bus.hreadyout;
  assign bus.hreadyout = (initiator_responder == RESPONDER) ? hreadyout_o : 'bz;


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.ecc_rst_n = (initiator_responder == INITIATOR) ? ecc_rst_n_o : 'bz;
  assign ecc_rst_n_i = bus.ecc_rst_n;
  assign bus.haddr = (initiator_responder == INITIATOR) ? haddr_o : 'bz;
  assign haddr_i = bus.haddr;
  assign bus.hwdata = (initiator_responder == INITIATOR) ? hwdata_o : 'bz;
  assign hwdata_i = bus.hwdata;
  assign bus.hsel = (initiator_responder == INITIATOR) ? hsel_o : 'bz;
  assign hsel_i = bus.hsel;
  assign bus.hwrite = (initiator_responder == INITIATOR) ? hwrite_o : 'bz;
  assign hwrite_i = bus.hwrite;
  assign bus.hready = (initiator_responder == INITIATOR) ? hready_o : 'bz;
  assign hready_i = bus.hready;
  assign bus.htrans = (initiator_responder == INITIATOR) ? htrans_o : 'bz;
  assign htrans_i = bus.htrans;
  assign bus.hsize = (initiator_responder == INITIATOR) ? hsize_o : 'bz;
  assign hsize_i = bus.hsize;
  assign bus.transaction_flag_out_monitor = (initiator_responder == INITIATOR) ? transaction_flag_out_monitor_o : 'bz;
  assign transaction_flag_out_monitor_i = bus.transaction_flag_out_monitor;
  assign bus.test = (initiator_responder == INITIATOR) ? test_o : 'bz;
  assign test_i = bus.test;
  assign bus.op = (initiator_responder == INITIATOR) ? op_o : 'bz;
  assign op_i = bus.op;

  // Proxy handle to UVM driver
  ECC_in_pkg::ECC_in_driver #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH)
    )
  proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in ECC_in_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from ECC_in_driver to this BFM
  // ****************************************************************************
  `ECC_in_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by ECC_in_driver and ECC_in_driver_bfm
  // to communicate initiator driven data to ECC_in_driver_bfm.           
  `ECC_in_INITIATOR_STRUCT
    ECC_in_initiator_s initiator_struct;
  // Responder macro used by ECC_in_driver and ECC_in_driver_bfm
  // to communicate Responder driven data to ECC_in_driver_bfm.
  `ECC_in_RESPONDER_STRUCT
    ECC_in_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge rst_n_i )
     begin
       // RESPONDER mode output signals
       hrdata_o <= 'bz;
       hreadyout_o <= 'bz;
       // INITIATOR mode output signals
       ecc_rst_n_o <= 'b0;
       haddr_o <= 'bz;
       hwdata_o <= 'bz;
       hsel_o <= 0;
       hwrite_o <= 0;
       hready_o <= 0;
       htrans_o <= 0;
       hsize_o <= 3'b011;

       transaction_flag_out_monitor_o <= '0;
       test_o <= 'bz;
       op_o <= 'bz;
       // Bi-directional signals
 
     end    
// pragma uvmf custom reset_condition_and_response end

  // pragma uvmf custom interface_item_additional begin
  // pragma uvmf custom interface_item_additional end

  //******************************************************************
  // The configure() function is used to pass agent configuration
  // variables to the driver BFM.  It is called by the driver within
  // the agent at the beginning of the simulation.  It may be called 
  // during the simulation if agent configuration variables are updated
  // and the driver BFM needs to be aware of the new configuration 
  // variables.
  //

  function void configure(ECC_in_configuration_s ECC_in_configuration_arg); // pragma tbx xtf  
    initiator_responder = ECC_in_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction                                                                             

// pragma uvmf custom initiate_and_get_response begin
// ****************************************************************************
// UVMF_CHANGE_ME
// This task is used by an initator.  The task first initiates a transfer then
// waits for the responder to complete the transfer.
    task initiate_and_get_response( 
       // This argument passes transaction variables used by an initiator
       // to perform the initial part of a protocol transfer.  The values
       // come from a sequence item created in a sequence.
       input ECC_in_initiator_s ECC_in_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output ECC_in_responder_s ECC_in_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the ECC_in_initiator_struct:
       //   ecc_in_test_transactions test ;
       //   ecc_in_op_transactions op ;
       // Members within the ECC_in_responder_struct:
       //   ecc_in_test_transactions test ;
       //   ecc_in_op_transactions op ;
       initiator_struct = ECC_in_initiator_struct;
       //
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available initiator input and inout signals listed.
       //    Initiator input signals
       //      ECC_in_responder_struct.xyz = hrdata_i;  //    [AHB_DATA_WIDTH-1:0] 
       //      ECC_in_responder_struct.xyz = hreadyout_i;  //     
       //    Initiator inout signals
       //    How to assign a signal from an initiator struct member named xyz.   
       //    All available initiator output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Initiator output signals
       //      ecc_rst_n_o <= ECC_in_initiator_struct.xyz;  //     
       //      haddr_o <= ECC_in_initiator_struct.xyz;  //    [AHB_ADDR_WIDTH-1:0] 
       //      hwdata_o <= ECC_in_initiator_struct.xyz;  //    [AHB_DATA_WIDTH-1:0] 
       //      hsel_o <= ECC_in_initiator_struct.xyz;  //     
       //      hwrite_o <= ECC_in_initiator_struct.xyz;  //     
       //      hready_o <= ECC_in_initiator_struct.xyz;  //     
       //      htrans_o <= ECC_in_initiator_struct.xyz;  //    [1:0] 
       //      hsize_o <= ECC_in_initiator_struct.xyz;  //    [2:0] 
       //      transaction_flag_out_monitor_o <= ECC_in_initiator_struct.xyz;  //     
       //      test_o <= ECC_in_initiator_struct.xyz;  //    [2:0] 
       //      op_o <= ECC_in_initiator_struct.xyz;  //    [2:0] 
       //    Initiator inout signals
    // Initiate a transfer using the data received.
    @(posedge clk_i);
    /*
    $display("** ECC_in_driver_bfm** : Inside initiate_and_get_response");
    $display("** ECC_in_driver_bfm** : test = %0s", ECC_in_initiator_struct.test.name());
    $display("** ECC_in_driver_bfm** : op = %0s", ECC_in_initiator_struct.op.name());
      */
    case (ECC_in_initiator_struct.test)
      ecc_reset_test      : ecc_init(ECC_in_initiator_struct.test, ECC_in_initiator_struct.op);
      ecc_normal_test     : ecc_test(ECC_in_initiator_struct.test, ECC_in_initiator_struct);
      ecc_otf_reset_test  : ecc_test(ECC_in_initiator_struct.test, ECC_in_initiator_struct);
      default             : ecc_test(ECC_in_initiator_struct.test, ECC_in_initiator_struct);
    endcase

  endtask   
  
  // --------------------------------------------
  // anjpar added the following
  // --------------------------------------------
  parameter   TEST_VECTOR_NUM = 15;

  parameter BASE_ADDR        = 32'h00000000;

  parameter ADDR_NAME0       = BASE_ADDR + 32'h00000000;
  parameter ADDR_NAME1       = BASE_ADDR + 32'h00000004;
  parameter ADDR_VERSION0    = BASE_ADDR + 32'h00000008;
  parameter ADDR_VERSION1    = BASE_ADDR + 32'h0000000C;

  parameter ADDR_CTRL        = BASE_ADDR + 32'h00000010;
  parameter KEYGEN_CMD       = 2'b01;
  parameter SIGN_CMD         = 2'b10;
  parameter VERIFY_CMD       = 2'b11;
  parameter DH_SHARED_CMD    = (1 << 4);


  parameter ADDR_STATUS          = BASE_ADDR + 32'h00000018;
  parameter STATUS_READY_BIT = 0;
  parameter STATUS_VALID_BIT = 1;

  parameter ADDR_SEED_START      = BASE_ADDR + 32'h00000080;
  parameter ADDR_SEED_END        = BASE_ADDR + 32'h000000AC;

  parameter ADDR_MSG_START       = BASE_ADDR + 32'h00000100;
  parameter ADDR_MSG_END         = BASE_ADDR + 32'h0000012C;

  localparam ADDR_PRIVKEY_OUT_START   = BASE_ADDR + 32'h00000180;
  localparam ADDR_PRIVKEY_OUT_END     = BASE_ADDR + 32'h000001AC;

  parameter ADDR_PUBKEYX_START   = BASE_ADDR + 32'h00000200;
  parameter ADDR_PUBKEYX_END     = BASE_ADDR + 32'h0000022C;

  parameter ADDR_PUBKEYY_START   = BASE_ADDR + 32'h00000280;
  parameter ADDR_PUBKEYY_END     = BASE_ADDR + 32'h000002AC;

  parameter ADDR_SIGNR_START     = BASE_ADDR + 32'h00000300;
  parameter ADDR_SIGNR_END       = BASE_ADDR + 32'h0000032C;

  parameter ADDR_SIGNS_START     = BASE_ADDR + 32'h00000380;
  parameter ADDR_SIGNS_END       = BASE_ADDR + 32'h000003AC;

  parameter ADDR_VERIFY_R_START  = BASE_ADDR + 32'h00000400;
  parameter ADDR_VERIFY_R_END    = BASE_ADDR + 32'h0000042C;

  parameter ADDR_IV_START        = BASE_ADDR + 32'h00000480;
  parameter ADDR_IV_END          = BASE_ADDR + 32'h000004AC;

  parameter ADDR_NONCE_START     = BASE_ADDR + 32'h00000500;
  parameter ADDR_NONCE_END       = BASE_ADDR + 32'h0000052C;

  localparam ADDR_PRIVKEY_IN_START   = BASE_ADDR + 32'h00000580;
  localparam ADDR_PRIVKEY_IN_END     = BASE_ADDR + 32'h000005AC;

  parameter ADDR_DH_SHARED_KEY_START = BASE_ADDR + 32'h000005C0;
  parameter ADDR_DH_SHARED_KEY_END   = BASE_ADDR + 32'h000005EC;

  // KV control register addresses (see src/ecc/rtl/ecc_reg.rdl).
  parameter ADDR_KV_RD_PKEY_CTRL   = BASE_ADDR + 32'h00000600;
  parameter ADDR_KV_RD_SEED_CTRL   = BASE_ADDR + 32'h00000608;
  parameter ADDR_KV_WR_PKEY_CTRL   = BASE_ADDR + 32'h00000610;
  parameter KV_READ_EN_MASK        = 32'h00000001;
  parameter KV_WRITE_EN_MASK       = 32'h00000001;
  parameter KV_ECC_PKEY_DEST_MASK  = 32'h00000200;

  // ECC_CTRL bit masks (see src/ecc/rtl/ecc_reg.rdl -- ECC_CTRL fields).
  parameter CTRL_ZEROIZE_MASK      = 32'h00000004;
  parameter CTRL_PCR_SIGN_MASK     = 32'h00000008;
  parameter CTRL_CURVE_SEL_MASK    = 32'h00000020;
  parameter CTRL_NONDETERMINISTIC_MASK    = 32'h00000040;

  parameter REG_SIZE      = 384;
  parameter PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  parameter ADD_NUM_ADDS  = 1;
  parameter ADD_BASE_SZ   = 384;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter           R_WIDTH                   = 384;

  typedef bit         [R_WIDTH-1:0]             r_t;
  typedef bit         [383 : 0]                 operand_t;

  typedef struct packed {
      operand_t   x;
      operand_t   y;
  } affn_point_t;

  typedef struct packed {
      operand_t   X;
      operand_t   Y;
      operand_t   Z;
  } proj_point_t;

  typedef struct packed {
      operand_t     hashed_msg;
      operand_t     privkey;
      affn_point_t  pubkey;
      operand_t     R;
      operand_t     S;
      operand_t     seed;
      operand_t     nonce;
      operand_t     IV;
      operand_t     privkeyB;
      operand_t     DH_sharedkey;
  } test_vector_t;

  test_vector_t test_vector;

  reg [31 : 0]  cycle_ctr;

  //reg [31 : 0]  read_data;
  reg [383: 0]  reg_read_data;

  reg [7:0] test_case_num;

  //--------------------
  //Reset task
  //--------------------
  task do_assert_rst();
    begin
      ecc_rst_n_o = 0;
      transaction_flag_out_monitor_o = 0;
      repeat (5) @(posedge clk_i);
      ecc_rst_n_o = 1;
    end
  endtask

  //--------------------
  //Init DUT
  //--------------------
  task ecc_init (
    input ecc_in_test_transactions test,
    input ecc_in_op_transactions op
    );

    $display("%d ***************   Starting Reset", $time);
    test_o = test;
    op_o = op;
    ecc_rst_n_o <= 1'b0;
    transaction_flag_out_monitor_o = 0;
    cycle_ctr = '0;
    test_case_num = '0;

    haddr_o     = 'Z;
    hwdata_o    = 'Z;
    hsel_o      = 0;
    hwrite_o    = 0;
    hready_o    = 0;
    htrans_o    = AHB_HTRANS_IDLE;
    hsize_o     = 3'b011;

    repeat (10) @(posedge clk_i);
    ecc_rst_n_o <= 1'b1;
    repeat (5) @(posedge clk_i);
    transaction_flag_out_monitor_o = 1;

    $display("%d ***************   Ending Reset", $time);
  endtask

  //--------------------
  //Reset Other signals
  //--------------------
  always @(negedge rst_n_i) begin
    ecc_rst_n_o <= 'b0;
    haddr_o <= 'bz;
    hwdata_o <= 'bz;
    hsel_o <= 'b0;
    hwrite_o <= 'b0;
    hready_o <= 'b0;
    htrans_o <= 'b0;
    hsize_o <= 3'b011;
  end

  always @(posedge rst_n_i) begin
	  ecc_rst_n_o = 1;
  end

  //----------------------------------------------------------------
  // sys_monitor()
  //
  // An always running process that creates a cycle counter and
  // conditionally displays information about the DUT.
  //----------------------------------------------------------------
  always
    begin : sys_monitor
      @(posedge clk_i);
      cycle_ctr = cycle_ctr + 1;
    end


  //----------------------------------------------------------------
  // wait_ready()
  //
  // Wait for the ready flag in the dut to be set.
  // (Actually we wait for either ready or valid to be set.)
  //
  // Note: It is the callers responsibility to call the function
  // when the dut is actively processing and will in fact at some
  // point set the flag.
  //----------------------------------------------------------------
    task wait_ready;
      begin
        read_single_word(ADDR_STATUS);
        while (hrdata_i == 0)
          begin
            read_single_word(ADDR_STATUS);
          end
      end
    endtask // wait_ready

    // Wait for STATUS[1]=VALID specifically. wait_ready above returns
    // as soon as any status bit is set, which can be too eager right
    // after a dispatch (ready=1 default lingers a few clocks before the
    // FSM drops it), causing the caller to observe stale outputs.
    task wait_valid;
      begin
        read_single_word(ADDR_STATUS);
        // VALID = bit 1 on either AHB lane depending on addr[2] of
        // STATUS (0x18, bit[2]=0 -> lane 0).
        while (((hrdata_i[31:0] | hrdata_i[63:32]) & 32'h2) == 32'h0)
          begin
            read_single_word(ADDR_STATUS);
          end
      end
    endtask // wait_valid
  

  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word (
    input [31 : 0]  address,
    input [31 : 0] word
    );
    begin
      hsel_o      <= 1;
      haddr_o     <= address;
      hwrite_o    <= 1;
      hready_o    <= 1;
      htrans_o    <= AHB_HTRANS_NONSEQ;
      hsize_o     <= 3'b010;
      
      @(posedge clk_i); 
      haddr_o     <= 'Z;
      hwdata_o    <= address[2] ? {word, 32'h0} : {32'h0, word};
      hwrite_o    <= 0;
      htrans_o    <= AHB_HTRANS_IDLE;
      wait(hreadyout_i == 1'b1);

      @(posedge clk_i);
      hsel_o      <= 0;
    end
  endtask // write_single_word

  //----------------------------------------------------------------
  // write_block()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block (
    input [31 : 0] addr, 
    input [383 : 0] block
    );
    begin
      write_single_word(addr,      block[383  : 352]);
      write_single_word(addr+4*1,  block[351  : 320]);
      write_single_word(addr+4*2,  block[319  : 288]);
      write_single_word(addr+4*3,  block[287  : 256]);
      write_single_word(addr+4*4,  block[255  : 224]);
      write_single_word(addr+4*5,  block[223  : 192]);
      write_single_word(addr+4*6,  block[191  : 160]);
      write_single_word(addr+4*7,  block[159  : 128]);
      write_single_word(addr+4*8,  block[127  :  96]);
      write_single_word(addr+4*9,  block[95   :  64]);
      write_single_word(addr+4*10, block[63   :  32]);
      write_single_word(addr+4*11, block[31   :   0]);
    end
  endtask // write_block

  //----------------------------------------------------------------
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word (
    input [31 : 0]  address
    );
    begin
      hsel_o       <= 1;    
      haddr_o      <= address;
      hwrite_o     <= 0;
      hready_o     <= 1;
      htrans_o     <= AHB_HTRANS_NONSEQ;
      hsize_o      <= 3'b010;
      
      @(posedge clk_i);
      hwdata_o     <= 0;
      haddr_o      <= 'Z;
      htrans_o     <= AHB_HTRANS_IDLE;
      wait(hreadyout_i == 1'b1);

      @(posedge clk_i);
      hsel_o      <= 0;
    end
  endtask // read_single_word
  
  //----------------------------------------------------------------
  // read_block()
  //
  // Read the digest in the dut. The resulting digest will be
  // available in the global variable digest_data.
  //----------------------------------------------------------------
  task read_block (
    input [31 : 0] addr
    );
    begin
      // 32-bit dword lands on lane 0 or lane 1 of the 64-bit hrdata
      // bus based on addr[2]; other lane is zero. OR both lanes to
      // recover the dword regardless (matches ECC_out_pkg hrdata_32).
      read_single_word(addr);
      reg_read_data[383 : 352] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr + 4*1);
      reg_read_data[351 : 320] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*2);
      reg_read_data[319 : 288] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*3);
      reg_read_data[287 : 256] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*4);
      reg_read_data[255 : 224] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*5);
      reg_read_data[223 : 192] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*6);
      reg_read_data[191 : 160] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*7);
      reg_read_data[159 : 128] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*8);
      reg_read_data[127 :  96] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*9);
      reg_read_data[95  :  64] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*10);
      reg_read_data[63  :  32] = hrdata_i[31:0] | hrdata_i[63:32];
      read_single_word(addr +  4*11);
      reg_read_data[31  :   0] = hrdata_i[31:0] | hrdata_i[63:32];
    end
  endtask // read_digest

  //----------------------------------------------------------------
  // trig_ECC()
  //----------------------------------------------------------------
  task trig_ECC(input [31 : 0] cmd);
    begin
      write_single_word(ADDR_CTRL  , cmd);
      repeat (10) @(posedge clk_i);
      write_single_word(ADDR_CTRL  , 0);
    end
  endtask // trig_ECC

  //----------------------------------------------------------------
  // ecc_keygen_test()
  //
  // Perform a single point multiplication block test.
  //----------------------------------------------------------------
  task ecc_keygen_test (
    input test_vector_t test_vector,
    input               test_otf_reset
  );
    
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    reg [383 : 0]   privkey;
    affn_point_t    pubkey;
    
    begin
      wait_ready();

      
      start_time = cycle_ctr;
      write_block(ADDR_SEED_START, test_vector.seed);
      write_block(ADDR_NONCE_START, test_vector.nonce);
      write_block(ADDR_IV_START, test_vector.IV);

      trig_ECC(KEYGEN_CMD);
      @(posedge clk_i);

      if (!test_otf_reset) // regular operation
        wait_ready();
      else begin
        //Toggle OTF reset
        @(posedge clk_i);
        ecc_rst_n_o = 1'b0;
        repeat (2) @(posedge clk_i);
        ecc_rst_n_o = 1'b1;
      end

      transaction_flag_out_monitor_o = 1'b1;
      @(posedge clk_i);
      transaction_flag_out_monitor_o = 1'b0;
      @(posedge clk_i); 

      read_block(ADDR_PRIVKEY_OUT_START);
      privkey = reg_read_data;

      read_block(ADDR_PUBKEYX_START);
      pubkey.x = reg_read_data;

      read_block(ADDR_PUBKEYY_START);
      pubkey.y = reg_read_data;

      end_time = cycle_ctr - start_time;

      //$display("*** keygen test processing time = %01d cycles.", end_time);
      /*      
      if (!test_otf_reset) begin 
        $display("@ %0t privkey    : 0x%96x", $time, test_vector.privkey);

        if ((privkey == test_vector.privkey) & (pubkey == test_vector.pubkey)) begin
          $display("");
        end
        else begin
          $display("Expected_x: 0x%96x", test_vector.pubkey.x);
          $display("Got:        0x%96x", pubkey.x);
          $display("Expected_y: 0x%96x", test_vector.pubkey.y);
          $display("Got:        0x%96x", pubkey.y);
          $display("");
        end
      end
      */
    end
  endtask // ecc_keygen_test

  //----------------------------------------------------------------
  // ecc_signing_test()
  //
  // Perform a single signing operation test.
  //----------------------------------------------------------------
  task ecc_signing_test (
    input test_vector_t test_vector,
    input               test_otf_reset
  );

    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    reg [383 : 0]   R;
    reg [383 : 0]   S;

    begin
      wait_ready();

      
      start_time = cycle_ctr;

      write_block(ADDR_MSG_START, test_vector.hashed_msg);
      write_block(ADDR_PRIVKEY_IN_START, test_vector.privkey);
      write_block(ADDR_IV_START, test_vector.IV);

      trig_ECC(SIGN_CMD);
      @(posedge clk_i);

      if (!test_otf_reset) // regular operation
        wait_ready();
      else begin
        //Toggle OTF reset
        @(posedge clk_i);
        ecc_rst_n_o = 1'b0;
        repeat (2) @(posedge clk_i);
        ecc_rst_n_o = 1'b1;
      end
      
      transaction_flag_out_monitor_o = 1'b1;
      @(posedge clk_i);
      transaction_flag_out_monitor_o = 1'b0;
      @(posedge clk_i); 
      
      read_block(ADDR_SIGNR_START);
      R = reg_read_data;

      read_block(ADDR_SIGNS_START);
      S = reg_read_data;

      end_time = cycle_ctr - start_time;
      //$display("*** signing test processing time = %01d cycles.", end_time);

      /*
      if (!test_otf_reset) begin
        $display("@ %0t privkey    : 0x%96x", $time, test_vector.privkey);

        if (R == test_vector.R & S == test_vector.S) begin
          $display("");
        end
        else begin
          $display("Expected_R: 0x%96x", test_vector.R);
          $display("Got:        0x%96x", R);
          $display("Expected_S: 0x%96x", test_vector.S);
          $display("Got:        0x%96x", S);
          $display("");
        end
      end
      */
    end
  endtask // ecc_signing_test

  //----------------------------------------------------------------
  // ecc_verifying_test()
  //
  // Perform a single verifying operation test.
  //----------------------------------------------------------------
  task ecc_verifying_test (
    input test_vector_t test_vector,
    input               test_otf_reset
  );
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    reg [383 : 0]    verify_r;

    begin
      wait_ready();


      start_time = cycle_ctr;

      write_block(ADDR_MSG_START, test_vector.hashed_msg);
      write_block(ADDR_PUBKEYX_START, test_vector.pubkey.x);
      write_block(ADDR_PUBKEYY_START, test_vector.pubkey.y);
      write_block(ADDR_SIGNR_START, test_vector.R);
      write_block(ADDR_SIGNS_START, test_vector.S);
      write_block(ADDR_IV_START, 384'h1);

      trig_ECC(VERIFY_CMD);
      @(posedge clk_i);

      if (!test_otf_reset) // regular operation
        wait_ready();
      else begin
        //Toggle OTF reset
        @(posedge clk_i);
        ecc_rst_n_o = 1'b0;
        repeat (2) @(posedge clk_i);
        ecc_rst_n_o = 1'b1;
      end

      transaction_flag_out_monitor_o = 1'b1;
      @(posedge clk_i);
      transaction_flag_out_monitor_o = 1'b0;
      @(posedge clk_i); 

      read_block(ADDR_VERIFY_R_START);
      verify_r = reg_read_data;

      end_time = cycle_ctr - start_time;
      //$display("*** verifying test processing time = %01d cycles.", end_time);

      /*
      if (!test_otf_reset) begin
        $display("@ %0t privkey    : 0x%96x", $time, test_vector.privkey);

        if (verify_r == test_vector.R)
        begin
          $display("");
        end
        else
        begin
          $display("Expected_R: 0x%96x", test_vector.R);
          $display("Got:        0x%96x", verify_r);
          $display("");
        end
      end
      */
    end
  endtask // ecc_verifying_test

  task ecc_DH_sharedkey_test (
    input test_vector_t test_vector,
    input               test_otf_reset
  );
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    operand_t       DH_sharedkey;

    begin
      wait_ready();


      start_time = cycle_ctr;

      // write_block(ADDR_MSG_START, test_vector.hashed_msg);
      write_block(ADDR_PRIVKEY_IN_START, test_vector.privkeyB);
      write_block(ADDR_PUBKEYX_START, test_vector.pubkey.x);
      write_block(ADDR_PUBKEYY_START, test_vector.pubkey.y);
      write_block(ADDR_IV_START, test_vector.IV);

      trig_ECC(DH_SHARED_CMD);
      @(posedge clk_i);

      if (!test_otf_reset) // regular operation
        wait_ready();
      else begin
        //Toggle OTF reset
        @(posedge clk_i);
        ecc_rst_n_o = 1'b0;
        repeat (2) @(posedge clk_i);
        ecc_rst_n_o = 1'b1;
      end

      transaction_flag_out_monitor_o = 1'b1;
      @(posedge clk_i);
      transaction_flag_out_monitor_o = 1'b0;
      @(posedge clk_i); 

      read_block(ADDR_DH_SHARED_KEY_START);
      DH_sharedkey = reg_read_data;

      // trig_ECC()

      end_time = cycle_ctr - start_time;
    end
  endtask

  //----------------------------------------------------------------
  // check_field()
  //
  // Compare 384b actual against 384b expected; uvm_error on mismatch.
  // For P-256 the DUT scrubs the upper 128b (curve-native), so the
  // expected is masked to lower 256b regardless of whether the caller
  // polluted test_vector's upper bits.
  //----------------------------------------------------------------
  task check_field (input bit [383:0] got, input bit [383:0] exp,
                    input ecc_in_curve_e curve, input string name);
    bit [383:0] exp_masked;
    begin
      exp_masked = (curve == ecc_curve_p256) ? {128'h0, exp[255:0]} : exp;
      if (got !== exp_masked) begin
        `uvm_error("ECC_BFM", $sformatf("%s MISMATCH: expected 0x%096h, got 0x%096h", name, exp_masked, got))
      end else begin
        `uvm_info("ECC_BFM", $sformatf("%s CHECK OK: 0x%096h", name, got), UVM_LOW)
      end
    end
  endtask

  //----------------------------------------------------------------
  // check_op_output()
  //
  // Read DUT output block(s) for the given op and compare against the
  // exe-provided fresh KAT (in test_vector). Only meaningful when the
  // op completes deterministically (legal det: KEYGEN, non-nondet SIGN,
  // VERIFY, ECDH). Nondet SIGN, err, otf-reset, zeroize paths call
  // read_op_output instead (no check).
  //----------------------------------------------------------------
  task check_op_output (input ecc_in_op_transactions op, input ecc_in_curve_e curve);
    begin
      case (op)
        key_gen : begin
          read_block(ADDR_PRIVKEY_OUT_START);
          check_field(reg_read_data, test_vector.privkey,  curve, "privkey_out");
          read_block(ADDR_PUBKEYX_START);
          check_field(reg_read_data, test_vector.pubkey.x, curve, "pubkey_x");
          read_block(ADDR_PUBKEYY_START);
          check_field(reg_read_data, test_vector.pubkey.y, curve, "pubkey_y");
        end
        key_sign : begin
          read_block(ADDR_SIGNR_START);
          check_field(reg_read_data, test_vector.R, curve, "sign_R");
          read_block(ADDR_SIGNS_START);
          check_field(reg_read_data, test_vector.S, curve, "sign_S");
        end
        key_verify : begin
          read_block(ADDR_VERIFY_R_START);
          check_field(reg_read_data, test_vector.R, curve, "verify_R");
        end
        ecdh_sharedkey : begin
          read_block(ADDR_DH_SHARED_KEY_START);
          check_field(reg_read_data, test_vector.DH_sharedkey, curve, "DH_sharedkey");
        end
        default : ;
      endcase
    end
  endtask

  //----------------------------------------------------------------
  // check_zero_outputs()
  //
  // Verify that all sensitive output CSRs read as 0. Used after
  // zeroize-mid-op and OTF-reset paths to confirm the DUT cleared
  // its outputs (the zeroize / reset contract).
  //----------------------------------------------------------------
  task check_zero_outputs (input string ctx);
    begin
      read_block(ADDR_PRIVKEY_OUT_START);
      check_field(reg_read_data, '0, ecc_curve_p384, {ctx, ":privkey_out"});
      read_block(ADDR_PUBKEYX_START);
      check_field(reg_read_data, '0, ecc_curve_p384, {ctx, ":pubkey_x"});
      read_block(ADDR_PUBKEYY_START);
      check_field(reg_read_data, '0, ecc_curve_p384, {ctx, ":pubkey_y"});
      read_block(ADDR_SIGNR_START);
      check_field(reg_read_data, '0, ecc_curve_p384, {ctx, ":sign_R"});
      read_block(ADDR_SIGNS_START);
      check_field(reg_read_data, '0, ecc_curve_p384, {ctx, ":sign_S"});
      read_block(ADDR_VERIFY_R_START);
      check_field(reg_read_data, '0, ecc_curve_p384, {ctx, ":verify_R"});
      read_block(ADDR_DH_SHARED_KEY_START);
      check_field(reg_read_data, '0, ecc_curve_p384, {ctx, ":DH_sharedkey"});
    end
  endtask

  //----------------------------------------------------------------
  // verify_signature()
  //
  // Dispatch an RTL VERIFY on the given (R, S) using the current
  // test_vector's (msg, pubkey). Reads back verify_R and checks
  // verify_R == R (the ECDSA validity condition). Used for nondet
  // SIGN self-check: any valid signature must satisfy this
  // regardless of the k value the DRBG produced.
  //----------------------------------------------------------------
  task verify_signature (input bit [383:0] R_got, input bit [383:0] S_got,
                         input ecc_in_curve_e curve, input string ctx);
    bit [31:0] cmd_word;
    begin
      // Give the SIGN op time to fully complete (ready should be up).
      wait_ready();
      write_block(ADDR_MSG_START,     test_vector.hashed_msg);
      write_block(ADDR_PUBKEYX_START, test_vector.pubkey.x);
      write_block(ADDR_PUBKEYY_START, test_vector.pubkey.y);
      write_block(ADDR_SIGNR_START,   R_got);
      write_block(ADDR_SIGNS_START,   S_got);
      write_block(ADDR_IV_START,      384'h1);
      cmd_word = VERIFY_CMD | ((curve == ecc_curve_p256) ? CTRL_CURVE_SEL_MASK : 0);
      write_single_word(ADDR_CTRL, cmd_word);
      @(posedge clk_i);
      hsel_o <= 0;
      @(posedge clk_i);
      wait_valid();
      read_block(ADDR_VERIFY_R_START);
      check_field(reg_read_data, R_got, curve,
                  {ctx, ":nondet_self_verify_R"});
    end
  endtask

  //----------------------------------------------------------------
  // drbg_force_p256 / drbg_release_p256
  //
  // Force the P-256 HMAC-DRBG wrapper's output to a known k value so
  // the RTL bit-matches the pre-baked nondet KAT's R,S. Used only for
  // P-256 nondet SIGN. Mirrors ecc_top_tb::drbg_bypass_force.
  //----------------------------------------------------------------
  task drbg_force_p256 (input bit [255:0] k_val);
    begin
      force hdl_top.dut.ecc_dsa_ctrl_i.hmac_drbg_result_p256 = k_val;
      force hdl_top.dut.ecc_dsa_ctrl_i.lambda_p256           = 256'd1;
      force hdl_top.dut.ecc_dsa_ctrl_i.scalar_rnd_p256       = '0;
      force hdl_top.dut.ecc_dsa_ctrl_i.masking_rnd_p256      = '0;
    end
  endtask

  task drbg_release_p256 ();
    begin
      release hdl_top.dut.ecc_dsa_ctrl_i.hmac_drbg_result_p256;
      release hdl_top.dut.ecc_dsa_ctrl_i.lambda_p256;
      release hdl_top.dut.ecc_dsa_ctrl_i.scalar_rnd_p256;
      release hdl_top.dut.ecc_dsa_ctrl_i.masking_rnd_p256;
    end
  endtask

  //----------------------------------------------------------------
  // drbg_force_p384 / drbg_release_p384
  //
  // Force the P-384 HMAC-DRBG output to a known k, bypassing the RTL
  // DRBG's SIGN_NONCE_ST whitening stage. Also short-circuits the
  // DRBG wait via hmac_ready_p384=1 so the FSM doesn't stall waiting
  // for the (bypassed) DRBG. Used for P-384 nondet SIGN so R,S
  // bit-exactly match the pre-computed nondet KAT (k from privkeyB
  // slot, injected by gen_nondet_kat.py's _HmacDrbgSha384). Mirrors
  // ecc_top_tb::drbg_bypass_force_p384.
  //----------------------------------------------------------------
  task drbg_force_p384 (input bit [383:0] k_val);
    begin
      force hdl_top.dut.ecc_dsa_ctrl_i.hmac_drbg_result_p384 = k_val;
      force hdl_top.dut.ecc_dsa_ctrl_i.lambda_p384           = {{(384-1){1'b0}}, 1'b1};
      force hdl_top.dut.ecc_dsa_ctrl_i.scalar_rnd_p384       = '0;
      force hdl_top.dut.ecc_dsa_ctrl_i.masking_rnd_p384      = '0;
      force hdl_top.dut.ecc_dsa_ctrl_i.hmac_ready_p384       = 1'b1;
    end
  endtask

  task drbg_release_p384 ();
    begin
      release hdl_top.dut.ecc_dsa_ctrl_i.hmac_drbg_result_p384;
      release hdl_top.dut.ecc_dsa_ctrl_i.lambda_p384;
      release hdl_top.dut.ecc_dsa_ctrl_i.scalar_rnd_p384;
      release hdl_top.dut.ecc_dsa_ctrl_i.masking_rnd_p384;
      release hdl_top.dut.ecc_dsa_ctrl_i.hmac_ready_p384;
    end
  endtask

  //----------------------------------------------------------------
  // ecc_test()
  //
  // Dispatch entry. Legacy P-384-det path preserved for backward compat
  // with ECC_normal_test / ECC_otf_reset_test; new random axes are
  // handled by ecc_random_test which selects curve/mode-aware KAT and
  // drives ECC_CTRL with CURVE_SEL / NONDETERMINISTIC / PCR_SIGN.
  //----------------------------------------------------------------
  task ecc_test (
    input ecc_in_test_transactions test,
    input ECC_in_initiator_s       istruct
  );
    string    file_name;
    reg       test_otf_reset;

    begin

      // pass op and selection to monitor
      transaction_flag_out_monitor_o = 1'b0;
      test_o = test;
      op_o = istruct.op;

      test_case_num++;

      if (test == ecc_normal_test)
        test_otf_reset = 0;
      else if (test == ecc_otf_reset_test)
        test_otf_reset = 1;

      // Any non-default random axis routes to the random-test path.
      if ((istruct.curve   != ecc_curve_p384) ||
          (istruct.err_mode != ERR_NONE)      ||
          (istruct.nondet != 1'b0)         ||
          (istruct.pcr_sign  != 1'b0)         ||
          (istruct.kv_intf   != 1'b0)         ||
          (istruct.pollute_upper != 1'b0)     ||
          (istruct.zeroize_mid_op != 1'b0)) begin
        ecc_random_test(istruct, test_otf_reset);
        return;
      end

      // Legacy path: P-384 det, single-TC KAT freshly generated on each call.
      $system("./ecc_secp384r1.exe");
      file_name = "secp384_testvector.hex";
      read_test_vectors(file_name);

      if (istruct.op == key_gen)
        ecc_keygen_test(test_vector, test_otf_reset);
      else if (istruct.op == key_sign)
        ecc_signing_test(test_vector, test_otf_reset);
      else if (istruct.op == key_verify)
        ecc_verifying_test(test_vector, test_otf_reset);
      else if (istruct.op == ecdh_sharedkey)
        ecc_DH_sharedkey_test(test_vector, test_otf_reset);
    end
  endtask // ecc_test

  //----------------------------------------------------------------
  // ecc_random_test()
  //
  // Random-axes dispatch: selects the right KAT hex (per curve, per
  // det/nondet), optionally pollutes P-256 upper 4 dwords, and arms
  // the illegal combination when err_mode != NONE.
  //
  // Output monitor is NEVER armed on the random path -- the existing
  // out-monitor is timing-fragile (fixed 2-clk sample cadence vs the
  // AHB read's variable cadence) and only reliably follows the legacy
  // path. UVM random tests here own stimulus + coverage; correctness
  // checking is delegated to the shared ecc_top_cov_if.sv + block-TB
  // KAT compares + SVAs. Predictor mirrors this by skipping emit for
  // any transaction with a non-default new axis so scoreboard queues
  // stay balanced.
  //----------------------------------------------------------------
  task ecc_random_test (
    input ECC_in_initiator_s istruct,
    input bit                test_otf_reset
  );
    bit [31:0] cmd_word;
    bit        is_p256;
    bit        is_nondet;
    bit        is_err;
    bit        drbg_forced;   // track SV-force so we can always release
    begin
      // Backdoor test/op signals -- kept updated for the ECC_in monitor
      // and out-monitor even though our path leaves the flag low.
      test_o = istruct.test;
      op_o   = istruct.op;
      transaction_flag_out_monitor_o = 1'b0;
      test_case_num++;
      drbg_forced = 1'b0;

      is_p256   = (istruct.curve == ecc_curve_p256);
      is_nondet = istruct.nondet;
      is_err    = (istruct.err_mode != ERR_NONE);

      // Load KAT.
      //   * Det: run the per-curve exe once to get a fresh single-TC
      //     KAT (msg, privkey, seed, nonce, pubkey, IV) -- every
      //     random seed produces distinct inputs.
      //   * Nondet: same exe first, then post-process via Python
      //     make_nondet_kat.py which derives k = HMAC-DRBG-SHA{256,
      //     384}(seed, nonce) and recomputes (R,S) = ECDSA(msg, priv,
      //     k) so KAT R,S is bit-exact for the k that the BFM SV-forces
      //     into hmac_drbg_result_p{256,384} at dispatch.
      if (is_p256) begin
        $system("./ecc_secp256r1.exe");
        if (is_nondet) begin
          $system("./make_nondet_kat.py secp256_testvector.hex secp256_nondet_kat.hex");
          read_test_vectors("secp256_nondet_kat.hex");
        end else begin
          read_test_vectors("secp256_testvector.hex");
        end
      end
      else begin
        $system("./ecc_secp384r1.exe");
        if (is_nondet) begin
          $system("./make_nondet_kat.py secp384_testvector.hex secp384_nondet_kat.hex");
          read_test_vectors("secp384_nondet_kat.hex");
        end else begin
          read_test_vectors("secp384_testvector.hex");
        end
      end

      wait_ready();

      // Arm KV control regs for the KV-error subtests. No actual KV
      // entry is required; the error latches at dispatch.
      if (istruct.err_mode == ERR_KV_P256 || istruct.err_mode == ERR_KV_RAND_K)
        arm_kv_illegal(istruct.kv_slot, istruct.op);

      // For P-256, upper 4 dwords are curve-native zeros; upper-word
      // pollution asks the DUT to scrub them (positive-control on the
      // per-op P-256 scrub pulse).
      if (is_p256 && istruct.pollute_upper) begin
        test_vector.hashed_msg[REG_SIZE-1:256] = {4{32'hDEADBEEF}};
        test_vector.privkey[REG_SIZE-1:256]    = {4{32'hDEADBEEF}};
        test_vector.pubkey.x[REG_SIZE-1:256]   = {4{32'hDEADBEEF}};
        test_vector.pubkey.y[REG_SIZE-1:256]   = {4{32'hDEADBEEF}};
        test_vector.seed[REG_SIZE-1:256]       = {4{32'hDEADBEEF}};
        test_vector.nonce[REG_SIZE-1:256]      = {4{32'hDEADBEEF}};
        test_vector.IV[REG_SIZE-1:256]         = {4{32'hDEADBEEF}};
        test_vector.privkeyB[REG_SIZE-1:256]   = {4{32'hDEADBEEF}};
      end

      // Build CTRL command word (base op + curve/rand_k/pcr bits).
      case (istruct.op)
        key_gen         : cmd_word = KEYGEN_CMD;
        key_sign        : cmd_word = SIGN_CMD;
        key_verify      : cmd_word = VERIFY_CMD;
        ecdh_sharedkey  : cmd_word = DH_SHARED_CMD;
        default         : cmd_word = KEYGEN_CMD;
      endcase
      if (is_p256)           cmd_word = cmd_word | CTRL_CURVE_SEL_MASK;
      if (istruct.nondet) cmd_word = cmd_word | CTRL_NONDETERMINISTIC_MASK;
      if (istruct.pcr_sign)  cmd_word = cmd_word | CTRL_PCR_SIGN_MASK;

      // Drive operand CSRs then dispatch.
      write_operands(istruct.op);
      // For nondet SIGN (both curves), force hmac_drbg_result to the
      // KAT's pre-computed k in privkeyB, bypassing the RTL DRBG
      // (P-256: temp wrapper; P-384: SIGN_NONCE_ST whitening) so R,S
      // become deterministic and bit-exact match the KAT. Released
      // unconditionally at end of txn regardless of which path taken.
      if (is_nondet && istruct.op == key_sign) begin
        if (is_p256)
          drbg_force_p256(test_vector.privkeyB[255:0]);
        else
          drbg_force_p384(test_vector.privkeyB);
        drbg_forced = 1'b1;
      end
      write_single_word(ADDR_CTRL, cmd_word);
      @(posedge clk_i);
      hsel_o <= 0;
      @(posedge clk_i);

      if (is_err) begin
        // Wait for error_flag to latch.
        wait_for_error_or_timeout(2000);
      end
      else if (istruct.zeroize_mid_op) begin
        // Zeroize-mid-op: wait N clocks after dispatch (op is mid-flight,
        // ready=0), then fire the ZEROIZE cmd bit. Then wait a bit for
        // the FSM to snap back to ECC_RESET and ready to reassert.
        // After zeroize completes, all sensitive outputs must be 0.
        repeat (istruct.zeroize_delay_clks + 1) @(posedge clk_i);
        write_single_word(ADDR_CTRL, CTRL_ZEROIZE_MASK);
        @(posedge clk_i);
        hsel_o <= 0;
        wait_ready();
        check_zero_outputs("zeroize_mid_op");
      end
      else begin
        if (!test_otf_reset) begin
          wait_valid();
        end
        else begin
          @(posedge clk_i);
          ecc_rst_n_o = 1'b0;
          repeat (2) @(posedge clk_i);
          ecc_rst_n_o = 1'b1;
          repeat (10) @(posedge clk_i);
        end
        // After completion, check the outputs.
        //   * Legal det op   -> compare against fresh KAT from the exe.
        //   * Nondet SIGN    -> forced k means (R,S) must bit-exactly
        //                       match the pre-baked nondet KAT (works
        //                       for both curves; P-384 k pre-computed
        //                       by gen_nondet_kat.py's HMAC-DRBG-SHA384
        //                       into privkeyB slot).
        //   * OTF-reset      -> all outputs zeroed.
        if (test_otf_reset) begin
          check_zero_outputs("otf_reset");
        end
        else begin
          check_op_output(istruct.op, istruct.curve);
        end
      end

      // Always release the DRBG force at end of txn so it can't leak
      // into the next transaction regardless of which path was taken.
      if (drbg_forced) begin
        if (is_p256)
          drbg_release_p256();
        else
          drbg_release_p384();
      end
    end
  endtask // ecc_random_test

  //----------------------------------------------------------------
  // write_operands()
  //
  // Op-specific operand-CSR writes; shared by legacy and random paths.
  //----------------------------------------------------------------
  task write_operands (input ecc_in_op_transactions op);
    begin
      case (op)
        key_gen : begin
          write_block(ADDR_SEED_START,  test_vector.seed);
          write_block(ADDR_NONCE_START, test_vector.nonce);
          write_block(ADDR_IV_START,    test_vector.IV);
        end
        key_sign : begin
          write_block(ADDR_MSG_START,        test_vector.hashed_msg);
          write_block(ADDR_PRIVKEY_IN_START, test_vector.privkey);
          write_block(ADDR_IV_START,         test_vector.IV);
          // Nondet SIGN also consumes SEED/NONCE for the DRBG entropy.
          write_block(ADDR_SEED_START,       test_vector.seed);
          write_block(ADDR_NONCE_START,      test_vector.nonce);
        end
        key_verify : begin
          write_block(ADDR_MSG_START,     test_vector.hashed_msg);
          write_block(ADDR_PUBKEYX_START, test_vector.pubkey.x);
          write_block(ADDR_PUBKEYY_START, test_vector.pubkey.y);
          write_block(ADDR_SIGNR_START,   test_vector.R);
          write_block(ADDR_SIGNS_START,   test_vector.S);
          write_block(ADDR_IV_START,      384'h1);
        end
        ecdh_sharedkey : begin
          write_block(ADDR_PRIVKEY_IN_START, test_vector.privkeyB);
          write_block(ADDR_PUBKEYX_START,    test_vector.pubkey.x);
          write_block(ADDR_PUBKEYY_START,    test_vector.pubkey.y);
          write_block(ADDR_IV_START,         test_vector.IV);
        end
        default : ;
      endcase
    end
  endtask

  //----------------------------------------------------------------
  // read_op_output()
  //
  // Op-specific output-CSR reads; keeps hrdata visible to the out-monitor.
  //----------------------------------------------------------------
  task read_op_output (input ecc_in_op_transactions op);
    begin
      case (op)
        key_gen : begin
          read_block(ADDR_PRIVKEY_OUT_START);
          read_block(ADDR_PUBKEYX_START);
          read_block(ADDR_PUBKEYY_START);
        end
        key_sign : begin
          read_block(ADDR_SIGNR_START);
          read_block(ADDR_SIGNS_START);
        end
        key_verify : begin
          read_block(ADDR_VERIFY_R_START);
        end
        ecdh_sharedkey : begin
          read_block(ADDR_DH_SHARED_KEY_START);
        end
        default : ;
      endcase
    end
  endtask

  //----------------------------------------------------------------
  // arm_kv_illegal()
  //
  // Programs one of the ECC_KV_*_CTRL registers with read_en/write_en=1
  // to fire kv_under_p256_invalid / kv_under_nondet_invalid at dispatch.
  //----------------------------------------------------------------
  task arm_kv_illegal (input bit [4:0] slot, input ecc_in_op_transactions op);
    bit [31:0] v;
    begin
      v = KV_READ_EN_MASK | ({27'h0, slot} << 1);
      if (op == key_gen)
        write_single_word(ADDR_KV_RD_SEED_CTRL, v);
      else if (op == key_sign)
        write_single_word(ADDR_KV_RD_PKEY_CTRL, v);
      else
        write_single_word(ADDR_KV_WR_PKEY_CTRL, KV_WRITE_EN_MASK | ({27'h0, slot} << 1) | KV_ECC_PKEY_DEST_MASK);
      @(posedge clk_i);
      hsel_o <= 0;
      @(posedge clk_i);
    end
  endtask

  //----------------------------------------------------------------
  // wait_for_error_or_timeout()
  //
  // Poll ecc_dsa_ctrl_i.error_flag via absolute hierarchical path from
  // inside hdl_top. Returns when error_flag is high. Fires uvm_error
  // if the expected error does not assert within max_clocks.
  //----------------------------------------------------------------
  task wait_for_error_or_timeout (input int max_clocks);
    int i;
    begin
      for (i = 0; i < max_clocks; i++) begin
        if (hdl_top.dut.ecc_dsa_ctrl_i.error_flag ||
            hdl_top.dut.ecc_dsa_ctrl_i.error_flag_reg) begin
          `uvm_info("ECC_BFM", $sformatf("error_flag asserted after %0d clocks", i), UVM_MEDIUM)
          return;
        end
        @(posedge clk_i);
      end
      `uvm_error("ECC_BFM", $sformatf("Expected error_flag did not assert within %0d clocks", max_clocks))
    end
  endtask

  task read_test_vectors (
    input string fname
  );
    integer values_per_test_vector;
    integer line_cnt;
    integer fin;
    integer rv;
    r_t val;    // must be the largest width of any possible value

    int fd_r;
    
    string line_read;
    
    begin

      // ATTN: Must match the number of fields generated by gen_mm_test_vectors.py script
      values_per_test_vector = 11;

      fd_r = $fopen(fname, "r");
      if (fd_r == 0)
        `uvm_fatal("ECC_BFM", $sformatf("Cannot open KAT file %s", fname))
  
      // Get hashed message, private key, public key x, public key y, k and R
      $fgets(line_read, fd_r);  
      $sscanf(line_read, "%h", test_vector.hashed_msg);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.privkey);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.pubkey.x);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.pubkey.y);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.seed);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.nonce);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.R);
      $fgets(line_read, fd_r); 
      $sscanf(line_read, "%h", test_vector.S);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.IV);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.privkeyB);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", test_vector.DH_sharedkey);

      $fclose(fd_r);

    end
  endtask


// pragma uvmf custom initiate_and_get_response end

// pragma uvmf custom respond_and_wait_for_next_transfer begin
// ****************************************************************************
// The first_transfer variable is used to prevent completing a transfer in the 
// first call to this task.  For the first call to this task, there is not
// current transfer to complete.
bit first_transfer=1;

// UVMF_CHANGE_ME
// This task is used by a responder.  The task first completes the current 
// transfer in progress then waits for the initiator to start the next transfer.
  task respond_and_wait_for_next_transfer( 
       // This argument is used to send data received from the initiator
       // back to the sequence item.  The sequence determines how to respond.
       output ECC_in_initiator_s ECC_in_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input ECC_in_responder_s ECC_in_responder_struct 
       );// pragma tbx xtf   
  // Variables within the ECC_in_initiator_struct:
  //   ecc_in_test_transactions test ;
  //   ecc_in_op_transactions op ;
  // Variables within the ECC_in_responder_struct:
  //   ecc_in_test_transactions test ;
  //   ecc_in_op_transactions op ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      ECC_in_responder_struct.xyz = ecc_rst_n_i;  //     
       //      ECC_in_responder_struct.xyz = haddr_i;  //    [AHB_ADDR_WIDTH-1:0] 
       //      ECC_in_responder_struct.xyz = hwdata_i;  //    [AHB_DATA_WIDTH-1:0] 
       //      ECC_in_responder_struct.xyz = hsel_i;  //     
       //      ECC_in_responder_struct.xyz = hwrite_i;  //     
       //      ECC_in_responder_struct.xyz = hready_i;  //     
       //      ECC_in_responder_struct.xyz = htrans_i;  //    [1:0] 
       //      ECC_in_responder_struct.xyz = hsize_i;  //    [2:0] 
       //      ECC_in_responder_struct.xyz = transaction_flag_out_monitor_i;  //     
       //      ECC_in_responder_struct.xyz = test_i;  //    [2:0] 
       //      ECC_in_responder_struct.xyz = op_i;  //    [1:0] 
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //      hrdata_o <= ECC_in_initiator_struct.xyz;  //    [AHB_DATA_WIDTH-1:0] 
       //      hreadyout_o <= ECC_in_initiator_struct.xyz;  //     
       //    Responder inout signals
    
  @(posedge clk_i);
  if (!first_transfer) begin
    // Perform transfer response here.   
    // Reply using data recieved in the ECC_in_responder_struct.
    @(posedge clk_i);
    // Reply using data recieved in the transaction handle.
    @(posedge clk_i);
  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the ECC_in_initiator_struct.
    @(posedge clk_i);
    @(posedge clk_i);
    first_transfer = 0;
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end


// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

package mbox_csr_pkg;

    localparam MBOX_CSR_DATA_WIDTH = 32;
    localparam MBOX_CSR_MIN_ADDR_WIDTH = 6;

    typedef struct packed{
        logic hwclr;
    } mbox_csr__mbox_lock__lock__in_t;

    typedef struct packed{
        mbox_csr__mbox_lock__lock__in_t lock;
    } mbox_csr__mbox_lock__in_t;

    typedef struct packed{
        logic [31:0] next;
    } mbox_csr__mbox_id__id__in_t;

    typedef struct packed{
        mbox_csr__mbox_id__id__in_t id;
    } mbox_csr__mbox_id__in_t;

    typedef struct packed{
        logic [31:0] next;
        logic we;
        logic swwe;
    } mbox_csr__mbox_dataout__dataout__in_t;

    typedef struct packed{
        mbox_csr__mbox_dataout__dataout__in_t dataout;
    } mbox_csr__mbox_dataout__in_t;

    typedef struct packed{
        logic hwclr;
    } mbox_csr__mbox_execute__execute__in_t;

    typedef struct packed{
        mbox_csr__mbox_execute__execute__in_t execute;
    } mbox_csr__mbox_execute__in_t;

    typedef struct packed{
        logic hwclr;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__status__in_t;

    typedef struct packed{
        logic hwset;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__ecc_single_error_next_e066e214_wel_e066e214__in_t;

    typedef struct packed{
        logic hwset;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__ecc_double_error_next_e066e214_wel_e066e214__in_t;

    typedef struct packed{
        logic [2:0] next;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__mbox_fsm_ps__in_t;

    typedef struct packed{
        logic next;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__soc_has_lock__in_t;

    typedef struct packed{
        logic [14:0] next;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__mbox_rdptr__in_t;

    typedef struct packed{
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__status__in_t status;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__ecc_single_error_next_e066e214_wel_e066e214__in_t ecc_single_error;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__ecc_double_error_next_e066e214_wel_e066e214__in_t ecc_double_error;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__mbox_fsm_ps__in_t mbox_fsm_ps;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__soc_has_lock__in_t soc_has_lock;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__mbox_rdptr__in_t mbox_rdptr;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__in_t;

    typedef struct packed{
        logic cptra_rst_b;
        logic soc_req;
        logic lock_set;
        logic valid_requester;
        logic valid_receiver;
        mbox_csr__mbox_lock__in_t mbox_lock;
        mbox_csr__mbox_id__in_t mbox_id;
        mbox_csr__mbox_dataout__in_t mbox_dataout;
        mbox_csr__mbox_execute__in_t mbox_execute;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__in_t mbox_status;
    } mbox_csr__in_t;

    typedef struct packed{
        logic value;
        logic swmod;
    } mbox_csr__mbox_lock__lock__out_t;

    typedef struct packed{
        mbox_csr__mbox_lock__lock__out_t lock;
    } mbox_csr__mbox_lock__out_t;

    typedef struct packed{
        logic [31:0] value;
    } mbox_csr__mbox_id__id__out_t;

    typedef struct packed{
        mbox_csr__mbox_id__id__out_t id;
    } mbox_csr__mbox_id__out_t;

    typedef struct packed{
        logic swmod;
    } mbox_csr__mbox_cmd__command__out_t;

    typedef struct packed{
        mbox_csr__mbox_cmd__command__out_t command;
    } mbox_csr__mbox_cmd__out_t;

    typedef struct packed{
        logic [31:0] value;
        logic swmod;
    } mbox_csr__mbox_dlen__length__out_t;

    typedef struct packed{
        mbox_csr__mbox_dlen__length__out_t length;
    } mbox_csr__mbox_dlen__out_t;

    typedef struct packed{
        logic swmod;
    } mbox_csr__mbox_datain__datain__out_t;

    typedef struct packed{
        mbox_csr__mbox_datain__datain__out_t datain;
    } mbox_csr__mbox_datain__out_t;

    typedef struct packed{
        logic [31:0] value;
        logic swacc;
    } mbox_csr__mbox_dataout__dataout__out_t;

    typedef struct packed{
        mbox_csr__mbox_dataout__dataout__out_t dataout;
    } mbox_csr__mbox_dataout__out_t;

    typedef struct packed{
        logic value;
        logic swmod;
    } mbox_csr__mbox_execute__execute__out_t;

    typedef struct packed{
        mbox_csr__mbox_execute__execute__out_t execute;
    } mbox_csr__mbox_execute__out_t;

    typedef struct packed{
        logic [3:0] value;
        logic swmod;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__status__out_t;

    typedef struct packed{
        logic value;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__ecc_single_error_next_e066e214_wel_e066e214__out_t;

    typedef struct packed{
        logic value;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__ecc_double_error_next_e066e214_wel_e066e214__out_t;

    typedef struct packed{
        logic [2:0] value;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__mbox_fsm_ps__out_t;

    typedef struct packed{
        logic value;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__soc_has_lock__out_t;

    typedef struct packed{
        logic [14:0] value;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__mbox_rdptr__out_t;

    typedef struct packed{
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__status__out_t status;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__ecc_single_error_next_e066e214_wel_e066e214__out_t ecc_single_error;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__ecc_double_error_next_e066e214_wel_e066e214__out_t ecc_double_error;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__mbox_fsm_ps__out_t mbox_fsm_ps;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__soc_has_lock__out_t soc_has_lock;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__mbox_rdptr__out_t mbox_rdptr;
    } mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__out_t;

    typedef struct packed{
        logic value;
    } mbox_csr__mbox_unlock__unlock__out_t;

    typedef struct packed{
        mbox_csr__mbox_unlock__unlock__out_t unlock;
    } mbox_csr__mbox_unlock__out_t;

    typedef struct packed{
        mbox_csr__mbox_lock__out_t mbox_lock;
        mbox_csr__mbox_id__out_t mbox_id;
        mbox_csr__mbox_cmd__out_t mbox_cmd;
        mbox_csr__mbox_dlen__out_t mbox_dlen;
        mbox_csr__mbox_datain__out_t mbox_datain;
        mbox_csr__mbox_dataout__out_t mbox_dataout;
        mbox_csr__mbox_execute__out_t mbox_execute;
        mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760__out_t mbox_status;
        mbox_csr__mbox_unlock__out_t mbox_unlock;
    } mbox_csr__out_t;

    typedef enum logic [31:0] {
        mbox_csr__mbox_status__status__mbox_status_e__CMD_BUSY = 'h0,
        mbox_csr__mbox_status__status__mbox_status_e__DATA_READY = 'h1,
        mbox_csr__mbox_status__status__mbox_status_e__CMD_COMPLETE = 'h2,
        mbox_csr__mbox_status__status__mbox_status_e__CMD_FAILURE = 'h3
    } mbox_csr__mbox_status__status__mbox_status_e_e;

    typedef enum logic [31:0] {
        mbox_csr__mbox_status__mbox_fsm_ps__mbox_fsm_e__MBOX_IDLE = 'h0,
        mbox_csr__mbox_status__mbox_fsm_ps__mbox_fsm_e__MBOX_RDY_FOR_CMD = 'h1,
        mbox_csr__mbox_status__mbox_fsm_ps__mbox_fsm_e__MBOX_RDY_FOR_DLEN = 'h3,
        mbox_csr__mbox_status__mbox_fsm_ps__mbox_fsm_e__MBOX_RDY_FOR_DATA = 'h2,
        mbox_csr__mbox_status__mbox_fsm_ps__mbox_fsm_e__MBOX_EXECUTE_UC = 'h6,
        mbox_csr__mbox_status__mbox_fsm_ps__mbox_fsm_e__MBOX_EXECUTE_SOC = 'h4,
        mbox_csr__mbox_status__mbox_fsm_ps__mbox_fsm_e__MBOX_ERROR = 'h7
    } mbox_csr__mbox_status__mbox_fsm_ps__mbox_fsm_e_e;

    localparam MBOX_CSR_ADDR_WIDTH = 32'd6;

endpackage
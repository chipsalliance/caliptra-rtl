// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

package mbox_csr_pkg;
    typedef struct {
        logic hwclr;
    } mbox_csr__mbox_lock__lock__in_t;

    typedef struct {
        mbox_csr__mbox_lock__lock__in_t lock;
    } mbox_csr__mbox_lock__in_t;

    typedef struct {
        logic [31:0] next;
    } mbox_csr__mbox_user__user__in_t;

    typedef struct {
        mbox_csr__mbox_user__user__in_t user;
    } mbox_csr__mbox_user__in_t;

    typedef struct {
        logic [31:0] next;
        logic we;
        logic swwe;
    } mbox_csr__mbox_dataout__dataout__in_t;

    typedef struct {
        mbox_csr__mbox_dataout__dataout__in_t dataout;
    } mbox_csr__mbox_dataout__in_t;

    typedef struct {
        logic reset_b;
        logic lock_set;
        logic valid_user;
        mbox_csr__mbox_lock__in_t mbox_lock;
        mbox_csr__mbox_user__in_t mbox_user;
        mbox_csr__mbox_dataout__in_t mbox_dataout;
    } mbox_csr__in_t;

    typedef struct {
        logic value;
        logic swmod;
    } mbox_csr__mbox_lock__lock__out_t;

    typedef struct {
        mbox_csr__mbox_lock__lock__out_t lock;
    } mbox_csr__mbox_lock__out_t;

    typedef struct {
        logic [31:0] value;
    } mbox_csr__mbox_user__user__out_t;

    typedef struct {
        mbox_csr__mbox_user__user__out_t user;
    } mbox_csr__mbox_user__out_t;

    typedef struct {
        logic swmod;
    } mbox_csr__mbox_cmd__command__out_t;

    typedef struct {
        mbox_csr__mbox_cmd__command__out_t command;
    } mbox_csr__mbox_cmd__out_t;

    typedef struct {
        logic swmod;
    } mbox_csr__mbox_dlen__length__out_t;

    typedef struct {
        mbox_csr__mbox_dlen__length__out_t length;
    } mbox_csr__mbox_dlen__out_t;

    typedef struct {
        logic [31:0] value;
        logic swmod;
    } mbox_csr__mbox_datain__datain__out_t;

    typedef struct {
        mbox_csr__mbox_datain__datain__out_t datain;
    } mbox_csr__mbox_datain__out_t;

    typedef struct {
        logic swacc;
    } mbox_csr__mbox_dataout__dataout__out_t;

    typedef struct {
        mbox_csr__mbox_dataout__dataout__out_t dataout;
    } mbox_csr__mbox_dataout__out_t;

    typedef struct {
        logic value;
    } mbox_csr__mbox_execute__execute__out_t;

    typedef struct {
        mbox_csr__mbox_execute__execute__out_t execute;
    } mbox_csr__mbox_execute__out_t;

    typedef struct {
        mbox_csr__mbox_lock__out_t mbox_lock;
        mbox_csr__mbox_user__out_t mbox_user;
        mbox_csr__mbox_cmd__out_t mbox_cmd;
        mbox_csr__mbox_dlen__out_t mbox_dlen;
        mbox_csr__mbox_datain__out_t mbox_datain;
        mbox_csr__mbox_dataout__out_t mbox_dataout;
        mbox_csr__mbox_execute__out_t mbox_execute;
    } mbox_csr__out_t;
endpackage
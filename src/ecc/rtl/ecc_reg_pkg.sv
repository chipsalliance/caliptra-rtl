// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

package ecc_reg_pkg;
    typedef struct {
        logic [31:0] next;
    } ecc_reg__sr_hw_w32__in_t;

    typedef struct {
        ecc_reg__sr_hw_w32__in_t NAME;
    } ecc_reg__ecc_NAME__in_t;

    typedef struct {
        ecc_reg__sr_hw_w32__in_t VERSION;
    } ecc_reg__ecc_VERSION__in_t;

    typedef struct {
        logic [31:0] next;
    } ecc_reg__srw_hrw_w32__in_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__in_t CTRL;
    } ecc_reg__ecc_CTRL__in_t;

    typedef struct {
        logic [31:0] next;
    } ecc_reg__sr_hrw_w32__in_t;

    typedef struct {
        ecc_reg__sr_hrw_w32__in_t STATUS;
    } ecc_reg__ecc_STATUS__in_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__in_t SEED;
    } ecc_reg__ecc_SEED__in_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__in_t PRIVKEY;
    } ecc_reg__ecc_PRIVKEY__in_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__in_t PUBKEY_X;
    } ecc_reg__ecc_PUBKEY_X__in_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__in_t PUBKEY_Y;
    } ecc_reg__ecc_PUBKEY_Y__in_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__in_t R;
    } ecc_reg__ecc_R__in_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__in_t S;
    } ecc_reg__ecc_S__in_t;

    typedef struct {
        ecc_reg__sr_hrw_w32__in_t VERIFY_R;
    } ecc_reg__ecc_VERIFY_R__in_t;

    typedef struct {
        logic reset_b;
        ecc_reg__ecc_NAME__in_t ecc_NAME[2];
        ecc_reg__ecc_VERSION__in_t ecc_VERSION[2];
        ecc_reg__ecc_CTRL__in_t ecc_CTRL;
        ecc_reg__ecc_STATUS__in_t ecc_STATUS;
        ecc_reg__ecc_SEED__in_t ecc_SEED[12];
        ecc_reg__ecc_PRIVKEY__in_t ecc_PRIVKEY[12];
        ecc_reg__ecc_PUBKEY_X__in_t ecc_PUBKEY_X[12];
        ecc_reg__ecc_PUBKEY_Y__in_t ecc_PUBKEY_Y[12];
        ecc_reg__ecc_R__in_t ecc_R[12];
        ecc_reg__ecc_S__in_t ecc_S[12];
        ecc_reg__ecc_VERIFY_R__in_t ecc_VERIFY_R[12];
    } ecc_reg__in_t;

    typedef struct {
        logic [31:0] value;
    } ecc_reg__sr_hw_w32__out_t;

    typedef struct {
        ecc_reg__sr_hw_w32__out_t NAME;
    } ecc_reg__ecc_NAME__out_t;

    typedef struct {
        ecc_reg__sr_hw_w32__out_t VERSION;
    } ecc_reg__ecc_VERSION__out_t;

    typedef struct {
        logic [31:0] value;
    } ecc_reg__srw_hrw_w32__out_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__out_t CTRL;
    } ecc_reg__ecc_CTRL__out_t;

    typedef struct {
        logic [31:0] value;
    } ecc_reg__sr_hrw_w32__out_t;

    typedef struct {
        ecc_reg__sr_hrw_w32__out_t STATUS;
    } ecc_reg__ecc_STATUS__out_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__out_t SEED;
    } ecc_reg__ecc_SEED__out_t;

    typedef struct {
        logic [31:0] value;
    } ecc_reg__srw_hr_w32__out_t;

    typedef struct {
        ecc_reg__srw_hr_w32__out_t MSG;
    } ecc_reg__ecc_MSG__out_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__out_t PRIVKEY;
    } ecc_reg__ecc_PRIVKEY__out_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__out_t PUBKEY_X;
    } ecc_reg__ecc_PUBKEY_X__out_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__out_t PUBKEY_Y;
    } ecc_reg__ecc_PUBKEY_Y__out_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__out_t R;
    } ecc_reg__ecc_R__out_t;

    typedef struct {
        ecc_reg__srw_hrw_w32__out_t S;
    } ecc_reg__ecc_S__out_t;

    typedef struct {
        ecc_reg__sr_hrw_w32__out_t VERIFY_R;
    } ecc_reg__ecc_VERIFY_R__out_t;

    typedef struct {
        ecc_reg__srw_hr_w32__out_t LAMBDA;
    } ecc_reg__ecc_LAMBDA__out_t;

    typedef struct {
        ecc_reg__ecc_NAME__out_t ecc_NAME[2];
        ecc_reg__ecc_VERSION__out_t ecc_VERSION[2];
        ecc_reg__ecc_CTRL__out_t ecc_CTRL;
        ecc_reg__ecc_STATUS__out_t ecc_STATUS;
        ecc_reg__ecc_SEED__out_t ecc_SEED[12];
        ecc_reg__ecc_MSG__out_t ecc_MSG[12];
        ecc_reg__ecc_PRIVKEY__out_t ecc_PRIVKEY[12];
        ecc_reg__ecc_PUBKEY_X__out_t ecc_PUBKEY_X[12];
        ecc_reg__ecc_PUBKEY_Y__out_t ecc_PUBKEY_Y[12];
        ecc_reg__ecc_R__out_t ecc_R[12];
        ecc_reg__ecc_S__out_t ecc_S[12];
        ecc_reg__ecc_VERIFY_R__out_t ecc_VERIFY_R[12];
        ecc_reg__ecc_LAMBDA__out_t ecc_LAMBDA[12];
    } ecc_reg__out_t;
endpackage
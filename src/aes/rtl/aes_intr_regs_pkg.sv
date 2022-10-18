// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

package aes_intr_regs_pkg;
    typedef struct {
        logic hwset;
    } aes_intr_regs__error_intr_t__error0_sts_enable_528ccada_next_b1018582_resetsignal_939e99d4__in_t;

    typedef struct {
        logic hwset;
    } aes_intr_regs__error_intr_t__error1_sts_enable_938cafef_next_f460eb81_resetsignal_939e99d4__in_t;

    typedef struct {
        logic hwset;
    } aes_intr_regs__error_intr_t__error2_sts_enable_0dacf7a6_next_4b5b9e74_resetsignal_939e99d4__in_t;

    typedef struct {
        logic hwset;
    } aes_intr_regs__error_intr_t__error3_sts_enable_fc3af94b_next_c3125d40_resetsignal_939e99d4__in_t;

    typedef struct {
        aes_intr_regs__error_intr_t__error0_sts_enable_528ccada_next_b1018582_resetsignal_939e99d4__in_t error0_sts;
        aes_intr_regs__error_intr_t__error1_sts_enable_938cafef_next_f460eb81_resetsignal_939e99d4__in_t error1_sts;
        aes_intr_regs__error_intr_t__error2_sts_enable_0dacf7a6_next_4b5b9e74_resetsignal_939e99d4__in_t error2_sts;
        aes_intr_regs__error_intr_t__error3_sts_enable_fc3af94b_next_c3125d40_resetsignal_939e99d4__in_t error3_sts;
    } aes_intr_regs__error_intr_t_error0_sts_28545624_error1_sts_40e0d3e1_error2_sts_b1cf2205_error3_sts_74a35378__in_t;

    typedef struct {
        logic hwset;
    } aes_intr_regs__notif_intr_t__notif_cmd_done_sts_enable_dabe0b8b_next_540fa3b7__in_t;

    typedef struct {
        aes_intr_regs__notif_intr_t__notif_cmd_done_sts_enable_dabe0b8b_next_540fa3b7__in_t notif_cmd_done_sts;
    } aes_intr_regs__notif_intr_t_notif_cmd_done_sts_1c68637e__in_t;

    typedef struct {
        aes_intr_regs__error_intr_t_error0_sts_28545624_error1_sts_40e0d3e1_error2_sts_b1cf2205_error3_sts_74a35378__in_t error_internal_intr_r;
        aes_intr_regs__notif_intr_t_notif_cmd_done_sts_1c68637e__in_t notif_internal_intr_r;
    } aes_intr_regs__intr_block_t__in_t;

    typedef struct {
        logic reset_b;
        logic error_reset_b;
        aes_intr_regs__intr_block_t__in_t intr_block_rf;
    } aes_intr_regs__in_t;

    typedef struct {
        logic intr;
    } aes_intr_regs__global_intr_t_agg_sts_dd3dcf0a__out_t;

    typedef struct {
        logic intr;
    } aes_intr_regs__global_intr_t_agg_sts_e6399b4a__out_t;

    typedef struct {
        logic intr;
    } aes_intr_regs__error_intr_t_error0_sts_28545624_error1_sts_40e0d3e1_error2_sts_b1cf2205_error3_sts_74a35378__out_t;

    typedef struct {
        logic intr;
    } aes_intr_regs__notif_intr_t_notif_cmd_done_sts_1c68637e__out_t;

    typedef struct {
        aes_intr_regs__global_intr_t_agg_sts_dd3dcf0a__out_t error_global_intr_r;
        aes_intr_regs__global_intr_t_agg_sts_e6399b4a__out_t notif_global_intr_r;
        aes_intr_regs__error_intr_t_error0_sts_28545624_error1_sts_40e0d3e1_error2_sts_b1cf2205_error3_sts_74a35378__out_t error_internal_intr_r;
        aes_intr_regs__notif_intr_t_notif_cmd_done_sts_1c68637e__out_t notif_internal_intr_r;
    } aes_intr_regs__intr_block_t__out_t;

    typedef struct {
        aes_intr_regs__intr_block_t__out_t intr_block_rf;
    } aes_intr_regs__out_t;

    localparam AES_INTR_REGS_ADDR_WIDTH = 32'd10;

endpackage
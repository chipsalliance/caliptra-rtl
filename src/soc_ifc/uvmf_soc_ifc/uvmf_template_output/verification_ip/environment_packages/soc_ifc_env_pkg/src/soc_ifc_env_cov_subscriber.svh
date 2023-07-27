// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//------------------------------------------------------------------------------
//
// CLASS: soc_ifc_env_cov_subscriber
//
// This class provides an analysis export for receiving transactions from a
// connected analysis export. Making such a connection "subscribes" this
// component to any transactions emitted by the connected analysis port.
//
// This extended class provides a coverage subscriber that receives uvm_reg_item
// objects exported from the uvm_reg_predictor and calls the sample_values 
// function for the associated register.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// CLASS: soc_ifc_env_cov_subscriber
//
// This class instantiates externally defined analysis exports for receiving
// transactions from connected monitors.
//
// This extended class provides a coverage subscriber that receives transaction
// items from all interfaces and leverages the reg-model and predictor state
// to calculate functional coverage for UVM stimulus.
//
// In the environment build flow, connections are made from monitors to the
// analysis exports from this subscriber _last_, so that any prediction tasks
// will complete prior to the coverage model being called. This allows coverage
// to be computed on the updated current state of the system, with reference
// to expected changes.
//
//------------------------------------------------------------------------------

class soc_ifc_env_cov_subscriber #(
  type PRED_T = soc_ifc_predictor,
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  typedef soc_ifc_env_cov_subscriber #( PRED_T, CONFIG_T, BASE_T) this_type;

  // Factory registration of this class
  `uvm_component_param_utils( this_type )

  PRED_T pred;
  CONFIG_T configuration;
  soc_ifc_reg_model_top c_soc_ifc_rm;


  //------------------------------------------------------------------------------------------
  //                                   Coverage Signals
  //------------------------------------------------------------------------------------------
  mbox_steps_by_if_s prev_step_sampled = '{is_ahb: NOT_AHB_REQ, step:{null_action: 1'b1, default: 1'b0}};


  //------------------------------------------------------------------------------------------
  //                                   Covergroups
  //------------------------------------------------------------------------------------------
  covergroup soc_ifc_env_mbox_steps_cg with function sample (input bit is_ahb, input mbox_steps_s next_step);
    option.per_instance = 1;
    step_lock_acquire   : coverpoint (next_step.lock_acquire);
    step_cmd_wr         : coverpoint (next_step.cmd_wr);
    step_dlen_wr        : coverpoint (next_step.dlen_wr);
    step_datain_wr      : coverpoint (next_step.datain_wr);
    step_exec_set       : coverpoint (next_step.exec_set);
    step_cmd_rd         : coverpoint (next_step.cmd_rd);
    step_dlen_rd        : coverpoint (next_step.dlen_rd);
    step_dataout_rd     : coverpoint (next_step.dataout_rd);
    step_resp_datain_wr : coverpoint (next_step.resp_datain_wr);
    step_resp_dlen_wr   : coverpoint (next_step.resp_dlen_wr);
    step_resp_dlen_rd   : coverpoint (next_step.resp_dlen_rd);
    step_resp_dataout_rd: coverpoint (next_step.resp_dataout_rd);
    step_status_wr      : coverpoint (next_step.status_wr);
    step_status_rd      : coverpoint (next_step.status_rd);
    step_exec_clr       : coverpoint (next_step.exec_clr);
    step_force_unlock   : coverpoint (next_step.force_unlock);
    step_reset          : coverpoint (next_step.reset);
    /*
    *steps_all_mbox_flow : coverpoint (next_step) {
    *    bins mbox_flow = (MBOX_STEP_LOCK_ACQUIRE            =>
    *                      MBOX_STEP_CMD_WR         [=1]     =>
    *                      MBOX_STEP_DLEN_WR        [=1]     =>
    *                      MBOX_STEP_DATAIN_WR      [=1:511] =>
    *                      MBOX_STEP_EXEC_SET       [=1]     =>
    *                      MBOX_STEP_CMD_RD         [=1]     =>
    *                      MBOX_STEP_DLEN_RD        [=1]     =>
    *                      MBOX_STEP_DATAOUT_RD     [=1:511] =>
    *                      MBOX_STEP_STATUS_WR      [=1]     =>
    *                      MBOX_STEP_STATUS_RD      [=1:511] =>
    *                      MBOX_STEP_EXEC_CLR);
    *    bins mbox_resp_flow = (MBOX_STEP_LOCK_ACQUIRE                                                       =>
    *                           MBOX_STEP_CMD_WR                                                    [=1]     =>
    *                           MBOX_STEP_DLEN_WR                                                   [=1]     =>
    *                           MBOX_STEP_DATAIN_WR                                                 [=1:511] =>
    *                           MBOX_STEP_EXEC_SET                                                  [=1]     =>
    *                           MBOX_STEP_CMD_RD                                                    [=1]     =>
    *                           MBOX_STEP_DLEN_RD                                                   [=1]     =>
    *                           MBOX_STEP_DATAOUT_RD                                                [=1:511] =>
    *                           MBOX_STEP_RESP_DATAIN_WR,MBOX_STEP_RESP_DLEN_WR                     [=2:511] =>
    *                           MBOX_STEP_STATUS_WR                                                 [=1]     =>
    *                           MBOX_STEP_RESP_DLEN_RD,MBOX_STEP_RESP_DATAOUT_RD,MBOX_STEP_STATUS_RD[=3:511] =>
    *                           MBOX_STEP_EXEC_CLR);
    *}
    */
    which_lock_acquire   : cross step_lock_acquire   , is_ahb;
    which_cmd_wr         : cross step_cmd_wr         , is_ahb;
    which_dlen_wr        : cross step_dlen_wr        , is_ahb;
    which_datain_wr      : cross step_datain_wr      , is_ahb;
    which_exec_set       : cross step_exec_set       , is_ahb;
    which_cmd_rd         : cross step_cmd_rd         , is_ahb;
    which_dlen_rd        : cross step_dlen_rd        , is_ahb;
    which_dataout_rd     : cross step_dataout_rd     , is_ahb;
    which_resp_datain_wr : cross step_resp_datain_wr , is_ahb { ignore_bins ignore_apb = binsof(is_ahb) intersect {1'b0}; }
    which_resp_dlen_wr   : cross step_resp_dlen_wr   , is_ahb { ignore_bins ignore_apb = binsof(is_ahb) intersect {1'b0}; }
    which_resp_dlen_rd   : cross step_resp_dlen_rd   , is_ahb { ignore_bins ignore_ahb = binsof(is_ahb) intersect {1'b1}; }
    which_resp_dataout_rd: cross step_resp_dataout_rd, is_ahb { ignore_bins ignore_ahb = binsof(is_ahb) intersect {1'b1}; }
    which_status_wr      : cross step_status_wr      , is_ahb;
    which_status_rd      : cross step_status_rd      , is_ahb;
    which_exec_clr       : cross step_exec_clr       , is_ahb;
    which_force_unlock   : cross step_force_unlock   , is_ahb { ignore_bins ignore_apb = binsof(is_ahb) intersect {1'b0}; }
  endgroup

  covergroup soc_ifc_env_mbox_scenarios_cg with function sample (mbox_steps_by_if_s step_by_if);
    option.per_instance = 1;
    mbox_steps_by_if : coverpoint (step_by_if) {
        bins step_lock_acquire_ahb    = {{    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}};
        bins step_cmd_wr_ahb          = {{    AHB_REQ,MBOX_STEP_CMD_WR}};
        bins step_dlen_wr_ahb         = {{    AHB_REQ,MBOX_STEP_DLEN_WR}};
        bins step_datain_wr_ahb       = {{    AHB_REQ,MBOX_STEP_DATAIN_WR}};
        bins step_exec_set_ahb        = {{    AHB_REQ,MBOX_STEP_EXEC_SET}};
        bins step_cmd_rd_ahb          = {{    AHB_REQ,MBOX_STEP_CMD_RD}};
        bins step_dlen_rd_ahb         = {{    AHB_REQ,MBOX_STEP_DLEN_RD}};
        bins step_dataout_rd_ahb      = {{    AHB_REQ,MBOX_STEP_DATAOUT_RD}};
        bins step_resp_datain_wr_ahb  = {{    AHB_REQ,MBOX_STEP_RESP_DATAIN_WR}};
        bins step_resp_dlen_wr_ahb    = {{    AHB_REQ,MBOX_STEP_RESP_DLEN_WR}};
        bins step_status_wr_ahb       = {{    AHB_REQ,MBOX_STEP_STATUS_WR}};
        bins step_status_rd_ahb       = {{    AHB_REQ,MBOX_STEP_STATUS_RD}};
        bins step_exec_clr_ahb        = {{    AHB_REQ,MBOX_STEP_EXEC_CLR}};
        bins step_force_unlock_ahb    = {{    AHB_REQ,MBOX_STEP_FORCE_UNLOCK}};
        bins step_lock_acquire_apb    = {{NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}};
        bins step_cmd_wr_apb          = {{NOT_AHB_REQ,MBOX_STEP_CMD_WR}};
        bins step_dlen_wr_apb         = {{NOT_AHB_REQ,MBOX_STEP_DLEN_WR}};
        bins step_datain_wr_apb       = {{NOT_AHB_REQ,MBOX_STEP_DATAIN_WR}};
        bins step_exec_set_apb        = {{NOT_AHB_REQ,MBOX_STEP_EXEC_SET}};
        bins step_cmd_rd_apb          = {{NOT_AHB_REQ,MBOX_STEP_CMD_RD}};
        bins step_dlen_rd_apb         = {{NOT_AHB_REQ,MBOX_STEP_DLEN_RD}};
        bins step_dataout_rd_apb      = {{NOT_AHB_REQ,MBOX_STEP_DATAOUT_RD}};
        bins step_resp_dlen_rd_apb    = {{NOT_AHB_REQ,MBOX_STEP_RESP_DLEN_RD}};
        bins step_resp_dataout_rd_apb = {{NOT_AHB_REQ,MBOX_STEP_RESP_DATAOUT_RD}};
        bins step_status_wr_apb       = {{NOT_AHB_REQ,MBOX_STEP_STATUS_WR}};
        bins step_status_rd_apb       = {{NOT_AHB_REQ,MBOX_STEP_STATUS_RD}};
        bins step_exec_clr_apb        = {{NOT_AHB_REQ,MBOX_STEP_EXEC_CLR}};
        bins step_reset               = {{NOT_AHB_REQ,MBOX_STEP_RESET}};
    }
    /*
    *mbox_flow_by_if : coverpoint (step_by_if) {
    *    bins uc_to_soc_flow = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_SET    } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_RD      } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_RD     } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAOUT_RD  } [=1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_STATUS_WR   } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_STATUS_RD   } [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_CLR    });
    *    bins soc_to_uc_flow = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                    =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_CMD_RD      }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_RD     }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DATAOUT_RD  }                                                                           [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_RESP_DATAIN_WR},{AHB_REQ,MBOX_STEP_RESP_DLEN_WR}                                        [=2:511] =>
    *        {    AHB_REQ,MBOX_STEP_STATUS_WR   }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESP_DLEN_RD},{NOT_AHB_REQ,MBOX_STEP_RESP_DATAOUT_RD},{NOT_AHB_REQ,MBOX_STEP_STATUS_RD} [=3:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_CLR    });
    *}
    *mbox_flow_uc_to_soc_with_rst_by_if : coverpoint (step_by_if) {
    *    bins uc_to_soc_rst_after_lock  = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_cmd = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_dlen = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_datain = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}           =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [->1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_exec_set = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_SET    } [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_cmd_rd = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_SET    } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_RD      } [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_dlen_rd = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_SET    } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_RD      } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_RD     } [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_dataout_rd = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}           =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [=1:511]  =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_SET    } [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_RD      } [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_RD     } [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAOUT_RD  } [->1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_status_wr = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_SET    } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_RD      } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_RD     } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAOUT_RD  } [=1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_STATUS_WR   } [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_status_rd = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}           =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [=1:511]  =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_SET    } [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_RD      } [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_RD     } [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAOUT_RD  } [=1:511]  =>
    *        {NOT_AHB_REQ,MBOX_STEP_STATUS_WR   } [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_STATUS_RD   } [->1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins uc_to_soc_rst_after_exec_clr = (
    *        {    AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}          =>
    *        {    AHB_REQ,MBOX_STEP_CMD_WR      } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_WR     } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DATAIN_WR   } [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_SET    } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_RD      } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_RD     } [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAOUT_RD  } [=1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_STATUS_WR   } [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_STATUS_RD   } [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_EXEC_CLR    } [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *}
    *mbox_flow_soc_to_uc_with_rst_by_if : coverpoint (step_by_if) {
    *    bins soc_to_uc_rst_after_lock = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_cmd_wr = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                    =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_dlen_wr = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                    =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_datain_wr = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [->1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_exec_set = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                    =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_cmd_rd = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                    =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_CMD_RD      }                                                                           [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_dlen_rd = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                    =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_CMD_RD      }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_RD     }                                                                           [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_dataout_rd = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511]  =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_CMD_RD      }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_RD     }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DATAOUT_RD  }                                                                           [->1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_resp_dlen_wr = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511]  =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_CMD_RD      }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_RD     }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DATAOUT_RD  }                                                                           [=1:511]  =>
    *        {    AHB_REQ,MBOX_STEP_RESP_DATAIN_WR},{AHB_REQ,MBOX_STEP_RESP_DLEN_WR}                                        [->2:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_status_wr = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511]  =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_CMD_RD      }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_RD     }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DATAOUT_RD  }                                                                           [=1:511]  =>
    *        {    AHB_REQ,MBOX_STEP_RESP_DATAIN_WR},{AHB_REQ,MBOX_STEP_RESP_DLEN_WR}                                        [=2:511]  =>
    *        {    AHB_REQ,MBOX_STEP_STATUS_WR   }                                                                           [->1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_status_rd = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                     =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511]  =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_CMD_RD      }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_RD     }                                                                           [=1]      =>
    *        {    AHB_REQ,MBOX_STEP_DATAOUT_RD  }                                                                           [=1:511]  =>
    *        {    AHB_REQ,MBOX_STEP_RESP_DATAIN_WR},{AHB_REQ,MBOX_STEP_RESP_DLEN_WR}                                        [=2:511]  =>
    *        {    AHB_REQ,MBOX_STEP_STATUS_WR   }                                                                           [=1]      =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESP_DLEN_RD},{NOT_AHB_REQ,MBOX_STEP_RESP_DATAOUT_RD},{NOT_AHB_REQ,MBOX_STEP_STATUS_RD} [->3:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *    bins soc_to_uc_rst_after_exec_clr = (
    *        {NOT_AHB_REQ,MBOX_STEP_LOCK_ACQUIRE}                                                                                    =>
    *        {NOT_AHB_REQ,MBOX_STEP_CMD_WR      }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DLEN_WR     }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_DATAIN_WR   }                                                                           [=1:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_SET    }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_CMD_RD      }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DLEN_RD     }                                                                           [=1]     =>
    *        {    AHB_REQ,MBOX_STEP_DATAOUT_RD  }                                                                           [=1:511] =>
    *        {    AHB_REQ,MBOX_STEP_RESP_DATAIN_WR},{AHB_REQ,MBOX_STEP_RESP_DLEN_WR}                                        [=2:511] =>
    *        {    AHB_REQ,MBOX_STEP_STATUS_WR   }                                                                           [=1]     =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESP_DLEN_RD},{NOT_AHB_REQ,MBOX_STEP_RESP_DATAOUT_RD},{NOT_AHB_REQ,MBOX_STEP_STATUS_RD} [=3:511] =>
    *        {NOT_AHB_REQ,MBOX_STEP_EXEC_CLR    }                                                                           [->1]    =>
    *        {NOT_AHB_REQ,MBOX_STEP_RESET       });
    *}
    */
  endgroup
  /* TODO:
  * covergroup soc_ifc_env_resets;
  * covergroup soc_ifc_env_trng; // Incl. TRNG PAUSER cases
  * covergroup soc_ifc_env_pauser;
  * covergroup soc_ifc_env_iccm_lock;
  * covergroup soc_ifc_env_wdt;
  * covergroup soc_ifc_env_mtime;
  * covergroup soc_ifc_env_fuses; // Writes, resets, blocked writes
  * covergroup soc_ifc_env_errors; // E.g. NMI, MBOX PROT, ECC
  * covergroup soc_ifc_env_interrupts;
  * covergroup soc_ifc_env_boot;
  * covergroup soc_ifc_env_security_state;
  * covergroup soc_ifc_env_clk_gate;
  * covergroup soc_ifc_env_sha_accel;
  * covergroup soc_ifc_env_ahb_apb_arb; // Cover access contention
  */


  //------------------------------------------------------------------------------------------
  //                                   Member Variables
  //------------------------------------------------------------------------------------------
  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                      ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                      ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                      ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                      ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                      ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_transaction_t;
  typedef apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT,
                                       apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                                       apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                                       apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_transaction_t;

  // Instantiate the analysis exports
  uvm_analysis_imp_cov_soc_ifc_ctrl_ae   #(soc_ifc_ctrl_transaction,   this_type) soc_ifc_ctrl_ae;
  uvm_analysis_imp_cov_soc_ifc_status_ae #(soc_ifc_status_transaction, this_type) soc_ifc_status_ae;
  uvm_analysis_imp_cov_apb_ae            #(mvc_sequence_item_base,     this_type) apb_ae;
  uvm_analysis_imp_cov_cptra_ctrl_ae     #(cptra_ctrl_transaction,     this_type) cptra_ctrl_ae;
  uvm_analysis_imp_cov_cptra_status_ae   #(cptra_status_transaction,   this_type) cptra_status_ae;
  uvm_analysis_imp_cov_ahb_ae            #(mvc_sequence_item_base,     this_type) ahb_ae;
  uvm_analysis_imp_cov_mbox_sram_ae      #(mbox_sram_transaction,      this_type) mbox_sram_ae;

  //------------------------------------------------------------------------------------------
  //                                   Constructor
  //------------------------------------------------------------------------------------------
  function new (string name, uvm_component parent);
    super.new(name, parent);
    soc_ifc_env_mbox_steps_cg = new;
    soc_ifc_env_mbox_scenarios_cg = new;
  endfunction

  //------------------------------------------------------------------------------------------
  //                                   build_phase
  //------------------------------------------------------------------------------------------
  virtual function void build_phase (uvm_phase phase);
    soc_ifc_ctrl_ae   = new("soc_ifc_ctrl_ae"  , this);
    soc_ifc_status_ae = new("soc_ifc_status_ae", this);
    apb_ae            = new("apb_ae"           , this);
    cptra_ctrl_ae     = new("cptra_ctrl_ae"    , this);
    cptra_status_ae   = new("cptra_status_ae"  , this);
    ahb_ae            = new("ahb_ae"           , this);
    mbox_sram_ae      = new("mbox_sram_ae"     , this);

    c_soc_ifc_rm = configuration.soc_ifc_rm;
    soc_ifc_env_mbox_steps_cg.set_inst_name($sformatf("soc_ifc_env_mbox_steps_cg_%s",get_full_name()));
    soc_ifc_env_mbox_scenarios_cg.set_inst_name($sformatf("soc_ifc_env_mbox_scenarios_cg_%s",get_full_name()));
  endfunction

  //------------------------------------------------------------------------------------------
  //                                   CPTRA CTRL - write
  //------------------------------------------------------------------------------------------
  virtual function void write_cov_cptra_ctrl_ae(cptra_ctrl_transaction txn);
//    `uvm_fatal("FIXME", "FIXME")
  endfunction

  //------------------------------------------------------------------------------------------
  //                                   CPTRA STATUS - write
  //------------------------------------------------------------------------------------------
  virtual function void write_cov_cptra_status_ae(cptra_status_transaction txn);
//    `uvm_fatal("FIXME", "FIXME")
  endfunction

  //------------------------------------------------------------------------------------------
  //                                   SOC_IFC CTRL - write
  //------------------------------------------------------------------------------------------
  virtual function void write_cov_soc_ifc_ctrl_ae(soc_ifc_ctrl_transaction txn);
    `uvm_info("SOC_IFC_COV_SOC_IFC_CTRL", {"Collecting coverage on transaction: ", txn.convert2string()}, UVM_MEDIUM)
    if (!txn.set_pwrgood || txn.assert_rst) begin
        `uvm_info("SOC_IFC_COV_SOC_IFC_CTRL", $sformatf("Got next_step [%p]", pred.next_step), UVM_FULL)
        soc_ifc_env_mbox_steps_cg.sample(.is_ahb(NOT_AHB_REQ), .next_step(pred.next_step));
        soc_ifc_env_mbox_scenarios_cg.sample({NOT_AHB_REQ,pred.next_step});
        prev_step_sampled = {is_ahb:NOT_AHB_REQ,step:pred.next_step};
    end
  endfunction

  //------------------------------------------------------------------------------------------
  //                                   SOC_IFC STATUS - write
  //------------------------------------------------------------------------------------------
  virtual function void write_cov_soc_ifc_status_ae(soc_ifc_status_transaction txn);
//    `uvm_fatal("FIXME", "FIXME")
  endfunction

  //------------------------------------------------------------------------------------------
  //                                   MBOX SRAM - write
  //------------------------------------------------------------------------------------------
  virtual function void write_cov_mbox_sram_ae(mbox_sram_transaction txn);
//    `uvm_fatal("FIXME", "FIXME")
  endfunction

  //------------------------------------------------------------------------------------------
  //                                   AHB - write
  //------------------------------------------------------------------------------------------
  virtual function void write_cov_ahb_ae(mvc_sequence_item_base txn);
    ahb_transaction_t ahb_txn;
    uvm_reg axs_reg;
    uvm_mem axs_mem;

    // Decode argument to access type
    if (!$cast(ahb_txn,txn))
        `uvm_fatal("SOC_IFC_ENV_COV", "AHB coverage analysis import received invalid transaction")
    if (c_soc_ifc_rm.soc_ifc_AHB_map.get_mem_by_offset(ahb_txn.address) != null) begin: MEM_HANDLE
        `uvm_info("SOC_IFC_COV_AHB", $sformatf("Detected access to mailbox at address: 0x%x", ahb_txn.address), UVM_MEDIUM)
        axs_mem = c_soc_ifc_rm.soc_ifc_AHB_map.get_mem_by_offset(ahb_txn.address);
    end: MEM_HANDLE
    else begin: REG_HANDLE
        axs_reg = c_soc_ifc_rm.soc_ifc_AHB_map.get_reg_by_offset(ahb_txn.address);
        if (axs_reg == null) begin
            `uvm_error("SOC_IFC_COV_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from soc_ifc_AHB_map", ahb_txn.address))
        end
    end: REG_HANDLE

    // Calculate coverage impact from register access
    if (axs_mem != null) begin: MEM_AXS
        `uvm_info("SOC_IFC_COV_AHB", $sformatf("Not calculating any system coverage for access to mailbox at address: 0x%x", ahb_txn.address), UVM_FULL)
    end// MEM_AXS
    else if (axs_reg == null) begin
        `uvm_error("SOC_IFC_COV_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from soc_ifc_AHB_map", ahb_txn.address))
    end
    else begin: REG_AXS
        `uvm_info("SOC_IFC_COV_AHB", {"Collecting coverage on access to register: ", axs_reg.get_full_name()}, UVM_MEDIUM)
        // Non-interrupt registers have 2-levels of ancestry back to reg_model top
        if (axs_reg.get_parent().get_parent().get_name() == "soc_ifc_rm") begin
            case (axs_reg.get_name()) inside
                "mbox_lock",
                "mbox_user",
                "mbox_cmd",
                "mbox_dlen",
                "mbox_datain",
                "mbox_dataout",
                "mbox_execute",
                "mbox_status",
                "mbox_unlock": begin
                    `uvm_info("SOC_IFC_COV_AHB", $sformatf("Got next_step [%p]", pred.next_step), UVM_FULL)
                    // Skip coverage on repeated steps, as a memory optimization (large rep. operators are onerous)
                    if (pred.next_step inside {MBOX_STEP_DATAIN_WR,
                                               MBOX_STEP_DATAOUT_RD,
                                               MBOX_STEP_STATUS_RD,
                                               MBOX_STEP_RESP_DATAIN_WR,
                                               MBOX_STEP_RESP_DATAOUT_RD/*shouldn't happen*/} &&
                        pred.next_step == prev_step_sampled.step &&
                        prev_step_sampled.is_ahb) begin
                        `uvm_info("SOC_IFC_COV_AHB", "Skipping sample for step [%p] as it is a repetition", UVM_DEBUG)
                    end
                    else begin
                        soc_ifc_env_mbox_steps_cg.sample(.is_ahb(AHB_REQ), .next_step(pred.next_step));
                        soc_ifc_env_mbox_scenarios_cg.sample({AHB_REQ,pred.next_step});
                        prev_step_sampled = '{is_ahb:AHB_REQ, step:pred.next_step};
                    end
                end
            endcase
        end
    end
  endfunction

  //------------------------------------------------------------------------------------------
  //                                   APB - write
  //------------------------------------------------------------------------------------------
  virtual function void write_cov_apb_ae(mvc_sequence_item_base txn);
    apb_transaction_t apb_txn;
    uvm_reg           axs_reg;

    // Extract info
    if (!$cast(apb_txn,txn)) `uvm_fatal("SOC_IFC_COV_APB", "APB coverage analysis import received invalid transaction")
    axs_reg = c_soc_ifc_rm.soc_ifc_APB_map.get_reg_by_offset(apb_txn.addr);

    // Calculate coverage impact from register access
    if (axs_reg == null) begin
        `uvm_error("SOC_IFC_COV_APB", $sformatf("APB transaction to address: 0x%x decodes to null from soc_ifc_APB_map", apb_txn.addr))
    end
    else begin: REG_AXS
        `uvm_info("SOC_IFC_COV_APB", {"Collecting coverage on access to register: ", axs_reg.get_full_name()}, UVM_MEDIUM)
        case (axs_reg.get_name()) inside
            "mbox_lock",
            "mbox_user",
            "mbox_cmd",
            "mbox_dlen",
            "mbox_datain",
            "mbox_dataout",
            "mbox_execute",
            "mbox_status",
            "mbox_unlock": begin
                `uvm_info("SOC_IFC_COV_APB", $sformatf("Got next_step [%p]", pred.next_step), UVM_FULL)
                // Skip coverage on repeated steps, as a memory optimization (large rep. operators are onerous)
                if (pred.next_step inside {MBOX_STEP_DATAIN_WR,
                                           MBOX_STEP_DATAOUT_RD,
                                           MBOX_STEP_STATUS_RD,
                                           MBOX_STEP_RESP_DATAIN_WR/*shouldn't happen*/,
                                           MBOX_STEP_RESP_DATAOUT_RD} &&
                    pred.next_step == prev_step_sampled.step &&
                    !prev_step_sampled.is_ahb) begin
                    `uvm_info("SOC_IFC_COV_APB", "Skipping sample for step [%p] as it is a repetition", UVM_DEBUG)
                end
                else begin
                    soc_ifc_env_mbox_steps_cg.sample(.is_ahb(NOT_AHB_REQ), .next_step(pred.next_step));
                    soc_ifc_env_mbox_scenarios_cg.sample({NOT_AHB_REQ,pred.next_step});
                    prev_step_sampled = '{is_ahb: NOT_AHB_REQ, step:pred.next_step};
                end
            end
        endcase
    end
  endfunction
  
endclass

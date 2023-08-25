#export UVMF_HOME='/home/cad/tools/mentor/uvmf/UVMF_2022.3'
python ${UVMF_HOME}/scripts/yaml2uvmf.py --merge_source uvmf_template_output \
                                         --merge_skip_missing_blocks \
                                         soc_ifc_global.yaml \
                                         soc_ifc_ctrl_interface.yaml \
                                         soc_ifc_status_interface.yaml \
                                         mbox_sram_interface.yaml \
                                         soc_ifc_util_comp_soc_ifc_predictor.yaml \
                                         soc_ifc_util_comp_soc_ifc_scoreboard.yaml \
                                         ../../libs/uvmf/qvip_ahb_lite_slave_dir/uvmf/qvip_ahb_lite_slave_subenv_config.yaml \
                                         ../../libs/uvmf/qvip_apb5_slave_dir/uvmf/qvip_apb5_slave_subenv_config.yaml \
                                         soc_ifc_environment.yaml \
                                         soc_ifc_bench.yaml \
                                         -d uvmf_template_output_merged


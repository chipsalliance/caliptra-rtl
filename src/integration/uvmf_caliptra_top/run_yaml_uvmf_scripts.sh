#export UVMF_HOME='/home/cad/tools/mentor/uvmf/UVMF_2022.3'
python ${UVMF_HOME}/scripts/yaml2uvmf.py --merge_source uvmf_template_output \
                                         --merge_skip_missing_blocks \
                                         caliptra_top_global.yaml \
                                         ../../libs/uvmf/qvip_ahb_lite_slave_dir/uvmf/qvip_ahb_lite_slave_subenv_config.yaml \
                                         ../../libs/uvmf/qvip_apb5_slave_dir/uvmf/qvip_apb5_slave_subenv_config.yaml \
                                         ../../soc_ifc/uvmf_soc_ifc/uvmf_template_output/verification_ip/interface_packages/cptra_ctrl_pkg/yaml/cptra_ctrl_interface.yaml \
                                         ../../soc_ifc/uvmf_soc_ifc/uvmf_template_output/verification_ip/interface_packages/soc_ifc_ctrl_pkg/yaml/soc_ifc_ctrl_interface.yaml \
                                         ../../soc_ifc/uvmf_soc_ifc/uvmf_template_output/verification_ip/interface_packages/cptra_status_pkg/yaml/cptra_status_interface.yaml \
                                         ../../soc_ifc/uvmf_soc_ifc/uvmf_template_output/verification_ip/interface_packages/soc_ifc_status_pkg/yaml/soc_ifc_status_interface.yaml \
                                         ../../soc_ifc/uvmf_soc_ifc/uvmf_template_output/verification_ip/environment_packages/soc_ifc_env_pkg/yaml/soc_ifc_util_comp_soc_ifc_predictor.yaml \
                                         ../../soc_ifc/uvmf_soc_ifc/uvmf_template_output/verification_ip/environment_packages/soc_ifc_env_pkg/yaml/soc_ifc_util_comp_soc_ifc_scoreboard.yaml \
                                         ../../soc_ifc/uvmf_soc_ifc/uvmf_template_output/verification_ip/environment_packages/soc_ifc_env_pkg/yaml/soc_ifc_environment.yaml \
                                         caliptra_top_environment.yaml \
                                         caliptra_top_bench.yaml \
                                         -d uvmf_template_output_merged


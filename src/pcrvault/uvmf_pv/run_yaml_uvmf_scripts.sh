#export UVMF_HOME='/home/cad/tools/mentor/uvmf/UVMF_2022.3'
#python ${UVMF_HOME}/scripts/yaml2uvmf.py --merge_source uvmf_template_output \
python ${UVMF_HOME}/scripts/yaml2uvmf.py \
                                         --merge_skip_missing_blocks \
                                         pv_global.yaml \
                                         pv_interfaces.yaml \
                                         pv_util_comp_predictor.yaml \
                                         pv_util_comp_scoreboard.yaml \
                                         ../../libs/uvmf/qvip_ahb_lite_slave_dir/uvmf/qvip_ahb_lite_slave_subenv_config.yaml \
                                         pv_environment.yaml \
                                         pv_bench.yaml \
                                         -d uvmf_template_output
#                                         -d uvmf_template_output_merged


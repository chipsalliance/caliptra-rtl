#export UVMF_HOME='/home/cad/tools/mentor/uvmf/UVMF_2022.3'
python ${UVMF_HOME}/scripts/yaml2uvmf.py --merge_source uvmf_template_output \
                                         --merge_skip_missing_blocks \
                                         kv_global.yaml \
                                         kv_interfaces.yaml \
                                         kv_util_comp_predictor.yaml \
                                         ../../libs/uvmf/qvip_ahb_lite_slave_dir/uvmf/qvip_ahb_lite_slave_subenv_config.yaml \
                                         kv_environment.yaml \
                                         kv_bench.yaml \
                                         -d uvmf_template_output_merged


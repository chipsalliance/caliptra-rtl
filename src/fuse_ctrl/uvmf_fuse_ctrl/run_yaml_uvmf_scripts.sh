#export UVMF_HOME='/home/cad/tools/mentor/uvmf/UVMF_2022.3'
python ${UVMF_HOME}/scripts/yaml2uvmf.py --merge_source uvmf_template_output \
                                         --merge_skip_missing_blocks \
                                         fuse_ctrl_global.yaml \
                                         fuse_ctrl_in_interfaces.yaml \
                                         fuse_ctrl_out_interfaces.yaml \
                                         fuse_ctrl_util_comp_predictor.yaml \
                                         fuse_ctrl_util_comp_scoreboard.yaml \
                                         fuse_ctrl_environment.yaml \
                                         fuse_ctrl_bench.yaml \
                                         -d uvmf_template_output_merged


#export UVMF_HOME='/home/cad/tools/mentor/uvmf/UVMF_2022.3'
# The local template adds lifecycle hooks absent from the stock coverage template.
template_dir=$(CDPATH= cd -- "$(dirname -- "$0")/templates" && pwd) || exit 1
export UVMF_TEMPLATE_PATH="${template_dir}${UVMF_TEMPLATE_PATH:+:${UVMF_TEMPLATE_PATH}}"
# Preserve custom pragma blocks, including the fixed-length PV read coverage.
python ${UVMF_HOME}/scripts/yaml2uvmf.py --merge_source uvmf_template_output \
                                         --merge_skip_missing_blocks \
                                         pv_global.yaml \
                                         pv_interfaces.yaml \
                                         pv_util_comp_predictor.yaml \
                                         pv_util_comp_scoreboard.yaml \
                                         ../../libs/uvmf/qvip_ahb_lite_slave_dir/uvmf/qvip_ahb_lite_slave_subenv_config.yaml \
                                         pv_environment.yaml \
                                         pv_bench.yaml \
                                         -d uvmf_template_output_merged

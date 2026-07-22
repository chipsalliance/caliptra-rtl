#!/usr/bin/env bash
# Generate the HMAC256 UVMF environment from the yaml files in this directory.
#
# Required environment:
#   export UVMF_HOME=/home/cad/tools/mentor/uvmf/UVMF_2022.3
#   module load tools/anaconda/5.2.0      # optional, depends on UVMF version
#   module load tools/python/python3/3.6.8
#
# Behaviour:
# - First run (no uvmf_template_output/ present): straight generation
#   into uvmf_template_output/.
# - Re-runs (uvmf_template_output/ already exists): merge yaml updates
#   into uvmf_template_output_merged/ and rsync the .pragma-guarded
#   sections back. This preserves hand edits inside
#   `// pragma uvmf custom ... begin/end` blocks.
# - The KV interface packages (kv_read, kv_write) are pulled in from
#   the already-generated keyvault env so we do not maintain a second
#   copy.
# - The QVIP AHB-lite slave subenv config is shared with kv.
# - The DPI-C block in HMAC256_environment.yaml triggers generation of
#   the dpi header + Makefile rules; the hand-written hmac256_dpi.c is
#   dropped into uvmf_template_output/.../HMAC256_env_pkg/dpi/ after the
#   first generate.

set -euo pipefail

if [[ -z "${UVMF_HOME:-}" ]]; then
  echo "ERROR: UVMF_HOME is not set." >&2
  echo "Try: export UVMF_HOME=/home/cad/tools/mentor/uvmf/UVMF_2022.3" >&2
  exit 1
fi

# Caliptra UVMF flow requires python3; pick a python3 explicitly so we
# do not accidentally run under a system python2 default.
PY="${PYTHON3:-python3}"
if ! command -v "${PY}" >/dev/null 2>&1; then
  echo "ERROR: python3 not on PATH; try 'module load tools/python/python3/3.6.8'" >&2
  exit 1
fi

cd "$(dirname "$0")"

YAMLS=(
  hmac256_global.yaml
  hmac256_interfaces.yaml
  hmac256_util_comp_predictor.yaml
  hmac256_util_comp_scoreboard.yaml
  ../../libs/uvmf/qvip_ahb_lite_slave_dir/uvmf/qvip_ahb_lite_slave_subenv_config.yaml
  HMAC256_environment.yaml
  hmac256_bench.yaml
)

if [[ -d uvmf_template_output ]]; then
  echo "[run_yaml_uvmf_scripts] re-generating with merge into uvmf_template_output_merged"
  "${PY}" "${UVMF_HOME}/scripts/yaml2uvmf.py" \
    --merge_source uvmf_template_output \
    --merge_skip_missing_blocks \
    "${YAMLS[@]}" \
    -d uvmf_template_output_merged
  # The merge pass emits a fresh tree into uvmf_template_output_merged/
  # with our hand-edits inside `pragma uvmf custom` blocks preserved.
  # rsync it back over uvmf_template_output/ so the canonical
  # generated tree always reflects the latest yamls + latest custom
  # edits.
  if command -v rsync >/dev/null 2>&1; then
    rsync -a --delete uvmf_template_output_merged/ uvmf_template_output/
  else
    rm -rf uvmf_template_output && cp -r uvmf_template_output_merged uvmf_template_output
  fi
  rm -rf uvmf_template_output_merged
  echo
  echo "[run_yaml_uvmf_scripts] merge applied in place; review git diff before committing."
else
  echo "[run_yaml_uvmf_scripts] first-time generation into uvmf_template_output/"
  "${PY}" "${UVMF_HOME}/scripts/yaml2uvmf.py" \
    "${YAMLS[@]}" \
    -d uvmf_template_output
fi

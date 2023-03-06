@set QUESTA_ROOT=C:/MentorTools/questasim_2019.2
@set UVMF_HOME=C:/graemej/UVM_FRAMEWORK/UVMF_Repo_2019.4

python %UVMF_HOME%/scripts/yaml2uvmf.py SHA512_in_interface.yaml SHA512_out_interface.yaml SHA512_util_comp_SHA512_predictor.yaml SHA512_environment.yaml SHA512_bench.yaml -d ../uvmf_template_output

pause

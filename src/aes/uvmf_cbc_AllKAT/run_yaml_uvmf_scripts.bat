@set QUESTA_ROOT=C:/MentorTools/questasim_2019.2
@set UVMF_HOME=C:/graemej/UVM_FRAMEWORK/UVMF_Repo_2019.4

python %UVMF_HOME%/scripts/yaml2uvmf.py AES_in_interface.yaml AES_out_interface.yaml AES_util_comp_AES_predictor.yaml AES_environment.yaml AES_bench.yaml -d ../uvmf_template_output

pause

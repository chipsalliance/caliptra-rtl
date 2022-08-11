1.
To run UVMF, please set $UVMF_HOME use the following command:
"export UVMF_HOME=<path to UVMF home directory>"

The one on our server is located at:
"/home/cad/tools/mentor/questa/2022.2_1/questasim/examples/UVM_Framework/UVMF_2021.3"

Or, you can download the lastest release version online at: https://verificationacademy.com/courses/UVM-Framework-One-Bite-at-a-Time

2.
Please use the following commands to loading python and questa modules:
module load tools/python/python3/3.6.8
module load tools/mentor/license/2020.12
module load tools/mentor/questa/2022.2_1

3.
To run testbenches, go to "Caliptra/src/aes/uvmf/uvmf_template_output/project_benches/AES/sim"
and run "make debug" for random sequences, or "make debug TEST_NAME=AES_random_test" for preset sequences

4.
After Questa(ModelSim) opens, enter the run time (50000ns recommended) and hit run. It will run 25 random tests by default

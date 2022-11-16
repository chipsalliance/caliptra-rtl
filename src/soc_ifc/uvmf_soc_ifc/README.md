1.
To build UVMF QVIP instances, use the qvip configurator. First, load the
configurator module:
    module load tools/mentor/questa_vip/2022.2/x86_64_gcc-6.7.2_vcs
Then invoke the configurator with
    qvip_configurator
Documentation on the configurator here:
    /home/cad/tools/mentor/questa_vip/2022.2/docs/pdfdocs/icvip_configurator_user.pdf
Or check out the Verification Academy video:
    https://verificationacademy.com/sessions/uvmf-questa-vip-integration

2.
To run UVMF, please set $UVMF_HOME use the following command:
"export UVMF_HOME=<path to UVMF home directory>"

The one on our server is located at:
"/home/cad/tools/mentor/questa/2022.2_1/questasim/examples/UVM_Framework/UVMF_2021.3"

Or, you can download the lastest release version online at: https://verificationacademy.com/courses/UVM-Framework-One-Bite-at-a-Time

3.
Please use the following commands to loading python and questa modules:
module load tools/python/python3/3.6.8
module load tools/mentor/license/2020.12
module load tools/mentor/questa/2022.2_1

4.
To run testbenches, go to "Caliptra/src/mbox/uvmf/uvmf_template_output/project_benches/mbox/sim"
and run "make debug" for random sequences, or "make debug TEST_NAME=mbox_random_test" for preset sequences

5.
After Questa(ModelSim) opens, enter the run time (50000ns recommended) and hit run.

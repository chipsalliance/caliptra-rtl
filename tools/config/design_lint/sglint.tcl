#-------------------------------------------------------------------------------
#
# Spyglass LINT run script 
# 
#-------------------------------------------------------------------------------
# Copyright (C) Microsoft Corporation. All rights reserved.
#-------------------------------------------------------------------------------
#
# Change log
#
#   date         who      Description
#-----------------------------------------------------------------------------
#  2020-11-29   Jimmy     Modified to run on Playbook
#  2020-07-14   Gowtham   Changed rtlenv* to rtl:rtlenv*
#
########################################################################################################################
# Source Common Flow Files
########################################################################################################################

# Load ctl file options from the base_config repo
source $::env(BASE_CONFIG)/config/design_lint/sglint.tcl

########################################################################################################################
# Jinja templates
set OUTPUT_DIR {{ data.output_dir }}
set VERILOG_FLIST {{ data.verilog_flist }}
set DESIGN_NAME {{ data.design_name }}
set BB_MODULES {{ data.bb_modules }}
set EXTRA_POLICIES {{ data.extra_policies }}
set AUTO_BB {{ data.auto_bb }}
set PRAGMAS {{ data.pragmas }}
set IGNORE_CELLDEFS {{ data.ignore_celldefs }}
set BBOX_FILES {{ data.bbox_files }}
set GUI {{ data.gui }}
set WAIVER_FILES {{ data.waiver_files }}
set ELAB_OPTIONS {{ data.elab_options }}
set ANALYSIS_OPTIONS {{ data.analysis_options }}
set REPORT_FILE {{ data.report_file }}

########################################################################################################################
# Set Design Input Variables
########################################################################################################################
set output_dir $OUTPUT_DIR

# Setting the vcstatic platform to run vc spyglass lint
set_app_var enable_lint true
set_app_var sg_vc_compat true

# read the policy script for lint analysis, if it is there
if { [ file exists $output_dir/spyglass_lint.policy ] } { redirect spyglass_lint.policy.log {source $output_dir/spyglass_lint.policy} }

# add extra policies here
foreach policy $EXTRA_POLICIES {
  if { [ file exists $output_dir/$policy ] } { redirect spyglass_lint.policy.log {source $output_dir/$policy} }
}

## Goal for Lint analysis 
configure_lint_setup -goal lint_rtl_msft

set check_celldefine $IGNORE_CELLDEFS
set pragma $PRAGMAS

if { $BB_MODULES eq ""} {
   # Empty bbox list in compile.yml
   set autobb_unresolved_modules $AUTO_BB
} else {
   # Not-Empty bbox list in compile.yml
   set autobb_unresolved_modules true
}
set analyze_skip_translate_body false

analyze -format verilog -vcs "-f $VERILOG_FLIST" $ANALYSIS_OPTIONS

# Adding the file blackbox-ed - this is a 2020.03-SP2-3 +  feature only
set bbox_files_string [join $BBOX_FILES " "]
set_blackbox_file -files $bbox_files_string

# Adding the module blackbox-ed
set bb_modules_string [join $BB_MODULES " "]
set_blackbox -designs $bb_modules_string

elaborate $DESIGN_NAME -vcs $ELAB_OPTIONS

## To report the blackbox
#report_blackbox -designs -verbose -automatic
get_blackbox -designs  -automatic

# To report design read violations
report_read_violations -verbose -file spyglass_read.rpt

# read the waiver script for lint analysis, if it is there
foreach waiver_file $WAIVER_FILES {
   puts $waiver_file
  if { [ file exists $waiver_file ] } {source $waiver_file} 
}

if { $autobb_unresolved_modules != true } {
  foreach bbox_module $BB_MODULES {   
    waive_read -family DESIGN  -tag "ErrorAnalyzeBBox" -filter "Module == $bbox_module"  -add Blackbox_${bbox_module}
  }
}
# List all black-box waivers
# waive_read -tcl -family DESIGN

#### Running checks in VC Lint
check_lint

# Report the Lint violations
report_lint -file ${REPORT_FILE} -append
report_lint -verbose -report {all} -no_summary -file ${REPORT_FILE} -append

save_session -session SNAPSHOT

# To get the stats memory/runtime
get_resource_cost
#report_lint
report_lint -verbose -sort -ignore_viol_state waived -severity "fatal error warning" 
report_lint -ignore_viol_state waived -severity "fatal error warning" 

if { $GUI == "false" } {
  exit
} else {
  start_gui
}


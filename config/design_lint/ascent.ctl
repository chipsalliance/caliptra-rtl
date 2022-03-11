# Load ctl file options from the base_config repo
source $::env(BASE_CONFIG)/config/design_lint/ascent.ctl

# Read the policy script for lint analysis, if it is there.
if { [ file exists ascent_lint.policy ] } { echo "Sourcing ascent_lint.policy (output captured in ascent_lint.policy.log)" }
if { [ file exists ascent_lint.policy ] } { redirect {source ascent_lint.policy} -file ascent_lint.policy.log }

# Read the waiver script for lint analysis, if it is there.
if { [ file exists ascent_lint.waiver ] } { source ascent_lint.waiver }

# Read the global waiver script for lint analysis, if it is there.
if { [ file exists ascent_lint_global.waiver ] } { source ascent_lint_global.waiver }

# Reverse reduction in total range bits found in version 2019.A.p11. This restores previous checks.
set ri_max_total_range_bits 17

analyze \
    -sv \
    TOP_FILE

elaborate

report_policy ALL -verbose -output ascent_lint.rpt

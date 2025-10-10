---
name: RTL RFC Issue Template
about: Template for Caliptra contributors to file an RFC proposing development of
  features, modifications, or fixes for approval.
title: "[RFC] {RFC title here}"
labels: RFC
assignees: ''

---

# [edit] Title for contribution proposal
[edit] Abstract

## Scope
[edit] What parts of the project will be affected.
* [edit] Overview of anticipated changes to specifications or other documentation (e.g. impacts to Trademark Compliance)
* [edit] Overview of changes to security posture per FIPS 140-3
* [edit] Expected impact to area or memory consumption
* [edit] Expected impact to timing, CDC, RDC

## Rationale
[edit] The motivation and justification for the change, including why it is important to include in a specific Caliptra release version.

## Implementation Tradeoffs
[edit] Details of various implementations being considered. Explain why the proposed change can not be handled outside of Caliptra.<BR>
[optional - if available] Links to any development work already completed and accompanying test results.

## Implementation Timeline
[edit] A realistic estimate for completion. May include multiple milestones if a large change requires many Pull Requests.<BR>
[edit] Which MAJOR.MINOR release is this intended for inclusion?

## [optional - for hw/fw changes] Test Plan
[edit] Required for any hardware changes to ensure quality, certifiability, maintainability.

### Testbench development
[edit] Describe new testbenches or modifications to existing testbenches to validate feature.

### Test suite
| Test Title | TB | Description | Randomization | Pass Metrics |
| :--- | :--- | :--- | :--- | :--- |
| Test 1 | caliptra_top_tb | new test for testing tests | a,b,c | x,y,z |

## Maintenance
[edit] The individual or team responsible as the point of contact for this feature now and in the future. Contributors must provide a plan for ongoing maintenance.

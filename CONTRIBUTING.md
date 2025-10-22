# Contributing to caliptra-rtl

All contributions to Caliptra must adhere to the [guidelines](https://github.com/chipsalliance/Caliptra/blob/main/CONTRIBUTING.md) that are centrally defined in Caliptra repository.

This document defines additional guidelines and conventions that are specific to the Caliptra RTL repository.

## Git Conventions

### Commit conventions
Git documentation provides some guidance on preparing good quality commit messages here:<BR>
https://git-scm.com/docs/SubmittingPatches#describe-changes

Main points:
  - Imperative mood, present tense for subject line
  - Capitalized first-word of subject line
  - Prefix for the commit area (defined below)
  - 50-character subject line
  - 72-character line breaks in the body
  - Tell "what" and "why"
    - e.g. "Fix bug in UVM testbench causing AXI transaction mismatch"
    - e.g. "Update FSM transitions based on XYZ to resolve missed error states"

### Pull Request Conventions
  - Title of the Pull Request should match conventions for an individual commit subject line, as shown above (imperative mood, etc).
  - Title:
    - First word of Pull Request Title is in [BRACKETS] and tells which area the commit affects (e.g. RTL, RDL, DOC, VAL, ENV, etc).
    - Options for "area", in decreasing precedence (i.e., only one tag should be applied, matching the highest precedence tag from this list).
      - BUG FIX (An RTL fix that specifically resolves a bug in the source code)
      - RTL (i.e. for enhancements, features, refactoring)
      - RDL (illustrates that the commit may affect address map, might require RTL regeneration, etc)
      - VAL (The commit _only_ affects the test plan and bench design. This tag may be used for fixing bugs in test code, rather than the BUG FIX tag, because that tag is reserved for RTL bug fixes. If both RTL source code and testbenches are modified, the "RTL" area should be used)
      - UVM (A subset of VAL, but demonstrates that the commit only impacts UVM testbenches)
      - DOC (Only documentation files are affected, i.e. .md, .png, .jpg, .xlsx, .html)
      - ENV (compile.yml, *.vf file lists, any GH workflow file, tools/scripts/* changes, etc).
  - Pull Request Comment/Description:
    - Should include one bullet point for each item that is touched (i.e., 1 bullet for each bug fixed, 1 bullet for each feature addition, 1 bullet for each TB modification, 1 bullet for each documentation update, etc).
    - Should include one line for each GitHub issue that is resolved by the PR. That line should follow the format:<BR>`Resolves #<issue number>`<BR>This format causes GitHub to automatically close the issue upon Pull Request merge.

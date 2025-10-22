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
  - 50-character subject line
  - 72-character line breaks in the body
  - Tell "what" and "why"
    - e.g. "Fix bug in UVM testbench causing AXI transaction mismatch"
    - e.g. "Update FSM transitions based on XYZ to resolve missed error states"
  - NOTE: Prefixes are recommended for each commit in Git documentation. In caliptra-rtl, the prefix is mandated for Pull Request titles, but not for individual commits within a feature branch due to the use of squash-and-merge strategy.

### Pull Request Conventions

caliptra-rtl repository uses a squash strategy to merge changes from a Pull Request to the destination branch. This means that the title of the PR becomes the header of the commit in the destination branch's history. To improve debug, triage, readability, and preparation of change-lists, it is imperative that these commit headers be concise, meaningful, and consistent. The following conventions are used:
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
  - Title should be concise and capture highest-impact items. Pull Requests should ideally contain only the necessary changes for a single feature, fix, testcase, documentation area, or other area. However, RTL changes should always be accompanied by appropriate verification collateral and relevant documentation. In this case, the RTL change should be described in the Title, as this is the most meaningful change, while verification and documentation updates are implicit to the proposed changes. In some cases, multiple features may need to be compressed into a single Pull Request. In this circumstance, the title should capture the most impactful changes as concisely as possible as a comma-separated list.
  - Example Title:
    - `[RTL] Update Adams Bridge to v2.0, apply lint fixes, coverage updates`
  - Pull Request Description:
    - Include one bullet point for each item that is touched (i.e., 1 bullet for each bug fixed, 1 bullet for each feature addition, 1 bullet for each TB modification, 1 bullet for each documentation update, etc).
    - Include one line for each GitHub issue that is resolved by the PR. That line should follow the format:<BR>`Resolves #<issue number>`<BR>This format causes GitHub to automatically close the issue upon Pull Request merge.

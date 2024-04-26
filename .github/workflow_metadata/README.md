Files in this directory are used to support workflow checks that run on the caliptra-rtl repository using GitHub actions.

pr\_\* objects are used to validate a Pull Request run. This is in support of an honor based system that allows contributors to create internal pipelines (for example, to run tests with proprietary toolchains). The suggested procedure here is:
  1. Contributor develops a new feature and pushes a branch to the caliptra-rtl GitHub repository
  1. Contributor runs an internal workflow on a branch that contains the merge of the feature branch into main. This workflow includes the complete test-suite and (possibly) some additional checks required by the company policy of that contributor
    - All contributors MUST perform the following checks in their development pipeline:
      - VCS test of the complete L0 regression suite (smoke tests)
      - Lint check run against caliptra_top
  1. Upon successfully completing, the internal workflow runs the script [stamp_repo.sh](../scripts/stamp_repo.sh). This script:
    - Updates the pr\_timestamp file to the current date
    - Runs the hash script [file_hash.sh](../scripts/file_hash.sh) to measure the code that the workflow ran on (including the pr\_timestamp file)
    - Writes the hash to the pr\_hash file
  1. The internal workflow should commit the updates to pr\_timestamp and pr\_hash as the final commit to the feature branch
    - Note that the workflow should be run upon a branch containing the MERGE of the feature branch into main, but the updated stamp files should be committed directly to the feature branch
  1. Contributor creates a Pull Request to submit the feature branch to the GitHub `main` branch
  1. Pull Request triggers GitHub Actions to run
    - Verilator, etc
    - Check on the timestamp. If the timestamp is sufficiently outdated (predates the final commit to the branch by more than 1 hour) the feature branch is considered to have failed the internal workflow
    - Pull Request runs a hash on the branch fileset (including the timestamp), compares with the contents of pr\_hash. If the hash mismatches, the feature branch is considered to have failed the internal workflow
  1. Pull Request is allowed to be merged only once all Actions complete successfully

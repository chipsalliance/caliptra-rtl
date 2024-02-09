Files in this directory are used to support workflow checks that run on the repository using GitHub actions.

pr\_\* objects are used to validate a Pull Request run. This is in support of an honor based system that allows contributors to create internal pipelines (for example, to run tests with proprietary toolchains). The suggested procedure here is:
  1. Entity develops a new feature and pushes a branch to the caliptra-rtl GitHub repository
  1. Entity runs an internal workflow on the feature branch that includes the complete test-suite and (possibly) some additional checks required by the company policy
  1. Upon successfully completing, the internal workflow updates the pr\_timestamp file to the current date
  1. Then, (also contingent upon workflow success), the workflow runs the hash script [TODO](TODO_url) to measure the code that the workflow ran on
    - This includes the pr\_timestamp file
  1. The hash is written to the pr\_hash file
  1. Entity creates a Pull Request to submit the feature branch to the GitHub `main` branch
  1. Pull Request triggers GitHub Actions to run
    - Verilator, etc
    - Check on the timestamp. If the timestamp is sufficiently outdated (more than 1 day old) the feature branch is considered to have failed the internal workflow
    - Pull Request runs a hash on the branch fileset (including the timestamp), compares with the contents of pr\_hash. If the hash mismatches, the feature branch is considered to have failed the internal workflow
  1. Pull Request is allowed to be merged only once all Actions complete successfully

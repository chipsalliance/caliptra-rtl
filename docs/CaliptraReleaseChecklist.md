![OCP Logo](./images/OCP_logo.png)

<p style="text-align: center;">Caliptra Release Checklist</p>

<p style="text-align: center;">Version 2.0.1</p>

<div style="page-break-after: always"></div>

# Overview

This document provides the signoff checklist that is used when finalizing any Caliptra release version.

# Release Creation

## Versioning

Caliptra RTL releases may be created for new major, minor, or patch versions, as described in the [semantic versioning specification](https://semver.org/spec/v2.0.0.html). The version number is reflected in the [CPTRA_HW_REV_ID](https://chipsalliance.github.io/caliptra-rtl/main/internal-regs/?p=clp.soc_ifc_reg.CPTRA_HW_REV_ID) register. Steps described in this document are followed for each of these releases.

Pre-release versions are denoted with the alphanumeric key `rc<incrementing_numeric_value>` to indicate that the version is a release candidate. Release candidates are tagged to indicate that feature and validation effort has reached a finalized state, and the final release is pending further review. An example release candidate tag is: `v2.2.0-rc3`

Modifications may also be applied to the documentation of a patch release by opening pull requests to the `patch_v<MAJOR>.<MINOR>` branch. When a release receives updates to the documentation (with no other modifications) this is considered a new "build" from a versioning perspective. Semantic versioning specifies that build metadata can be included in a release version by appending build data to the version. The format for appending build information is: `<MAJOR>.<MINOR>.<PATCH>+<build_identifier>`.
In caliptra-rtl releases, the `build_identifier` is always an alphanumeric key that begins with a 1-indexed numeric value. The full format of the build identifier is: `<incrementing_numeric_value>.<alphanumeric_descriptor>`.
The only supported value for `<alphanumeric_descriptor>` is the keyword `doc`.

For example, a series of documentation updates to the 2.0.2 release of caliptra-rtl would be tagged as: `v2.0.2+1.doc`, `v2.0.2+2.doc`, ... , `v2.0.2+12.doc`.

Documentation updates are only applied to the latest patch release. That is, documentation updates to produce `v2.0.2+3.doc` are not applied to any `v2.0.1` release. A newer patch release inherits all documentation updates from prior patch releases, and may then be subsequently targeted for additional documentation updates. Thus, there is no guarantee that documentation from a given build is applicable to a prior patch release, as patch updates may have modified the area described in the documentation.

## Branches

Each major and minor release is created as a tag on the branch `main` of the caliptra-rtl repository. The tag is created using GitHub's repository release tagging feature, which also generates a zip file containing all of the code and documentation for that release. After tagging the release, any subsequent commits to `main` are pursuant to development efforts on future release versions, so the tagged release must be used to download the official release code.

When necessary, a patch release may be applied retroactively to earlier versions of Caliptra. In this case, a new branch is created to contain the patched code base. Patch release branches follow the naming convention, `patch_v<MAJOR>.<MINOR>`, to indicate which version is being patched. After the patched branch reaches its finalized state, a tag is created on the patch branch to indicate the full version number of that patch. Thus, any patch release is created as a tag on the same branch, with an incrementing patch version number.

## Steps

For each release, the following steps are followed to ensure code functionality and quality.

- Ensure all critical [issues](https://github.com/chipsalliance/caliptra-rtl/issues) and [Pull Requests](https://github.com/chipsalliance/caliptra-rtl/pulls) are closed
- Verify expected checks and scripts are in place
  - Audit pipelines: Coverage logging enabled
  - Audit pipelines: File list checks updated
  - Audit pipelines: License header check targets updated
  - Audit pipelines: RDL generator script is updated
  - Audit pipelines: RDL file checker is updated
  - Audit pipelines: Promote pipeline synth check enabled
  - Audit pipelines: Promote pipeline lint check enabled (and test a false-negative)
  - Audit pipelines: Promote pipeline L0 regression list updated
  - Audit pipelines: Promote pipeline L0 regression enabled
  - Audit pipelines: Promote pipeline unit tests enabled
  - Audit pipelines: Nightly pipeline firmware regression test list updated
  - Audit pipelines: Nightly pipeline firmware regression test list enabled
  - Audit pipelines: Nightly pipeline unit testbench regression test list updated
  - Audit pipelines: Nightly pipeline unit testbench regression test list enabled
  - Audit pipelines: Nightly pipeline UVM UNIT regressions test list updated
  - Audit pipelines: Nightly pipeline UVM UNIT regressions enabled
  - Audit pipelines: Nightly pipeline UVM TOP regression test list updated
  - Audit pipelines: Nightly pipeline UVM TOP regression enabled
  - Audit pipelines: Nightly pipeline UVM TOP (ROM) regression enabled
- Audit RTL and testbenches for FIXME/TODO items
- Pre-Silicon Regressions
  - [L0 regression](../src/integration/stimulus/L0_regression.yml)
  - Directed/Random regression per the [Test Plan](./Caliptra_TestPlan.xlsx)
- Coverage Review
  - Coverage database is manually reviewed to ensure all required coverpoints are exercised
- FPGA Validation
  - Latest RTL is tested in FPGA
- Register updates:
  - [CPTRA_HW_REV_ID](https://chipsalliance.github.io/caliptra-rtl/main/internal-regs/?p=clp.soc_ifc_reg.CPTRA_HW_REV_ID): Update version information according to the defined field mapping to match current release
  - [CPTRA_HW_CONFIG](https://chipsalliance.github.io/caliptra-rtl/main/internal-regs/?p=clp.soc_ifc_reg.CPTRA_HW_CONFIG): Update any fields to indicate a change in Caliptra capabilities
- Lint review:
  - Lint must be completely clean after applying policies and waivers described in [Caliptra Integration Specification](./CaliptraIntegrationSpecification.md#Recommended-LINT-rules)
- CDC review:
  - All clock crossings are safely synchronized, appropriate constraints are defined
- RDC review
  - All reset domain crossings are safely managed by hardware controls or reviewed and waived
- Formal Verification review
  - Formal test plans for cryptographic blocks are executed and pass
- Update documentation
  - Update lint rules in integration specification
  - Core logic changes documented in the [CaliptraHardwareSpecification](./CaliptraHardwareSpecification.md)
  - [README](../README.md) updates
  - Add latest synthesis results to the [CaliptraIntegrationSpecification](./CaliptraIntegrationSpecification.md#netlist-synthesis-data)
  - Update [Release_Notes](../Release_Notes.md)
  - Tag the main branch on GitHub to generate an official release
  - Generate version-specific registers documentation page in the [Register Documentation Workflow](./.github/workflows/doc-gen.yml)

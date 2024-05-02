![OCP Logo](./images/OCP_logo.png)

<p style="text-align: center;">Caliptra Release Checklist</p>

<p style="text-align: center;">Version 1.1</p>

<div style="page-break-after: always"></div>

# Overview

This document provides the signoff checklist that is used when finalizing any Caliptra release version.

# Release Creation

## Versioning

Caliptra RTL releases may be created for new major, minor, or patch versions, as described in the [semantic versioning specification](https://semver.org/spec/v2.0.0.html). The version number is reflected in the register CPTRA_HW_REV_ID. Steps described in this document are followed for each of these releases.

## Branches

Each major and minor release is created as a tag on the branch `main` of the caliptra-rtl repository. The tag is created using GitHub's repository release tagging feature, which also generates a zip file containing all of the code and documentation for that release. After tagging the release, any subsequent commits to `main` are pursuant to development efforts on future release versions, so the tagged release must be used to download the official release code.

When necessary, a patch release may be applied retroactively to earlier versions of Caliptra. In this case, a new branch is created to contain the patched code base. Patch release branches will follow the naming convention `patch_v<MAJOR>.<MINOR>` to indicate which version is being patched. Once the patched branch has reached it's finalized state, a tag is created on the patch branch to indicate the full version number of that patch. Thus, any patch release will be created as a tag on the same branch, of an incrementing patch version number.

## Steps

For each release, the following steps are followed to ensure code functionality and quality.

- Ensure all critical [issues](https://github.com/chipsalliance/caliptra-rtl/issues) and [Pull Requests](https://github.com/chipsalliance/caliptra-rtl/pulls) are closed
- Pre-Silicon Regressions
  - [L0 regression](../src/integration/stimulus/L0_regression.yml)
  - Directed/Random regression per the [Test Plan](./Caliptra_TestPlan.xlsx)
- Coverage Review
  - Coverage database is manually reviewed to ensure all required coverpoints are exercised
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
#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
import os
import json
import yaml

def main():

    # Load and parse YAML description    
    file_name = "src/integration/stimulus/L0_regression.yml"
    with open(file_name, "r") as fp:
        yaml_root = yaml.safe_load(fp)

    # Get excluded test list
    excluded = os.environ.get("EXCLUDE_TESTS", "")
    excluded = [s.strip() for s in excluded.strip().split(",")]

    # Get test list
    content = yaml_root["contents"][0]
    tests = content["tests"]
    paths = tests["paths"]

    # Extract test names from paths
    test_list = []
    for path in paths:
        parts = path.split("/")

        for i, part in enumerate(parts):
            if part == "test_suites" and i + 1 < len(parts):
                test_name = parts[i+1]
                if test_name not in excluded:
                    test_list.append(test_name)
                break

    # Extract per-test runtime plusargs from each test's own <test>.yml under
    # "plusargs:". BFM-gating plusargs (e.g. +CALIPTRA_TEST_STASH_BANK for the
    # RFC #673 stash-bank tests) must reach the Verilator sim or the bench never
    # executes its expected behavior and the test hangs. These are attached to
    # the matrix via "include" so the workflow can pass them as RUN_PLUSARGS,
    # while "test_name" remains the primary matrix dimension (clean job names).
    include = []
    for test_name in test_list:
        test_yml = f"src/integration/test_suites/{test_name}/{test_name}.yml"
        plusargs = []
        try:
            with open(test_yml, "r") as fp:
                test_cfg = yaml.safe_load(fp) or {}
            plusargs = test_cfg.get("plusargs") or []
        except FileNotFoundError:
            pass
        include.append({
            "test_name": test_name,
            "plusargs": " ".join(str(p) for p in plusargs),
        })

    # Emit the full matrix object (valid JSON) for the workflow's
    # `strategy: matrix: ${{ fromJSON(...) }}`.
    print(json.dumps({"test_name": test_list, "include": include}))

if __name__ == "__main__":
    main()

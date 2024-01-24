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

    # Output names
    print(test_list)

if __name__ == "__main__":
    main()

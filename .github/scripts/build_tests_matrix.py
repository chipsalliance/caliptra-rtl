#!/usr/bin/env python3
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

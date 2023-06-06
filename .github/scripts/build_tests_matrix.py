#!/usr/bin/env python3
import yaml

def main():

    # Load and parse YAML description    
    file_name = "src/integration/stimulus/L0_regression.yml"
    with open(file_name, "r") as fp:
        yaml_root = yaml.safe_load(fp)

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
                test_list.append(parts[i+1])
                break

    # Output names
    print(test_list)

if __name__ == "__main__":
    main()

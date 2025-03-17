import csv
import os
import logging
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import DoubleQuotedScalarString
from ruamel.yaml.comments import CommentedMap, CommentedSeq
import re

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Add file handler for DEBUG level
file_handler = logging.FileHandler('debug.log')
file_handler.setLevel(logging.DEBUG)
file_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
logger.addHandler(file_handler)

def generate_output_filename(csv_file_path, criteria):
    parts = []
    for key in ["L0|L1", "Nightly|Weekly", "PromotePipeline", "Directed|Random", "DUT"]:
        if criteria.get(key):
            parts.append(criteria[key])
    directory = os.path.dirname(csv_file_path)
    filename = "_".join(parts) + "_regression.yml"
    return os.path.join(directory, filename)

def csv_to_yaml(csv_file_path, yml_file_path, criteria, generations):
    # Required headers
    required_headers = ["TestName", "Directed|Random", "Nightly|Weekly", "L0|L1", "DUT", "PromotePipeline", "OtherTags", "Weight"]

    # Read the CSV file and filter the data
    filtered_data = []
    with open(csv_file_path, mode='r', encoding='utf-8') as csv_file:
        csv_reader = csv.DictReader(csv_file)
        headers = [header.strip() for header in csv_reader.fieldnames]

        # Debug: Log headers
        logger.debug(f"CSV Headers: {headers}")

        # Check for required headers
        for header in required_headers:
            if header not in headers:
                raise KeyError(f"Required header '{header}' not found in the CSV file.")

        # Debug: Log a sample row
        for row in csv_reader:
            logger.debug(f"Sample row: {row}")
            break  # Just log the first row for debugging

    # Re-read the CSV file and filter the data
    with open(csv_file_path, mode='r', encoding='utf-8') as csv_file:
        csv_reader = csv.DictReader(csv_file)
        for row in csv_reader:
            # Strip spaces from keys and values in each row
            row = {key.strip(): value.strip() for key, value in row.items()}

            # Debug: Log comparison values
            logger.debug(f"Comparing row values with criteria: {row} with {criteria}")

            if (
                row["Directed|Random"] == criteria["Directed|Random"]
                and (row["Nightly|Weekly"] == criteria["Nightly|Weekly"] or criteria["Nightly|Weekly"] == "" or row["Nightly|Weekly"] == "None")
                and row["L0|L1"] == criteria["L0|L1"]
                and row["DUT"] == criteria["DUT"]
                and (criteria["PromotePipeline"] == row["PromotePipeline"] or criteria["PromotePipeline"] is None)
            ):
                filtered_data.append(row)

    # Debug: Log filtered data size
    logger.debug(f"Filtered data size: {len(filtered_data)}")

    # Prepare the YAML structure using CommentedMap and CommentedSeq for better control
    tags = CommentedSeq([DoubleQuotedScalarString(criteria[key]) for key in ["L0|L1", "DUT", "Directed|Random", "Nightly|Weekly"] if criteria[key] is not None])
    
    # Add OtherTags if it's not None
    if criteria.get("OtherTags"):
        tags.append(DoubleQuotedScalarString(criteria["OtherTags"]))
    tags.fa.set_flow_style()

    generator_data = CommentedMap()
    generator_data['generator'] = CommentedMap()
    generator_data['generator']['tags'] = tags
    generator_data['generator']['path'] = DoubleQuotedScalarString("")
    generator_data['generator']['weight'] = 100
    generator_data['generator']['generations'] = generations
    
    # Use different formats based on PromotePipeline
    if criteria.get("PromotePipeline") == "Promote":
        generator_data['generator']['formats'] = CommentedMap([
            ('generate', DoubleQuotedScalarString("reseed {template}.yml -seed 1")),
            ('path', DoubleQuotedScalarString("{template_basename}__1.yml"))
        ])
    else:
        generator_data['generator']['formats'] = CommentedMap([
            ('generate', DoubleQuotedScalarString("reseed {template}.yml -seed {seed}")),
            ('path', DoubleQuotedScalarString("{template_basename}__{seed}.yml"))
        ])
        

    templates = CommentedMap()
    for row in filtered_data:
        template_path = row["TestName"]
        templates[template_path] = CommentedMap([('weight', int(row["Weight"]))])
        templates[template_path].fa.set_flow_style()

    generator_data['generator']['templates'] = templates

    # Add timeout if specified
    if "timeout" in criteria:
        generator_data["generator"]["config"] = {
            "params": {
                "timeout": criteria["timeout"]
            }
        }

    # Wrap generator_data in a list for the contents section
    contents = CommentedSeq([generator_data])
    
    # Create the final document structure
    document = CommentedMap()
    document["document"] = CommentedMap([('schema', 1.0)])  # Add schema version
    document["contents"] = contents

    # Use ruamel.yaml for better control over YAML formatting
    yaml = YAML()
    yaml.default_flow_style = False
    yaml.indent(sequence=4, offset=2)

    # Write the document to the file
    with open(yml_file_path, mode='w', encoding='utf-8') as yml_file:
        yaml.dump(document, yml_file)

    # Post-process the generated YAML file to fix lines with question marks and extra colons
    with open(yml_file_path, mode='r', encoding='utf-8') as yml_file:
        lines = yml_file.readlines()

    with open(yml_file_path, mode='w', encoding='utf-8') as yml_file:
        previous_line = None
        for line in lines:
            logger.debug(f"Current line: {line}")
            if line.strip().startswith('contents'):
                yml_file.write('\n')
                yml_file.write(line)
            elif re.search(r'^\s*\?\s*', line):
                logger.debug(f"Question mark line: {line}")
                indent = re.match(r'^\s*', line).group(0)
                line = re.sub(r'^\s*\?\s*', '', line)
                previous_line = f'{indent}{line.rstrip()}'
            elif re.search(r'^\s*\:\s*', line):
                logger.debug(f"Colon line: {line}")
                logger.debug(f"Previous line: {previous_line}")
                indent = re.match(r'^\s*', line).group(0)
                line = re.sub(r'^\s*\:\s*', '', line)
                current_line = f'{indent}{line}'
                yml_file.write(f'{previous_line}: {current_line}')
                previous_line = None
            elif re.search(r'\s+\{$', line):
                indent = re.match(r'^\s*', line).group(0)
                line = re.sub(r'^\s*', '', line)
                previous_line = f'{indent}{line.rstrip()}'
                logger.debug(f"Modified to {previous_line}")
            elif re.search(r'^\s*weight', line) and previous_line is not None:
                line = re.sub(r'^\s*', '', line)
                yml_file.write(f'{previous_line} {line.rstrip()}\n')
                previous_line = None
            else:
                if previous_line:
                    yml_file.write(f'{previous_line}\n')
                    previous_line = None
                yml_file.write(line)


if __name__ == "__main__":
    caliptra_root = os.getenv('CALIPTRA_ROOT')
    csv_file_path = os.path.join(caliptra_root, 'src/integration/stimulus/testsuites/caliptra_top_master_test_list.csv')

    combinations = [
        {"Directed|Random": "Directed", "Nightly|Weekly": "Nightly", "L0|L1": "L1", "DUT": "caliptra_top_tb", "PromotePipeline": None, "generations": 1},
        {"Directed|Random": "Random", "Nightly|Weekly": "Nightly", "L0|L1": "L1", "DUT": "uvmf_caliptra_top", "PromotePipeline": None, "generations": 500, "timeout": 720},
        {"Directed|Random": "Random", "Nightly|Weekly": "Nightly", "L0|L1": "L1", "DUT": "caliptra_top_tb", "PromotePipeline": None, "generations": 2000},
        {"Directed|Random": "Directed", "Nightly|Weekly": "Nightly", "L0|L1": "L1", "DUT": "uvmf_caliptra_top_itrng", "PromotePipeline": None, "generations": 1, "timeout": 1440},
        {"Directed|Random": "Directed", "Nightly|Weekly": None, "L0|L1": "L0", "DUT": "uvmf_caliptra_top", "PromotePipeline": "Promote", "generations": 6}
    ]

    for criteria in combinations:
        output_filename = generate_output_filename(csv_file_path, criteria)
        logger.info(f"Creating YAML file '{output_filename}' ")
        csv_to_yaml(csv_file_path, output_filename, criteria, criteria["generations"])
        logger.info(f"YAML file '{output_filename}' successfully created.")

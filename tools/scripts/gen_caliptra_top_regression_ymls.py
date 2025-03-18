import csv
import os
import logging
import glob
import pprint
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
    
    # Special handling for L0 regression files
    if criteria.get("L0") == "L0":
        # For L0 regression, only use L0, PromotePipeline, and DUT criteria
        if criteria.get("L0"):
            parts.append(criteria["L0"])
        if criteria.get("PromotePipeline"):
            parts.append(criteria["PromotePipeline"])
        if criteria.get("DUT"):
            parts.append(criteria["DUT"])
    else:
        # For other regression files, use all criteria
        for key in ["L0", "L1", "Nightly|Weekly", "PromotePipeline", "Directed|Random", "DUT"]:
            if criteria.get(key):
                parts.append(criteria[key])
    
    parent_directory = os.path.dirname(os.path.dirname(csv_file_path))
    filename = "_".join(parts) + "_regression.yml"
    return os.path.join(parent_directory, filename)

def csv_to_yaml(csv_file_path, yml_file_path, criteria, generations):
    # Required headers
    required_headers = ["TestName", "Directed|Random", "Nightly|Weekly", "L0", "L1", "DUT", "PromotePipeline", "OtherTags", "Weight"]

    # Read the CSV file and filter the data
    filtered_data = []
    with open(csv_file_path, mode='r', encoding='utf-8') as csv_file:
        csv_reader = csv.DictReader(csv_file)
        headers = [header.strip() for header in csv_reader.fieldnames]

        # Check for required headers
        for header in required_headers:
            if header not in headers:
                raise KeyError(f"Required header '{header}' not found in the CSV file.")

    # Re-read the CSV file and filter the data
    with open(csv_file_path, mode='r', encoding='utf-8') as csv_file:
        csv_reader = csv.DictReader(csv_file)
        logger.debug(f"Looking for rows that match criteria: {criteria}")
        
        for row in csv_reader:
            # Strip spaces from keys and values in each row
            row = {key.strip(): value.strip() for key, value in row.items()}
            
            # Check if this is an L0 regression case
            if criteria.get("L0") == "L0":
                # For L0 regression, focus only on L0, DUT, and PromotePipeline
                l0_match = (row["L0"] == "L0")
                dut_match = (row["DUT"] == criteria["DUT"])
                promote_match = (row["PromotePipeline"] == "Promote")
                
                logger.debug(f"Testing L0 criteria for: {row['TestName']}")
                logger.debug(f"  L0: {row['L0']} == L0? {l0_match}")
                logger.debug(f"  DUT: {row['DUT']} == {criteria['DUT']}? {dut_match}")
                logger.debug(f"  PromotePipeline: {row['PromotePipeline']} == Promote? {promote_match}")
                
                if l0_match and dut_match and promote_match:
                    logger.info(f"✅ L0 MATCH: {row['TestName']}")
                    filtered_data.append(row)
                else:
                    logger.debug(f"❌ No match for L0 regression: {row['TestName']}")
            else:
                # For other regression types, use original matching logic
                dir_rand_match = (row["Directed|Random"] == criteria["Directed|Random"] or row["Directed|Random"] == "None")
                nw_match = (row["Nightly|Weekly"] == criteria["Nightly|Weekly"] or criteria["Nightly|Weekly"] is None or 
                            criteria["Nightly|Weekly"] == "" or row["Nightly|Weekly"] == "None")
                l0_match = (row["L0"] == criteria["L0"] or row["L0"] == "None")
                l1_match = (row["L1"] == criteria["L1"] or row["L1"] == "None")
                dut_match = (row["DUT"] == criteria["DUT"])
                promote_match = (criteria["PromotePipeline"] == row["PromotePipeline"] or criteria["PromotePipeline"] is None)
                
                all_match = dir_rand_match and nw_match and l0_match and l1_match and dut_match and promote_match
                
                if all_match:
                    logger.info(f"✅ Standard match: {row['TestName']}")
                    filtered_data.append(row)
                else:
                    logger.debug(f"❌ No match for standard regression: {row['TestName']}")

    # Debug: Log filtered data
    logger.info(f"Filtered data size: {len(filtered_data)}")
    logger.info("Filtered data details:")
    for item in filtered_data:
        logger.info(f"  - {item['TestName']}")
        
    # Exit early if no matches were found
    if not filtered_data:
        logger.warning(f"No templates matched for criteria: {criteria}")
        # Create an empty YAML file to indicate processing was done
        with open(yml_file_path, mode='w', encoding='utf-8') as yml_file:
            yml_file.write("# No matching templates found for criteria\n")
            yml_file.write(f"# {criteria}\n")
        return

    # Adjust generations based on criteria
    template_count = len(filtered_data)
    if criteria.get("L0") == "L0" or criteria.get("PromotePipeline") == "Promote":
        adjusted_generations = template_count
        logger.info(f"Setting generations to {adjusted_generations} (match template count for L0 or PromotePipeline)")
    else:
        # For other criteria, set to 10x template count
        adjusted_generations = max(generations, template_count * 10)
        logger.info(f"Setting generations to {adjusted_generations} (10x template count)")
    generations = adjusted_generations

    # Create YAML structure
    document = create_yaml_document(filtered_data, criteria, generations)

    # Debug: Print the document structure
    logger.debug("YAML document structure:")
    logger.debug(pprint.pformat(document))

    # Write YAML file
    write_yaml_file(document, yml_file_path, filtered_data)
    
    logger.info(f"YAML file '{yml_file_path}' created with {len(filtered_data)} templates.")

def create_yaml_document(filtered_data, criteria, generations):
    # Prepare the YAML structure using CommentedMap and CommentedSeq for better control
    #tags = CommentedSeq([DoubleQuotedScalarString(criteria[key]) for key in ["L0", "L1", "DUT", "Directed|Random", "Nightly|Weekly"] if criteria.get(key) is not None])
    
    # Add OtherTags if it's not None
    #if criteria.get("OtherTags"):
    #    tags.append(DoubleQuotedScalarString(criteria["OtherTags"]))
    #tags.fa.set_flow_style()

    # Only include tags that are not 'Either' or 'None'
    tags = CommentedSeq([
        DoubleQuotedScalarString(criteria[key]) 
        for key in ["L0", "L1", "DUT", "Directed|Random", "Nightly|Weekly"] 
        if criteria.get(key) is not None and criteria.get(key) != 'Either' and criteria.get(key) != 'None'
    ])
    
    # Add OtherTags if it's not None, 'Either', or 'None'
    if criteria.get("OtherTags") and criteria.get("OtherTags") != 'Either' and criteria.get("OtherTags") != 'None':
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

    # Create templates section
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
    
    return document

def write_yaml_file(document, yml_file_path, filtered_data):
    # Use ruamel.yaml for better control over YAML formatting
    yaml = YAML()
    yaml.default_flow_style = False
    yaml.indent(sequence=4, offset=2)

    logger.info(f"Writing YAML file with {len(filtered_data)} templates")
    
    # Dump the document to a string first to debug
    import io
    string_stream = io.StringIO()
    yaml.dump(document, string_stream)
    yaml_content = string_stream.getvalue()
    logger.debug(f"YAML content to be written:\n{yaml_content}")

    # Write to the actual file
    try:
        with open(yml_file_path, mode='w', encoding='utf-8') as yml_file:
            yaml.dump(document, yml_file)
            logger.info(f"Successfully wrote to {yml_file_path}")
    except Exception as e:
        logger.error(f"Error writing YAML file: {e}")
        raise

    # Post-process the generated YAML file to fix lines with question marks and extra colons
    with open(yml_file_path, mode='r', encoding='utf-8') as yml_file:
        lines = yml_file.readlines()

    with open(yml_file_path, mode='w', encoding='utf-8') as yml_file:
        previous_line = None
        logger.debug(f"Previous line: {previous_line}")
        for line in lines:
            logger.debug(f"DEBUG: Current line: {line}")
            if line.strip().startswith('contents'):
                logger.debug(f"Condition #1")
                yml_file.write('\n')
                yml_file.write(line)
            elif re.search(r'^\s*\?\s*', line):
                logger.debug(f"Condition #2")
                indent = re.match(r'^\s*', line).group(0)
                line = re.sub(r'^\s*\?\s*', '', line)
                previous_line = f'{indent}{line.rstrip()}'
                logger.debug(f"Previous line: {previous_line}")
            elif re.search(r'^\s*\:\s*', line):
                logger.debug(f"Condition #3")
                indent = re.match(r'^\s*', line).group(0)
                line = re.sub(r'^\s*\:\s*', '', line)
                current_line = f'{indent}{line}'
                yml_file.write(f'{previous_line}: {current_line}')
                previous_line = None
            elif re.search(r'\s+\{$', line):
                logger.debug(f"Condition #4")
                indent = re.match(r'^\s*', line).group(0)
                line = re.sub(r'^\s*', '', line)
                previous_line = f'{indent}{line.rstrip()}'
                logger.debug(f"Previous line: {previous_line}")
            elif re.search(r'^\s*weight', line) and previous_line is not None:
                logger.debug(f"Condition #5")
                line = re.sub(r'^\s*', '', line)
                logger.debug(f"Write back: {previous_line} {line.rstrip()}\n")
                yml_file.write(f'{previous_line} {line.rstrip()}\n')
                previous_line = None
            else:
                logger.debug(f"Condition #6")
                if previous_line:
                    yml_file.write(f'{previous_line}\n')
                    previous_line = None
                yml_file.write(line)
    
    # Verify the file was written
    file_size = os.path.getsize(yml_file_path)
    logger.info(f"Final YAML file size: {file_size} bytes")


def scan_test_suites(caliptra_ss):
    """Scan through all src/<ip>/test_suites/ directories."""
    logger.info("Scanning for test suites...")
    
    search_pattern = os.path.join(caliptra_ss, "src", "*", "test_suites")
    test_suite_dirs = glob.glob(search_pattern)
    logger.debug(f"Found {len(test_suite_dirs)} test_suites directories: {test_suite_dirs}")
    
    all_tests = []
    
    for test_dir in test_suite_dirs:
        ip_name = os.path.basename(os.path.dirname(test_dir))
        logger.info(f"Scanning tests for IP: {ip_name}")
        
        for root, dirs, files in os.walk(test_dir):
            if 'includes' in dirs:
                dirs.remove('includes')
            if 'libs' in dirs:
                dirs.remove('libs')
            
            for file in files:
                if file.endswith('.yml') or file.endswith('.yaml'):
                    rel_path = os.path.relpath(os.path.join(root, file), test_dir)
                    test_name = f"{ip_name}/{rel_path}"
                    all_tests.append(test_name)
    
    all_tests.sort()
    
    logger.info(f"Found {len(all_tests)} tests:")
    for test in all_tests:
        logger.info(f"  - {test}")
    
    return all_tests


if __name__ == "__main__":
    caliptra_root = os.getenv('CALIPTRA_ROOT')

    if not caliptra_root:
        logger.error("CALIPTRA_ROOT environment variable is not set. Please set it before running this script.")
        exit(1)
    
    csv_file_path = os.path.join(caliptra_root, 'src/integration/stimulus/testsuites/caliptra_top_master_test_list.csv')

    # Display a few lines of CSV for debugging
    logger.info("First few lines of CSV file:")
    try:
        with open(csv_file_path, mode='r', encoding='utf-8') as csv_file:
            for i, line in enumerate(csv_file):
                if i < 5:  # Show first 5 lines
                    logger.info(f"Line {i}: {line.strip()}")
                else:
                    break
    except Exception as e:
        logger.error(f"Error reading CSV file: {e}")

    combinations = [
        {"Directed|Random": "Either", "Nightly|Weekly": "Either", "L0": "L0", "L1": None, "DUT": "caliptra_top_tb", "PromotePipeline": "Promote"},
        {"Directed|Random": "Either", "Nightly|Weekly": "Either", "L0": "L0", "L1": None, "DUT": "caliptra_top_trng_tb", "PromotePipeline": "Promote"},
        {"Directed|Random": "Directed", "Nightly|Weekly": "Nightly", "L0": None, "L1": "L1", "DUT": "caliptra_top_tb", "PromotePipeline": None},
        {"Directed|Random": "Random", "Nightly|Weekly": "Nightly", "L0": None, "L1": "L1", "DUT": "uvmf_caliptra_top", "PromotePipeline": None, "timeout": 720},
        {"Directed|Random": "Random", "Nightly|Weekly": "Nightly", "L0": None, "L1": "L1", "DUT": "caliptra_top_tb", "PromotePipeline": None},
        {"Directed|Random": "Directed", "Nightly|Weekly": "Nightly", "L0": None, "L1": "L1", "DUT": "uvmf_caliptra_top_itrng", "PromotePipeline": None, "timeout": 1440},
        {"Directed|Random": "Directed", "Nightly|Weekly": None, "L0": "L0", "L1": None, "DUT": "uvmf_caliptra_top", "PromotePipeline": "Promote"}
    ]

    # Process each combination
    for criteria in combinations:
        output_filename = generate_output_filename(csv_file_path, criteria)
        logger.info(f"\n\n===== Creating YAML file '{output_filename}' =====")
        logger.info(f"Using criteria: {criteria}")
        
        try:
            csv_to_yaml(csv_file_path, output_filename, criteria, 1)
            logger.info(f"YAML file '{output_filename}' successfully created.")
        except Exception as e:
            logger.error(f"Error creating YAML file: {e}")
            import traceback
            logger.error(traceback.format_exc())
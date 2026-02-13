!/bin/bash
# Licensed under the Apache-2.0 license

# Constants
modify_table_title="Caliptra integrator custom RTL file list"
integration_spec_relative_path="docs/CaliptraIntegrationSpecification.md"

# Check arg count
if [ $# -lt 1 ] || [ $# -gt 3 ]
  then
    echo "Usage: $(basename $0) <path_to_rtl> [baseline_release_tag] [diff_output_dir]"
    echo "  path_to_rtl             Path to the RTL repository"
    echo "  baseline_release_tag    (Optional) Release tag to diff against (lists available if not provided)"
    echo "  diff_output_dir         (Optional) Directory for diff outputs (default: rtl_diffs)"
    exit -1
fi

# Get args
rtl_path=$1
baseline_release=$2
diff_output_dir=${3:-rtl_diffs}

rtl_src_path="$rtl_path"/src
integration_spec="$rtl_path"/"$integration_spec_relative_path"

# Change to rtl_path to work with git
pushd "$rtl_path" > /dev/null

# If baseline release is not provided, list available releases and prompt
if [ -z "$baseline_release" ]; then
    echo "Available release tags:"
    git tag -l | sort -V
    echo ""
    read -p "Enter baseline release tag (or press Enter to skip diff generation): " baseline_release

    # If still empty, skip diff generation
    if [ -z "$baseline_release" ]; then
        echo "No baseline specified. Skipping diff generation."
        baseline_release=""
    fi
fi

# If baseline release is specified, validate it's a valid tag
if [ -n "$baseline_release" ]; then
    if ! git rev-parse "$baseline_release" >/dev/null 2>&1; then
        echo "Error: '$baseline_release' is not a valid git tag"
        popd > /dev/null
        exit -1
    fi

    # Verify it's actually a tag (not just any commit)
    if ! git tag -l | grep -q "^${baseline_release}$"; then
        echo "Error: '$baseline_release' is not a release tag. Only release tags are allowed."
        echo "Available tags:"
        git tag -l | sort -V
        popd > /dev/null
        exit -1
    fi

    echo "Using baseline release: $baseline_release"
fi

popd > /dev/null

echo "Generating RTL file list"

# Get list of RTL files that should be modified
modify_file_table=$(cat "$integration_spec" | sed -n "/$modify_table_title/,/^# /p" | grep "|")

# Extract the file names from the table
exclude_list=$(echo "$modify_file_table" | grep -o -P '(?<=\]\(../src/)[^ ]*(?=\) *\|)')

# Make sure files were found in the integration spec table
exclude_list_count=$(echo -n "$exclude_list" | grep -c '^')
if [ $exclude_list_count -lt 2 ]; then
    echo "$(basename $0): Error parsing integration spec for file list, expected at least 2 files. Found $exclude_list_count"
    exit -1
fi

# From this point on, exit and report failure if anything fails
set -euo pipefail

# Get all files of the right types within the RTL src (only .sv, .svh, .rdl, .v, and .vh files)
file_list=$(find "$rtl_src_path" -type f -iname *.sv -o -iname *.svh -o -iname *.rdl -o -iname *.v -o -iname *.vh | sort)

# Remove the rtl src path to get a relative path
file_list=$(echo "$file_list" | sed "s@$rtl_src_path@@")
# Remove a leading slash if present
file_list=$(echo "$file_list" | sed "s@^/@@")

# Filter out the files from the modify list
echo "Filtering out files on exclude list"
while read line; do
	# Print the files we are removing first for a sanity check
	echo "  " $(echo "$file_list" | grep $line)
	# Update the list with the file removed
	file_list=$(echo "$file_list" | grep -v $line)
done < <(echo "$exclude_list")

# Filter out files exclusive to testing
# Remove all UVMF files
echo "Filtering out uvmf files"
file_list=$(echo "$file_list" | grep -v -i "uvmf")

# Remove test bench files
echo "Filtering out tb directories"
file_list=$(echo "$file_list" | grep -v -i "/tb/")

# Remove asserts
echo "Filtering out asserts directories"
file_list=$(echo "$file_list" | grep -v -i "/asserts/")

# Function to generate diffs for a list of files
# Parameters: file_list, output_dir
# Sets global variables: diff_count, new_file_count, no_diff_count, unchanged_files
generate_diffs() {
    local file_list="$1"
    local output_dir="$2"

    # Reset counters and unchanged files list
    diff_count=0
    new_file_count=0
    no_diff_count=0
    unchanged_files=""

    # Create output directory
    mkdir -p "$output_dir"

    # Must be in rtl_path for git operations
    # Generate diff for each file in the list
    while IFS= read -r file; do
        if [ -z "$file" ]; then
            continue
        fi

        full_file_path="src/$file"

        # Create output filename by replacing / with _ and adding .diff extension
        diff_filename=$(echo "$file" | tr '/' '_').diff
        diff_output_path="$output_dir/$diff_filename"

        # Check if file exists in baseline
        if git cat-file -e "$baseline_release:$full_file_path" 2>/dev/null; then
            # Generate diff
            diff_output=$(git diff "$baseline_release" -- "$full_file_path" 2>/dev/null)

            if [ -n "$diff_output" ]; then
                echo "$diff_output" > "$diff_output_path"
                echo "  [MODIFIED] $file"
                diff_count=$((diff_count + 1))
            else
                echo "  [NO CHANGE] $file"
                no_diff_count=$((no_diff_count + 1))
                unchanged_files="${unchanged_files}${file}"$'\n'
            fi
        else
            # File is new (didn't exist in baseline)
            echo "  [NEW FILE] $file"
            git show "HEAD:$full_file_path" > "$diff_output_path" 2>/dev/null || echo "# New file: $file" > "$diff_output_path"
            new_file_count=$((new_file_count + 1))
        fi
    done < <(echo "$file_list")

}

# Generate diffs if baseline release is specified
if [ -n "$baseline_release" ]; then
    echo ""
    echo "Generating diffs against baseline release: $baseline_release"

    # Convert diff_output_dir to absolute path
    if [[ "$diff_output_dir" != /* ]]; then
        diff_output_dir="$(pwd)/$diff_output_dir"
    fi

    # Change to rtl_path for git operations
    pushd "$rtl_path" > /dev/null

    # Generate diffs for main file list
    generate_diffs "$file_list" "$diff_output_dir"

    # Check for deleted files (existed in baseline but not in current file list)
    deleted_file_count=0
    # Get list of files from baseline release that match our criteria
    baseline_files=$(git ls-tree -r --name-only "$baseline_release" | grep "^src/" | grep -E '\.(sv|svh|rdl|v|vh)$' | sed 's@^src/@@' || true)

    # Compare with current file list to find deleted files
    while IFS= read -r baseline_file; do
        if [ -z "$baseline_file" ]; then
            continue
        fi

        # Check if this baseline file exists in current file list
        if ! echo "$file_list" | grep -qF "$baseline_file"; then
            # Check if file still exists in current working tree
            if [ ! -f "src/$baseline_file" ]; then
                echo "  [DELETED] $baseline_file"
                deleted_file_count=$((deleted_file_count + 1))
            fi
        fi
    done < <(echo "$baseline_files")

    popd > /dev/null

    echo ""
    echo "Diff generation complete:"
    echo "  Modified files: $diff_count"
    echo "  New files: $new_file_count"
    echo "  Deleted files: $deleted_file_count"
    echo "  Unchanged files: $no_diff_count"
    echo "  Diff output directory: $diff_output_dir"

    # Generate diffs for expected-to-be-modified files (from integration spec table)
    echo ""
    echo "Generating diffs for expected-to-be-modified files (integration spec table):"

    expected_diff_dir="${diff_output_dir}_expected"

    # Change to rtl_path for git operations
    pushd "$rtl_path" > /dev/null

    # Check for missing expected-to-be-modified files first
    expected_missing_count=0
    expected_existing_list=""
    while IFS= read -r expected_file; do
        if [ -z "$expected_file" ]; then
            continue
        fi

        # Check if file exists in current working tree
        if [ ! -f "src/$expected_file" ]; then
            echo "  [MISSING] $expected_file"
            expected_missing_count=$((expected_missing_count + 1))
        else
            # Add to list of existing files to process
            expected_existing_list="${expected_existing_list}${expected_file}"$'\n'
        fi
    done < <(echo "$exclude_list")

    # Generate diffs for expected-to-be-modified files that exist
    generate_diffs "$expected_existing_list" "$expected_diff_dir"

    # Save the results for the expected files
    expected_diff_count=$diff_count
    expected_new_file_count=$new_file_count
    expected_no_diff_count=$no_diff_count
    expected_unchanged_files="$unchanged_files"

    popd > /dev/null

    echo ""
    echo "Expected-to-be-modified files diff generation complete:"
    echo "  Modified files: $expected_diff_count"
    echo "  New files: $expected_new_file_count"
    echo "  Missing files: $expected_missing_count"
    echo "  Unchanged files: $expected_no_diff_count"
    echo "  Diff output directory: $expected_diff_dir"

    # Warn if any expected-to-be-modified files are unchanged
    if [ $expected_no_diff_count -gt 0 ]; then
        echo ""
        echo "WARNING: The following files are listed in the integration spec as expected to be modified,"
        echo "         but have not been changed compared to baseline release $baseline_release:"
        echo ""
        echo "$expected_unchanged_files" | while IFS= read -r file; do
            if [ -n "$file" ]; then
                echo "  - $file"
            fi
        done
    fi
fi

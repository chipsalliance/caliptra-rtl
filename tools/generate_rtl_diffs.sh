#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
#
#
# Licensed under the Apache License, Version 2.0 (the \"License\");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an \"AS IS\" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License."

# Constants
modify_table_title="Caliptra integrator custom RTL file list"
integration_spec_relative_path="docs/CaliptraIntegrationSpecification.md"
upstream_repo_url="https://github.com/chipsalliance/caliptra-rtl.git"
baseline_clone_subdir=".baseline_repo"

# Directory for cloned baseline repo
baseline_clone_dir=""

# Parse flags and positional args
cleanup_baseline=false
positional_args=()
for arg in "$@"; do
    if [ "$arg" = "--cleanup" ]; then
        cleanup_baseline=true
    else
        positional_args+=("$arg")
    fi
done

# Check positional arg count
if [ ${#positional_args[@]} -lt 1 ] || [ ${#positional_args[@]} -gt 3 ]; then
    echo "Usage: $(basename $0) <path_to_rtl> [baseline_release_tag] [diff_output_dir] [--cleanup]"
    echo "  path_to_rtl             Path to the RTL repository"
    echo "  baseline_release_tag    (Optional) Release tag to diff against (lists available if not provided)"
    echo "  diff_output_dir         (Optional) Directory for diff outputs (default: rtl_diffs)"
    echo "  --cleanup               (Optional) Remove the baseline clone after completion"
    echo ""
    echo "Note: The upstream repo ($upstream_repo_url) is cloned to fetch the baseline."
    echo "      The clone is retained by default and reused on subsequent runs."
    exit -1
fi

# Get args
rtl_path=${positional_args[0]}
baseline_release=${positional_args[1]:-}
diff_output_dir=${positional_args[2]:-rtl_diffs}

# Convert diff_output_dir to absolute path early (needed for baseline clone location)
if [[ "$diff_output_dir" != /* ]]; then
    diff_output_dir="$(pwd)/$diff_output_dir"
fi

rtl_src_path="$rtl_path"/src
integration_spec="$rtl_path"/"$integration_spec_relative_path"

# Function to ensure baseline clone directory exists and is up to date
ensure_baseline_clone() {
    baseline_clone_dir="$diff_output_dir/$baseline_clone_subdir"
    if [ ! -d "$baseline_clone_dir" ]; then
        mkdir -p "$diff_output_dir"
        echo "Cloning upstream repo for baseline comparison..."
        echo "  Clone location: $baseline_clone_dir"
        git clone --filter=blob:none "$upstream_repo_url" "$baseline_clone_dir"
    else
        echo "Updating baseline repo at: $baseline_clone_dir"
        git -C "$baseline_clone_dir" fetch --tags
    fi
}

# Function to validate tag exists in the cloned baseline
validate_tag() {
    local tag=$1
    git -C "$baseline_clone_dir" rev-parse "$tag" >/dev/null 2>&1 && \
    git -C "$baseline_clone_dir" tag -l | grep -q "^${tag}$"
}

# If baseline release is not provided, list available releases and prompt
if [ -z "$baseline_release" ]; then
    ensure_baseline_clone
    echo "Available release tags:"
    git -C "$baseline_clone_dir" tag -l | sort -V
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
    ensure_baseline_clone
    if ! validate_tag "$baseline_release"; then
        echo "Error: '$baseline_release' is not a valid release tag."
        echo "Available tags:"
        git -C "$baseline_clone_dir" tag -l | sort -V
        exit -1
    fi

    echo "Checking out baseline release: $baseline_release"
    git -C "$baseline_clone_dir" checkout "$baseline_release" 2>/dev/null

    echo "Using baseline release: $baseline_release"
fi

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
for line in $exclude_list; do
	# Print the files we are removing first for a sanity check
	echo "  " $(echo "$file_list" | grep "$line")
	# Update the list with the file removed
	file_list=$(echo "$file_list" | grep -v "$line")
done

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
# Per-file status is written to $output_dir/diff_details.log
generate_diffs() {
    local file_list="$1"
    local output_dir="$2"
    local log_file="$output_dir/diff_details.log"

    # Reset counters and unchanged files list
    diff_count=0
    new_file_count=0
    no_diff_count=0
    unchanged_files=""

    # Create output directory and clear any stale log from a previous run
    mkdir -p "$output_dir"
    rm -f "$log_file"

    # Count total files to process for progress display
    local total current=0
    total=$(echo "$file_list" | grep -c . 2>/dev/null || true)
    total=${total:-0}

    # Generate diff for each file in the list
    echo "$file_list" | while IFS= read -r file; do
        if [ -z "$file" ]; then
            continue
        fi

        current=$((current + 1))
        printf "\r  Processing file %d of %d..." "$current" "$total"

        full_file_path="src/$file"

        # Create output filename by replacing / with _ and adding .diff extension
        diff_filename=$(echo "$file" | tr '/' '_').diff
        diff_output_path="$output_dir/$diff_filename"

        local baseline_file="$baseline_clone_dir/$full_file_path"
        local local_file="$rtl_path/$full_file_path"

        if [ -f "$baseline_file" ]; then
            # File exists in baseline, generate diff
            # Use --strip-trailing-cr to ignore CRLF vs LF line ending differences
            diff_output=$(diff -u --strip-trailing-cr "$baseline_file" "$local_file" 2>/dev/null || true)

            if [ -n "$diff_output" ]; then
                echo "$diff_output" > "$diff_output_path"
                echo "  [MODIFIED] $file" >> "$log_file"
            else
                echo "  [NO CHANGE] $file" >> "$log_file"
            fi
        else
            # File is new (didn't exist in baseline)
            echo "  [NEW FILE] $file" >> "$log_file"
            cat "$local_file" > "$diff_output_path" 2>/dev/null || echo "# New file: $file" > "$diff_output_path"
        fi
    done
    printf "\n"

    # Read stats from log file (needed because the while loop runs in a subshell)
    if [ -f "$log_file" ]; then
        diff_count=$(grep -c "\[MODIFIED\]" "$log_file" 2>/dev/null || true)
        new_file_count=$(grep -c "\[NEW FILE\]" "$log_file" 2>/dev/null || true)
        no_diff_count=$(grep -c "\[NO CHANGE\]" "$log_file" 2>/dev/null || true)
        unchanged_files=$(grep "\[NO CHANGE\]" "$log_file" 2>/dev/null | sed 's/.*\[NO CHANGE\] //' || echo "")
    fi

}

# Generate diffs if baseline release is specified
if [ -n "$baseline_release" ]; then
    echo ""
    echo "Generating diffs against baseline release: $baseline_release"

    # Convert rtl_path to absolute path for local copy mode
    if [[ "$rtl_path" != /* ]]; then
        rtl_path="$(pwd)/$rtl_path"
        rtl_src_path="$rtl_path/src"
    fi

    # Generate diffs for main file list
    generate_diffs "$file_list" "$diff_output_dir"

    # Check for deleted files (existed in baseline but not in current file list)
    deleted_file_count=0

    baseline_files=$(find "$baseline_clone_dir/src" -type f \( -iname "*.sv" -o -iname "*.svh" -o -iname "*.rdl" -o -iname "*.v" -o -iname "*.vh" \) 2>/dev/null | sed "s@$baseline_clone_dir/src/@@" | sort || true)

    # Compare with current file list to find deleted files
    # Use temp file to track count since pipe creates subshell
    deleted_count_file=$(mktemp)
    echo "0" > "$deleted_count_file"
    
    echo "$baseline_files" | while IFS= read -r baseline_file; do
        if [ -z "$baseline_file" ]; then
            continue
        fi

        # Check if this baseline file exists in current file list
        if ! echo "$file_list" | grep -qF "$baseline_file"; then
            # Check if file still exists in current working tree
            if [ ! -f "$rtl_path/src/$baseline_file" ]; then
                echo "  [DELETED] $baseline_file" >> "$diff_output_dir/diff_details.log"
                echo "deleted" >> "$deleted_count_file"
            fi
        fi
    done
    
    deleted_file_count=$(grep -c "deleted" "$deleted_count_file" 2>/dev/null || true)
    rm -f "$deleted_count_file"

    echo ""
    echo "Diff generation complete:"
    echo "  Modified files: $diff_count"
    echo "  New files: $new_file_count"
    echo "  Deleted files: $deleted_file_count"
    echo "  Unchanged files: $no_diff_count"
    echo "  Diff output directory: $diff_output_dir"
    echo "  Details: $diff_output_dir/diff_details.log"

    # Generate diffs for expected-to-be-modified files (from integration spec table)
    echo ""
    echo "Generating diffs for expected-to-be-modified files (integration spec table):"

    expected_diff_dir="${diff_output_dir}_expected"

    # Check for missing expected-to-be-modified files first
    # Use temp files since pipe creates subshell
    expected_stats_file=$(mktemp)
    expected_list_file=$(mktemp)
    
    echo "$exclude_list" | while IFS= read -r expected_file; do
        if [ -z "$expected_file" ]; then
            continue
        fi

        # Check if file exists in current working tree
        if [ ! -f "$rtl_path/src/$expected_file" ]; then
            echo "  [MISSING] $expected_file"
            echo "missing" >> "$expected_stats_file"
        else
            # Add to list of existing files to process
            echo "$expected_file" >> "$expected_list_file"
        fi
    done
    
    expected_missing_count=$(grep -c "missing" "$expected_stats_file" 2>/dev/null || true)
    expected_existing_list=$(cat "$expected_list_file" 2>/dev/null || echo "")
    rm -f "$expected_stats_file" "$expected_list_file"

    # Generate diffs for expected-to-be-modified files that exist
    generate_diffs "$expected_existing_list" "$expected_diff_dir"

    # Save the results for the expected files
    expected_diff_count=$diff_count
    expected_new_file_count=$new_file_count
    expected_no_diff_count=$no_diff_count
    expected_unchanged_files="$unchanged_files"

    echo ""
    echo "Expected-to-be-modified files diff generation complete:"
    echo "  Modified files: $expected_diff_count"
    echo "  New files: $expected_new_file_count"
    echo "  Missing files: $expected_missing_count"
    echo "  Unchanged files: $expected_no_diff_count"
    echo "  Diff output directory: $expected_diff_dir"
    echo "  Details: $expected_diff_dir/diff_details.log"

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

    # Clean up baseline clone directory if requested
    if [ "$cleanup_baseline" = true ] && [ -n "$baseline_clone_dir" ] && [ -d "$baseline_clone_dir" ]; then
        echo ""
        echo "Cleaning up baseline clone directory: $baseline_clone_dir"
        rm -rf "$baseline_clone_dir"
    fi
fi

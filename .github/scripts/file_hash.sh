#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# 
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
# DESCRIPTION:
# ====================================
# This tool is used to generate a hash over the Caliptra source code files
# This can be used to verify the hash of the code for which internal workflows were
# run prior to submission to the caliptra-rtl repo.
# 
# Usage: file_hash.sh <path_to_rtl_src_dir> <file_list>
#   path_to_rtl_src_dir     Path to the root directory of the caliptra RTL repo.
#   file_list               This list of all the files that should be included in the hash
#                           is generated
#
# Exit and report failure if anything fails
set -euo pipefail

# Check arg count
if [ $# -ne 2 ]
  then
    echo "Usage: $(basename $0) <path_to_caliptra_root> <file_list>"
	exit -1
fi

# Get args
rtl_path=$1

# Read expected file list, prepend rtl path, and store in array
IFS=$'\n' expected_file_list=($(cat "$2" | sed "s@^@""$rtl_path""/@"))

# Make sure all files exist
missing_files=0
for file in "${expected_file_list[@]}"
do
	# Check if the file is missing
	if ! test -f "$file"; then
		# Report any missing files (and keep count)
		if [ "$missing_files" -eq 0 ]; then
			echo "Missing expected files: "
		fi
		missing_files=$(($missing_files + 1))
		echo "  $file"
	fi
done

# Calculate the hash (only if no files were missing)
if [ "$missing_files" -eq 0 ]; then
	hash=$(cat "${expected_file_list[@]}" | sha384sum | tr -d "\n *-")
	echo "$hash"
else
	echo "Failed to generate code hash"
	exit -1
fi


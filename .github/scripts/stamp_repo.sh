#!/usr/bin/bash
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

# ENV Check
if [[ -z "${CALIPTRA_ROOT:+"empty"}" ]]; then
    echo "Error, must set CALIPTRA_ROOT"
    exit 1
fi

# Create file list
find "$CALIPTRA_ROOT" -type f -name "*.sv" \
                           -o -name "*.svh" \
                           -o -name "*.rdl" \
                           -o -name "*.json" \
                           -o -name "*.v" \
                           -o -name "*.vh" \
                           -o -name "*.rsp" \
                           -o -name "*.s" \
                           -o -name "*.c" \
                           -o -name "*.cpp" \
                           -o -name "*.h" \
                           -o -name "*.hex" \
                           -o -name "*.ld" \
                           -o -name "*.gdb" \
                           -o -name "*.yml" \
                           -o -name "*.sh" \
                           -o -name "*.py" \
                           -o -name "*.md" \
                           -o -name "pr_timestamp" \
                           ! -path "*.git/*" | LC_COLLATE=C sort -o $CALIPTRA_ROOT/.github/workflow_metadata/file_list.txt
sed -i "s,^$CALIPTRA_ROOT/,," $CALIPTRA_ROOT/.github/workflow_metadata/file_list.txt
echo "Found $(wc -l $CALIPTRA_ROOT/.github/workflow_metadata/file_list.txt) source code files to hash"
echo -e "First five files:\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"
head -5 $CALIPTRA_ROOT/.github/workflow_metadata/file_list.txt
echo -e ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"

# Create timestamp
if [[ ! -f $CALIPTRA_ROOT/.github/workflow_metadata/pr_timestamp ]]; then
    echo "Error, file not found: $CALIPTRA_ROOT/.github/workflow_metadata/pr_timestamp"
    exit 1
fi
timestamp=$(date +%s)
echo "Submitting timestamp [${timestamp}]"
echo -n ${timestamp} > $CALIPTRA_ROOT/.github/workflow_metadata/pr_timestamp

# Create hash
hash=$($CALIPTRA_ROOT/.github/scripts/file_hash.sh $CALIPTRA_ROOT $CALIPTRA_ROOT/.github/workflow_metadata/file_list.txt)
if [[ -z ${hash:+"empty"} ]]; then
    echo "Failed to run hash script"
    echo $hash
    exit 1;
fi
echo "RTL hash is $hash"
if [[ ! -f $CALIPTRA_ROOT/.github/workflow_metadata/pr_hash ]]; then
    echo "Error, file not found: $CALIPTRA_ROOT/.github/workflow_metadata/pr_hash"
    exit 1
fi
echo "Submitting hash [${hash}]"
echo -n ${hash} > $CALIPTRA_ROOT/.github/workflow_metadata/pr_hash

# Clean up
rm $CALIPTRA_ROOT/.github/workflow_metadata/file_list.txt

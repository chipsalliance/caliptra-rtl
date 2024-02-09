#!/usr/bin/bash

# Create file list
find "$CALIPTRA_ROOT" -type f -name "*.sv" \
                           -o -name "*.svh" \
                           -o -name "*.rdl" \
                           -o -name "*.v" \
                           -o -name "*.vh" \
                           -o -name "*.c" \
                           -o -name "*.h" \
                           -o -name "pr_timestamp" | sort > $CALIPTRA_ROOT/.github/workflow_metadata/file_list.txt
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
hash=$($CALIPTRA_ROOT/.github/scripts/rtl_hash.sh $CALIPTRA_ROOT $CALIPTRA_ROOT/.github/workflow_metadata/file_list.txt)
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

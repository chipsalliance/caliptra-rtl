#!/bin/bash
#********************************************************************************
# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
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
#********************************************************************************

# Define variables
ot_dir="$1"
clp_dir="$2"

# Check for correct number of arguments
if [ $# -ne 2 ]; then
    echo "Usage: $0 <ot_dir> <clp_dir>"
    exit 1
fi

# Copy OT files to CLP
cp $ot_dir/hw/ip/aes/rtl/* $clp_dir/src/aes/rtl/
#sync tlul manually for now
#cp $ot_dir/hw/ip/tlul/rtl/* $clp_dir/src/tlul/rtl/

# Use sed to find and replace
find "$clp_dir/src/aes/rtl" -type f -exec sed -i "s/prim_/caliptra_prim_/g" {} \;
find "$clp_dir/src/aes/rtl" -type f -exec sed -i "s/\`PRIM/\`CALIPTRA_PRIM/g" {} \;
find "$clp_dir/src/aes/rtl" -type f -exec sed -i "s/\`ASSERT/\`CALIPTRA_ASSERT/g" {} \;
find "$clp_dir/src/aes/rtl" -type f -exec sed -i "s/typedef enum integer/typedef enum logic [31:0]/g" {} \;
find "$clp_dir/src/aes/rtl" -type f -exec sed -i "s/typedef enum int/typedef enum logic [31:0]/g" {} \;
find "$clp_dir/src/aes/rtl" -type f -exec sed -i "s/caliptra_caliptra_/caliptra_/g" {} \;

# Use sed to find and replace
#find "$clp_dir/src/tlul/rtl" -type f -exec sed -i "s/prim_/caliptra_prim_/g" {} \;
#find "$clp_dir/src/tlul/rtl" -type f -exec sed -i "s/\`PRIM/\`CALIPTRA_PRIM/g" {} \;
#find "$clp_dir/src/tlul/rtl" -type f -exec sed -i "s/\`ASSERT/\`CALIPTRA_ASSERT/g" {} \;
#find "$clp_dir/src/tlul/rtl" -type f -exec sed -i "s/top_pkg\:\://g" {} \;

# Get the rev info
cd $ot_dir
git log -1 > $clp_dir/src/aes/rtl/aes_rev_info
#git log -1 > $clp_dir/src/tlul/rtl/tlul_rev_info
cd -

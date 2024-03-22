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

set -e

# Arg checks
if [[ $# -ne 2 ]]; then
    echo "Error, requires destination branch name argument and merge branch name argument"
    exit 1
else
    # I.e. 'main'
    merge_dest=$1
    # I.e. 'feature-branch-name'
    merge_branch=$2
fi

if [[ -z "${CALIPTRA_ROOT:+"empty"}" ]]; then
    echo "Error, must set CALIPTRA_ROOT"
    exit 1
fi
cd $CALIPTRA_ROOT

# Add remote
REMOTE_ADDR='https://github.com/chipsalliance/caliptra-rtl.git'
sts=$(git config --get remote.chips.url > /dev/null; echo $?)
echo "Status for git config --get remote.chips.url is $sts"
if [[ $sts -ne 0 ]]; then
    echo "Add chips remote at $REMOTE_ADDR"
    git remote add chips $REMOTE_ADDR
else
    chips_url=$(git config --get remote.chips.url)
    echo "Result of git config --get remote.chips.url is [$chips_url]"
fi

# Fetch remote
if [[ $(git rev-parse --is-shallow-repository) == "true" ]]; then
    echo "Fetching with unshallow option"
    git fetch --prune --unshallow chips
else
    echo "Repo is already full, no need to unshallow"
    git fetch --prune             chips
fi

# Check for branch existence
if ! git show-ref --quiet "chips/${merge_dest}"; then
    echo "Could not find destination ref [chips/${merge_dest}]"
    exit 1
fi
if ! git show-ref --quiet "chips/${merge_branch}"; then
    echo "Could not find merge branch ref [chips/${merge_branch}]"
    exit 1
fi

# Update branches and perform merge
merged=$(date +%F_%H-%M-%S)_merge_${merge_branch}_into_${merge_dest}
if git show-ref --quiet "${merged}"; then
    echo "Merged branch [${merged}] already exists"'!'
    exit 1
fi
git switch --create ${merged} chips/${merge_dest}

git merge -m "Merge ${merge_branch} into ${merge_dest}" chips/${merge_branch}
sts=$?

if [[ ${sts} -ne 0 ]]; then
    echo "Merge ${merge_branch} into ${merge_dest} failed with status ${sts}"
    git status -s
    exit 1
fi

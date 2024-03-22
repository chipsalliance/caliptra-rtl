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
    echo "Error, requires feature branch name argument and PAT for caliptra-rtl"
    exit 1
else
    # I.e. 'feature-branch-name'
    feature_branch=$1
    # Some PAT
    caliptra_rtl_pat=$2
fi

if [[ -z "${feature_branch:+'empty'}" ]]; then
    echo "Error, got empty branch name argument"
    exit 1
fi
if [[ -z "${caliptra_rtl_pat:+'empty'}" ]]; then
    echo "Error, got empty PAT argument"
    exit 1
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

# Look for target branch
if ! git show-ref --quiet "chips/${feature_branch}"; then
    echo "Could not find feature branch ref [chips/${feature_branch}]"
    exit 1
fi

# Stamp target branch
bash ${CALIPTRA_ROOT}/.github/scripts/stamp_repo.sh
merge_branch=$(git branch --show-current)
git commit -m "MICROSOFT AUTOMATED PIPELINE: Stamp '${merge_branch}' with updated timestamp and hash after successful run" -- ${CALIPTRA_ROOT}/.github/workflow_metadata/pr_hash ${CALIPTRA_ROOT}/.github/workflow_metadata/pr_timestamp

# Update the target branch
if [[ -n $(git branch --format='%(refname:short)' --list "${feature_branch}") ]]; then
    git switch          ${feature_branch}
    if [[ ($(git config --get branch.${feature_branch}.remote) != 'chips') || ($(git config --get branch.${feature_branch}.merge) != "refs/heads/${feature_branch}") ]]; then
        echo "Branch ${feature_branch} already exists, but with invalid merge info: remote [$(git config --get branch.${feature_branch}.remote)] merge [$(git config --get branch.${feature_branch}.merge)]"
        exit 1
    else
        echo "Branch ${feature_branch} already exists, updating"
        sts=$(git pull --ff-only > /dev/null; echo $?)
        if [[ ${sts} -ne 0 ]]; then
            echo "git pull failed to fast-forward"
            exit 1
        fi
    fi
else
    git switch --create ${feature_branch} --track chips/${feature_branch}
    sts=$?
    if [[ ${sts} -ne 0 ]]; then
        echo "Failed to switch to branch [${feature_branch}]"
        exit 1
    fi
fi

# Stamp and push target branch
git restore --source=${merge_branch} ${CALIPTRA_ROOT}/.github/workflow_metadata/pr_timestamp
git restore --source=${merge_branch} ${CALIPTRA_ROOT}/.github/workflow_metadata/pr_hash
git commit -m "MICROSOFT AUTOMATED PIPELINE: Stamp '${feature_branch}' with updated timestamp and hash after successful run" -- ${CALIPTRA_ROOT}/.github/workflow_metadata/pr_hash ${CALIPTRA_ROOT}/.github/workflow_metadata/pr_timestamp
sts=$(git push $(sed "s,github.com,microsoft_pipeline:${caliptra_rtl_pat}@github.com," <<< ${REMOTE_ADDR}) ${feature_branch}:${feature_branch} > /dev/null; echo $?)
if [[ ${sts} -ne 0 ]]; then
    echo "Push ${feature_branch} into chips/${feature_branch} failed with status ${sts}"
    exit 1
fi

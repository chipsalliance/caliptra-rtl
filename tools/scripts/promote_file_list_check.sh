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

set -eo pipefail

derive_github_dest=0
abr_check=0

if [[ $# -eq 3 ]]; then
    merge_dest=$1
    if [[ $3 == "abr" ]]; then
        echo "Running adams-bridge file list check"
        abr_check=1
    else
        echo "Invalid third arg [$3], expected [abr] or []"
        exit 1
    fi
    if [[ $2 == "derived" ]]; then
        derive_github_dest=1
    else
        github_dest=$2
    fi
elif [[ $# -eq 2 ]]; then
    merge_dest=$1
    github_dest=$2
elif [[ $# -eq 1 ]]; then
    merge_dest=$1
    derive_github_dest=1
else
    echo "Error, requires ADO branch name argument and GitHub ref argument (with the remote prefix, e.g. chips/main)"
    exit 1
fi

# Check for file mods in Caliptra (ADO)
cd $MSFT_REPO_ROOT

# Look for target branch
if ! git show-ref --quiet "${merge_dest}"; then
    echo "Could not find Caliptra ref [${merge_dest}]"
    exit 1
fi

echo "Searching for modified file list collateral in Caliptra relative to ${merge_dest}"
internal_mod_count=$(git diff --merge-base ${merge_dest} --name-status | grep -c 'compile.yml$\|compilespecs.yml$\|gen_pb_file_lists.sh$' || exit 0)

# Derive the GitHub comparison ref if needed
if [[ ${derive_github_dest} -eq 1 ]]; then
    cmd="git diff --merge-base ${merge_dest} --no-prefix --unified=0 --no-color -- .git-comodules"
    if [[ ${abr_check} -eq 1 ]]; then
        comod_tag_repo=promote_adams-bridge-mirror
    else
        comod_tag_repo=promote_caliptra-rtl-mirror
    fi
    if $cmd | grep -c "promote_${comod_tag_repo}" > /dev/null; then
        github_dest=$($cmd | grep --max-count=1 --only-matching --color=never -E "promote_${comod_tag_repo}\S+\b")
        echo "Derived github_dest as ${github_dest} from modifications to ${comod_tag_repo} entry in .git-comodules"
    else
        github_dest="chips/main"
        echo "Did not find modifications to ${comod_tag_repo} entry in .git-comodules, defaulting github_dest to ${github_dest}"
    fi
fi

# Check for file mods in mirror repo
if [[ ${abr_check} -eq 1 ]]; then
    cd $ADAMSBRIDGE_ROOT
    REMOTE_ADDR='https://github.com/chipsalliance/adams-bridge.git'
else
    cd $CALIPTRA_ROOT
    REMOTE_ADDR='https://github.com/chipsalliance/caliptra-rtl.git'
fi
# Add remote
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
git fetch --prune --tags origin

# Look for target branch
if ! git show-ref --quiet "${github_dest}"; then
    echo "Could not find ${comod_tag_repo} ref [${github_dest}]"
    exit 1
fi

# Do check...
echo "Searching for modified file list collateral in ${comod_tag_repo} relative to ${github_dest}"
yml_mod_count=$(git diff --merge-base $(git rev-list -n 1 ${github_dest}) --name-status | grep -c 'compile.yml$\|compilespecs.yml$\|gen_pb_file_lists.sh$\|gen_pb_file_lists_abr.sh$' || exit 0)
if [[ -d submodules ]]; then
    for sub in submodules/*; do
        if [[ $(git diff --name-only --submodule=diff --merge-base $(git rev-list -n 1 ${github_dest}) -- ${sub}) == "${sub}" ]]; then 
            old_commit=$(git ls-tree $(git rev-list -n 1 ${github_dest}) -- ${sub} | awk '{print $3}')
            new_commit=$(git ls-tree HEAD                                -- ${sub} | awk '{print $3}')
            echo "Searching for modified file list collateral in submodule ${sub}, which is updated from version ${old_commit} to ${new_commit}"
            pushd "${sub}"
            yml_mod_count_sub=$(git diff ${old_commit} ${new_commit} --name-status | grep -c 'compile.yml$\|compilespecs.yml$' || exit 0)
            yml_mod_count=$(expr ${yml_mod_count} + ${yml_mod_count_sub})
        fi
    done
fi

# Run the file list generator if modifications were found in collateral
if [[ (${yml_mod_count} -gt 0) || (${internal_mod_count} -gt 0) ]]; then
    # Run the Filelist generator script
    if [[ ${abr_check} -eq 1 ]]; then
        bash $MSFT_REPO_ROOT/tools/scripts/gen_pb_file_lists_abr.sh
    else
        bash $MSFT_REPO_ROOT/tools/scripts/gen_pb_file_lists.sh
    fi

    # Check for any file changes
    if [[ $(git status -s --untracked-files=all --ignored=traditional | grep "\.vf" -c) -gt 0 ]]; then
      echo "Regenerating VF file lists produced some file changes:";
      git status -s --untracked-files=all --ignored=traditional | grep "\.vf";
      git diff;
      echo "*****************************************";
      echo "Review above changes locally and resubmit pipeline";
      if [[ ${abr_check} -eq 1 ]]; then
          echo "(Hint: Check $ADAMSBRIDGE_ROOT for the above changes)";
      else
          echo "(Hint: Check $CALIPTRA_ROOT for the above changes)";
      fi
      echo "*****************************************";
      exit 1;
    fi
else
    echo "skipping file_list check since no compile.yml were modified"
fi

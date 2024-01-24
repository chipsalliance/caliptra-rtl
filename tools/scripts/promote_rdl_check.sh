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

if [[ $# -ne 1 ]]; then
    echo "Error, requires branch name argument"
    exit 1
else
    merge_dest=$1
fi

cd $CALIPTRA_ROOT

rdl_mod_count=$(git diff --merge-base ${merge_dest} --name-status | grep -c '\.rdl$\|tools\/templates\/rdl\|reg_gen.sh\|reg_gen.py\|reg_doc_gen.sh\|reg_doc_gen.py')
if [[ ${rdl_mod_count} -gt 0 ]]; then
    # Run the HTML Doc generator script (to update the REG macro header files)
    # and the individual reg generator script but then remove the docs directories
    bash $CALIPTRA_ROOT/tools/scripts/reg_gen.sh
    bash $CALIPTRA_ROOT/tools/scripts/reg_doc_gen.sh
    rm -rf $CALIPTRA_ROOT/src/integration/docs
    rm -rf $CALIPTRA_ROOT/src/soc_ifc/docs

    # Check for any file changes
    if [[ $(git status -s --untracked-files=all --ignored=traditional -- $CALIPTRA_ROOT/src/ | wc -l) -gt 0 ]]; then
      echo "Regenerating reg RDL outputs produced some file changes:";
      git status -s --untracked-files=all --ignored=traditional;
      git diff;
      echo "*****************************************";
      echo "Review above changes locally and resubmit pipeline";
      echo "(Hint: Check $CALIPTRA_ROOT for the above changes)";
      echo "*****************************************";
      exit 1;
    fi
else
    echo "skipping RDL check since no RDL files were modified"
fi

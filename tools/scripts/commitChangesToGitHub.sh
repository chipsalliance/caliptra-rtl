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

function show_usage() {
   printf "Usage: $0 [optional [parameters]]\n"
   printf "\n"
   printf "Options:\n"
   printf " -ws|--githubWS [githubWorkpsace], print githubWorkspace\n"
   printf " -db|--destBranch [destBranch], print destBranch\n"
   printf " -h|--help, Print help\n"

return 0
}

while [ ! -z "$1" ]; do
    echo "Now parsing $1"
    if [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
        show_usage
    elif [[ "$1" == "-ws" ]] || [[ "$1" == "--githubWS" ]]; then
        GITHUB_WS="$2"
        echo "ADO workspace is $GITHUB_WS"
        shift
    elif [[ $1 == "-db" ]] || [[ "$1" == "--destBranch" ]]; then
        GITHUB_DEST_BR="$2"
        echo "Destinaton branch is $GITHUB_DEST_BR"
        shift
    else
        echo "Incorrect input provided $1"
        show_usage
        return 1
    fi
shift
done   

GITHUB_REPO="rtl-caliptra"
GITHUB_ROOT_BR="development"

#Change dir to GitHub workspace
cd $GITHUB_WS
if [ $? -ne 0 ]; then
    echo "Enter correct GitHub workspace path and try again"
    exit 1
fi

#Change directory to GitHub repo
cd $GITHUB_REPO
if [ $? -ne 0 ]; then
    echo "Verify GitHub repo name in the script and try again"
    exit 1
fi

#Verify current branch is GITHUB_DEST_BR
git checkout $GITHUB_DEST_BR
if [ $? -ne 0 ]; then
    echo "Verify you can change to ${GITHUB_DEST_BR} branch of GitHub repo and try again"
    exit 1
fi

gitstat=$(git status)
matchStrGitHub="On branch $GITHUB_DEST_BR"
matchStr2="Changes not staged for commit:"
matchStr3="Untracked files:"
matchStr4="Nothing to commit"
if [[ ($gitstat =~ $matchStrGitHub) ]]; then 
    if [[ (($gitstat =~ $matchStr2) || ($gitstat =~ $matchStr3)) ]]; then
        git add -A && git commit -m "syncing latest updates from Microsoft internal repository"
        if [ $? -ne 0 ]; then
            echo "Verify commit manually and try again"
            exit 1
        else
            echo "Successfully committed changes"
        fi
    elif [[ ($gitstat =~ matchStr4) ]]; then
        echo "Nothing to commit"
    fi
else
    echo "Not on the correct branch. Specify right destination branch"
    exit  1
fi

# Push branch to remote
git push --set-upstream origin $GITHUB_DEST_BR
if [$? -ne 0]; then
    echo "Unable to push ${GITHUB_DEST_BR} to remote. Fix issue and try again"
    exit 1
fi
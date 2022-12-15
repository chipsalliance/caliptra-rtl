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
   printf " -dw|--destWS [destWorkpsace], print destWorkspace\n"
   printf " -dr|--destRepo [destRepo], print destRepo\n"
   printf " -db|--destBranch [destBranch], print destBranch\n"
   printf " -h|--help, Print help\n"

return 0
}

while [ ! -z "$1" ]; do
   if [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
      show_usage
   elif [[ "$1" == "-dw" ]] || [[ "$1" == "--destWS" ]]; then
      DEST_WS="$2"
      echo "Destination workspace is $DEST_WS"
      shift
   elif [[ $1 == "-dr" ]] || [[ "$1" == "--destRepo" ]]; then
      DEST_REPO="$2"
      echo "Destination Repo is $DEST_REPO"
      shift
   elif [[ $1 == "-db" ]] || [[ "$1" == "--destBranch" ]]; then
      DEST_BRANCH="$2"
      echo "Destination branch is $DEST_BRANCH"
      shift
   else
      echo "Incorrect input provided $1"
      show_usage
   fi
shift
done   

#Change dir to destination workspace
cd $DEST_WS
if [ $? -ne 0 ]; then
    echo "Enter correct destination workspace path and try again"
    exit 1
fi

#Change directory to destination repo
cd $DEST_REPO
if [ $? -ne 0 ]; then
    echo "Enter correct destination repo name and try again"
    exit 1
fi

#Checkout master and pull, verify that master is up to date
git checkout main
if [ $? -ne 0 ]; then
    echo "Verify you can change to main branch of destination repo and try again"
    exit 1
fi
git pull
if [ $? -ne 0 ]; then
    echo "Verify you can pull destination repo main branch and try again"
    exit 1
fi
gitstat=$(git status)
matchStr1="On branch main"
matchStr2="Your branch is up to date"
echo $gitstat
if [[ ( $gitstat =~ $matchStr1 ) && ( $gitstat =~ $matchStr2 ) ]]; then
    availbranch=$(git branch)
    if [[ $availbranch =~ $DEST_BRANCH ]]; then
        git checkout $DEST_BRANCH
    else
        git checkout -b $DEST_BRANCH
    fi
    if [ $? -ne 0 ]; then
        echo "Unable checkout branch $DEST_BRANCH. Clean up and try again"
        exit 1
    fi
else
    echo "Clean git status and try again"
    echo "NAY"
fi




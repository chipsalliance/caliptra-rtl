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
   printf " -a2g|--ado2github\n"
   printf " -h|--help, Print help\n"

return 0
}

while [ ! -z "$1" ]; do
    if [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
        show_usage
    elif [[ "$1" == "-ws" ]] || [[ "$1" == "--githubWS" ]]; then
        GITHUB_WS="$2"
        echo "GitHub workspace is $GITHUB_WS"
        shift
    elif [[ $1 == "-db" ]] || [[ "$1" == "--destBranch" ]]; then
        DEST_BRANCH="$2"
        echo "Destinaton branch is $DEST_BRANCH"
        shift
    elif [[ $1 == "-a2g" ]] || [[  "$1" == "--ado2github" ]]; then
        A2G="true"
        echo "ADO to GitHub Sync is enabled"
    else
        echo "Incorrect input provided $1"
        show_usage
        return 1
    fi
shift
done   

A2G=${A2G:-"false"}

GITHUB_REPO="caliptra-rtl"

# Set Source and Destination repositories based on $A2G
if [[ $A2G == "true" ]]; then
    GITHUB_ROOT_BR="dev-msft"
    GITHUB_DEST_BR=$DEST_BRANCH
else
    GITHUB_ROOT_BR="main"
fi

###############################################################
# Prep GITHUB repository
###############################################################
echo "Preparing GitHub Repository"

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

#Checkout appropriate branch and pull, verify that it is up to date
#   If GitHub repo is destination, checkout 'development'
#   If ADO repo is destination, checkout 'master'
git checkout $GITHUB_ROOT_BR
if [ $? -ne 0 ]; then
    echo "Verify you can change to ${GITHUB_ROOT_BTR} branch of GitHub repo and try again"
    exit 1
fi
git pull
if [ $? -ne 0 ]; then
    echo "Verify you can pull branch and try again"
    exit 1
fi
gitstat=$(git status)
matchStrGitHub="On branch $GITHUB_ROOT_BR"
matchStr2="Your branch is up to date"
echo $gitstat
if [[ ( $gitstat =~ $matchStrGitHub )  && ( $gitstat =~ $matchStr2 ) ]]; then
    if [ -n $GITHUB_DEST_BR ]; then
        availbranch=$(git branch)
        if [[ $availbranch =~ $GITHUB_DEST_BR ]]; then
            git checkout $GITHUB_DEST_BR
        else
            git checkout -b $GITHUB_DEST_BR
        fi
        if [ $? -ne 0 ]; then
            echo "Unable checkout branch $GITHUB_DEST_BR. Clean up and try again"
            exit 1
        fi
    fi
else
    echo "Clean git status and try again"
    echo "NAY"
fi

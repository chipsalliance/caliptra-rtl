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
   printf " -ws|--adoWS [adoWorkpsace], print adoWorkspace\n"
   printf " -db|--destBranch [destBranch], print destBranch\n"
   printf " -a2g|--ado2github\n"
   printf " -ir|--ignoreReadme\n"
   printf " -h|--help, Print help\n"

return 0
}

while [ ! -z "$1" ]; do
    if [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
        show_usage
    elif [[ "$1" == "-ws" ]] || [[ "$1" == "--adoWS" ]]; then
        ADO_WS="$2"
        echo "ADO workspace is $ADO_WS"
        shift
    elif [[ $1 == "-db" ]] || [[ "$1" == "--destBranch" ]]; then
        DEST_BRANCH="$2"
        echo "Destinaton branch is $DEST_BRANCH"
        shift
    elif [[ $1 == "-a2g" ]] || [[  "$1" == "--ado2github" ]]; then
        A2G="true"
        echo "ADO to GitHub Sync is enabled"
    elif [[ $1 == "-ir" ]] || [[ "$1" == "--ignoreReadme" ]]; then
        IGNORE_README="true"
        echo "Ignore README is enabled"
    elif [[ $1 == "-in" ]] || [[ "$1" == "--ignoreReleaseNotes" ]]; then
        IGNORE_RELEASE_NOTES="true"
        echo "Ignore Release_notes.txt is enabled"
    else
        echo "Incorrect input provided $1"
        show_usage
        return 1
    fi
shift
done   

echo $IGNORE_README
A2G=${A2G:-"false"}
IGNORE_README=${IGNORE_README:-"false"}

ADO_REPO="Caliptra"
ADO_ROOT_BR="master"

# Set Source and Destination repositories based on $A2G
if [[ $A2G == "false" ]]; then
    ADO_DEST_BR=$DEST_BRANCH
fi

###############################################################
# Prep ADO repository
###############################################################
echo "Preparing ADO repository"

# Verify ADO workspace
module load settings/tsd
curWs=$(which-ws)
if [[ $curWs != $ADO_WS ]]; then
    echo $curWs
    echo $ADO_WS
    echo "Enter correct workspace name and try again" 1>&2
    exit 1
fi

# Change  directory to $ADO_REPO
if [[ $(pwd) == $ADO_WS ]]; then
    cd $ADO_REPO
    if [ $? -ne 0 ]; then
        echo "Enter correct destination repo name and try again" 1>&2
        exit 1
    fi
fi 

# Check out ADO_ROOT_BR and pull, verify that ADO_ROOT_BR is up-to-date
git checkout $ADO_ROOT_BR
if [ $? -ne 0 ]; then
    echo "Verify you can change to $ADO_ROOT_BR branch of source repo and try again" 1>&2
    exit 1
fi
git pull --ff-only
if [ $? -ne 0 ]; then
    echo "Verify you can pull source repo $ADO_ROOT_BR branch and try again" 1>&2
    exit 1
fi
gitstat=$(git status)
matchStr1="On branch $ADO_ROOT_BR"
matchStr2="Your branch is up to date"
if [[ ( $gitstat =~ $matchStr1 ) && ( $gitstat =~ $matchStr2 ) ]]; then
    #Check README.md update timestamp and fail if timestamp is not today
    #Get today's date
    today=$(date +%F)
    # Get date from README.md and convert to yyyy-mm-dd format
    readmeDate=$(grep -oP "_\*Last Update: \d{4}\/\d{2}\/\d{2}\*_" Release_notes.md | sed 's/Last Update: //g' | sed 's/_//g' | sed 's/\*//g' | sed 's/\//-/g')
    #Check if dates match
    if [[ "$readmeDate" != "$today" ]]; then
        echo $IGNORE_README
        if [[ ${IGNORE_README} == "true" ]]; then
            echo "Warning - README.md is out of date. Not returning error code per script runtime options"
        else
            echo "README.md is out of date. Update file and timestamp and try again!!" 1>&2
            exit 1
        fi
    fi
    # Get date from Release_notes.txt timestamp and fail if timestamp is not today
    releaseNotesDate=$(grep -oP "_\*Last Update: \d{4}\/\d{2}\/\d{2}\*_" Release_notes.txt | sed 's/Last Update: //g' | sed 's/_//g' | sed 's/\*//g' | sed 's/\//-/g')
    #Check if dates match
    if [[ "$releaseNotesDate" != "$today" ]]; then
        echo $IGNORE_RELEASE_NOTES
        if [[ ${IGNORE_RELEASE_NOTES} == "true" ]]; then
            echo "Warning - RELEASE_NOTES.txt is out of date. Not returning error code per script runtime options"
        else
            echo "RELEASE_NOTES.txt is out of date. Update file and timestamp and try again!!" 1>&2
            exit 1
        fi
    fi
    if [[ -n $ADO_DEST_BR ]]; then
        availbranch=$(git branch)
        if [[ $availbranch =~ $ADO_DEST_BR ]]; then
            git checkout $ADO_DEST_BR
        else
            git checkout -b $ADO_DEST_BR
        fi
        if [[ $? -ne 0 ]]; then
            echo "Unable checkout branch $ADO_DEST_BR. Clean up and try again"
            exit 1
        fi
    fi
else
    echo "Check $ADO_ROOT_BR branch and try again!!!" 1>&2
    exit 1
fi

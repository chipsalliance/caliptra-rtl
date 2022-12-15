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
   printf " -sw|--srcWS [srcWorkpsace], print srcWorkspace\n"
   printf " -sr|--srcRepo [srcRepo], print srcRepo\n"
   printf " -h|--help, Print help\n"

return 0
}

while [ ! -z "$1" ]; do
   if [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
      show_usage
   elif [[ "$1" == "-sw" ]] || [[ "$1" == "--srcWS" ]]; then
      SRC_WS="$2"
      echo "Source workspace is $SRC_WS"
      shift
   elif [[ $1 == "-sr" ]] || [[ "$1" == "--srcRepo" ]]; then
      SRC_REPO="$2"
      echo "Source Repo is $SRC_REPO"
      shift
   else
      echo "Incorrect input provided $1"
      show_usage
   fi
shift
done   

#Verify source PB workspace
module load settings/tsd
if [ $(which-ws) != $SRC_WS ]; then
    echo "Enter correct workspace name and try again" 1>&2
    exit 1
fi

#Change directory to source repo
if [ $(pwd) == $SRC_WS ]; then
    cd $SRC_REPO
    if [ $? -ne 0 ]; then
        echo "Enter correct destination repo name and try again" 1>&2
        exit 1
    fi
fi

#Checkout master and pull, verify that master is up to date
git checkout master
if [ $? -ne 0 ]; then
    echo "Verify you can change to master branch of source repo and try again" 1>&2
    exit 1
fi
git pull
if [ $? -ne 0 ]; then
    echo "Verify you can pull source repo master branch and try again" 1>&2
    exit 1
fi
gitstat=$(git status)
matchStr1="On branch master"
matchStr2="Your branch is up to date"
if [[ ( $gitstat =~ $matchStr1 ) && ( $gitstat =~ $matchStr2 ) ]]; then
   #Check README.md update timestamp and fail if timestamp is not today
   #Get today's date
   today=$(date +%F)
   # Get date from README.md and convert to yyyy-mm-dd format
   readmeDate=$(grep -oP "_\*Last Update: \d{4}\/\d{2}\/\d{2}\*_" README.md | sed 's/Last Update: //g' | sed 's/_//g' | sed 's/\*//g' | sed 's/\//-/g')
    #Check if dates match
    if [ "$readmeDate" != "$today" ]; then
        echo "README.md is out of date. Update file and timestamp and try again!!" 1>&2
        exit 1
    fi
else
    echo "Check master branch and try again!!!" 1>&2
    exit 1
fi




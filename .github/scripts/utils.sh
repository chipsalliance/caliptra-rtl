#!/bin/bash

# Colors
COLOR_OFF='\033[0m'
COLOR_RED='\033[31m'
COLOR_GREEN='\033[32m'
COLOR_WHITE='\033[1;37m'

# Waits until the given phrase appears in a log file (actively written to)
# Usage: wait_for_phrase <log_file> <phrase>
wait_for_phrase () {

    # Check if the log exists
    sleep 1s
    if ! [ -f "$1" ]; then
        echo -e "${COLOR_RED}Log file '$1' not found!${COLOR_OFF}"
        return -1
    fi

    # Wait for the phrase
    DEADLINE=$((${EPOCHSECONDS} + 30))
    while [ ${EPOCHSECONDS} -lt ${DEADLINE} ]
    do
        # Check for the phrase
        grep "$2" "$1" >/dev/null
        if [ $? -eq 0 ]; then
            return 0
        fi

        # Sleep and retry
        sleep 1s
    done

    # Timeout
    return -1
}

# Terminates a process. First via SIGINT and if this doesn't work after 10s
# retries with SIGKILL
# Usage: terminate <pid>
terminate () {

    local PID=$1

    # Gently interrupt, wait some time and then kill
    /bin/kill -s SIGINT  ${PID} || true
    sleep 10s
    /bin/kill -s SIGKILL ${PID} || true
}

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

import sys
import os
import shutil
import yaml
import re
import subprocess
import logging
import datetime
from multiprocessing import Pool, Lock, Array

logger = logging.getLogger()
logger.setLevel(logging.INFO)
console_handler = logging.StreamHandler()
formatter = logging.Formatter('%(asctime)s | %(levelname)s: %(message)s', '%Y-%m-%d %H:%M:%S')
console_handler.setFormatter(formatter)
logger.addHandler(console_handler)

def createScratch():
    now = datetime.datetime.now()
    latestdir = now.date().strftime("%Y%m%d") + now.time().strftime("%H%M%S")
    scratch=os.path.join(os.environ.get('CALIPTRA_WORKSPACE'), "scratch", os.environ.get('USER'), "verilator", latestdir)
    if os.path.isdir(scratch):
        logger.warning("Clobbering existing verilator scratch folder")
        shutil.rmtree(scratch)
    os.makedirs(scratch)
    os.system(f"ln -snf {scratch} {os.path.join(scratch, '../latest')}")
    return scratch

# Run command and wait for it to complete before returning the results
def runBashScript(cmd):
    p = subprocess.Popen(cmd, stdin=None, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE )
    result = p.communicate()
    exitCode = p.returncode
    resultOut, resultErr = result
    return exitCode, resultOut, resultErr

def verilateTB(scratch):
    verilatedDir = os.path.join(scratch,".verilated_image")
    os.mkdir(verilatedDir)
    logfile = os.path.join(verilatedDir, "verilate.log")

    # Create a custom logger for logging run results to a file
    testlogger = logging.getLogger("verilate_image")

    # Create handlers
    f_handler = logging.FileHandler(logfile)
    f_handler.setLevel(logging.INFO)

    # Create formatters and add it to handlers
    f_format = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    f_handler.setFormatter(f_format)

    # Add handler to the logger
    testlogger.addHandler(f_handler)
    
    # Invoke makefile for the base verilated image
    mfile = os.path.join(os.environ.get('CALIPTRA_ROOT'),"tools/scripts/Makefile")
    cmd = " ".join(["make", "-C", verilatedDir, "-f", mfile, "verilator-build"])
    exitcode, resultout, resulterr = runBashScript(cmd)

    # Parse and log the results
    infoMsg = f"############################################## verilator-build ##############################################"
    logger.info(infoMsg)
    if (exitcode is None):
        errorMsg = f"Running verilator-build in Verilator failed to complete as expected"
        logger.error(errorMsg)
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        testlogger.error(resulterr.decode())
        raise subprocess.CalledProcessError(exitcode, cmd)
    elif (exitcode == 0):
        infoMsg = f"Ran verilator-build in Verilator to completion"
        logger.info(infoMsg)
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        # TODO: Parse output for status?
        logger.info(infoMsg)
    else:
        logger.error(f"verilator-build failed to run in Verilator")
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        testlogger.error(resulterr.decode())
        raise subprocess.CalledProcessError(exitcode, cmd)

    # Return the path to pristine build
    return verilatedDir

def getTestNames():
    l0_regress_file = os.path.join(os.environ.get('CALIPTRA_ROOT'), "src/integration/stimulus/L0_regression.yml")
    testPaths = []
    x = ''
    integrationTestSuiteList = []

    with open (l0_regress_file) as f:
        dict = yaml.load(f, Loader=yaml.FullLoader)
        for item in dict["contents"]:
            for key in item.keys():
                for testKey in item[key].keys():
                    if (testKey == 'paths'):
                        testPaths = item[key][testKey]

    for testYml in testPaths:
        x = re.search(r'../test_suites/(\S+)/\S+.yml', testYml)
        # Skip clk gating tests in Verilator until PC issue is resolved
        # https://github.com/chipsalliance/Cores-VeeR-EL2/issues/88
        # https://github.com/chipsalliance/caliptra-rtl/issues/126
        if (re.search(r'(smoke_test_clk_gating|smoke_test_cg_wdt|smoke_test_mbox_cg|smoke_test_kv_cg|smoke_test_doe_cg|smoke_test_dma|smoke_test_wdt_rst)',x.groups()[0])) :
            continue
        integrationTestSuiteList.append(x.groups()[0])

    return integrationTestSuiteList

def init_pool(lock, arr):
    global printlock
    printlock = lock
    global pending_test_arr
    pending_test_arr = arr

def runTest(args):

    (test, scratch, verilated, idx) = args;

    testdir = os.path.join(scratch, test)
    # Reuse pristine verilator-build output for each test
    shutil.copytree(verilated, testdir)
    logfile = os.path.join(testdir, test + ".log")

    # Create a custom logger for logging run results to a file
    testlogger = logging.getLogger(test)

    # Create handlers
    f_handler = logging.FileHandler(logfile)
    f_handler.setLevel(logging.INFO)

    # Create formatters and add it to handlers
    f_format = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    f_handler.setFormatter(f_format)

    # Add handler to the logger
    testlogger.addHandler(f_handler)
    
    # Invoke makefile for the current test
    mfile = os.path.join(os.environ.get('CALIPTRA_ROOT'),"tools/scripts/Makefile")
    testname = "TESTNAME=" + test
    cmd = " ".join(["make", "-C", testdir, "-f", mfile, testname, "verilator", "VERILATOR_RUN_ARGS=+CLP_REGRESSION"])
    exitcode, resultout, resulterr = runBashScript(cmd)

    # Parse and log the results
    if not printlock.acquire(timeout=60):
        raise RuntimeError(f"Failed to get lock in RunTest {test}")
    logger.info(f"Test {test} acquired print lock")
    infoMsg = f"############################################## {test} ##############################################"
    logger.info(infoMsg)
    if (exitcode is None):
        errorMsg = f"Running {test} in Verilator failed to complete as expected"
        logger.error(errorMsg)
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        testlogger.error(resulterr.decode())
        teststatus = 1
    elif (exitcode == 0):
        infoMsg = f"Ran {test} in Verilator to completion - parsing output for status"
        logger.info(infoMsg)
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        if r"* TESTCASE PASSED" in resultout.decode():
            infoMsg = f"{test} passed"
            teststatus = 0
        else:
            infoMsg = f"{test} failed"
            teststatus = 1
        logger.info(infoMsg)
    else:
        logger.error(f"{test} failed to run in Verilator")
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        testlogger.error(resulterr.decode())
        teststatus = 1
    pending_test_arr[idx] = 0
    printlock.release()
    return teststatus

def main():
    # Env vars $CALIPTRA_WORKSPACE and $CALIPTRA_ROOT must be set/present
    if (os.environ.get('CALIPTRA_WORKSPACE') is None):
        logger.error("CALIPTRA_WORKSPACE not defined!")
        return 1
    if (os.environ.get('CALIPTRA_ROOT') is None):
        logger.error("CALIPTRA_ROOT not defined!")
        return 1
    elif ((os.environ.get('CALIPTRA_ROOT') != os.path.join(os.environ.get('CALIPTRA_WORKSPACE'), "Caliptra"    )) and
          (os.environ.get('CALIPTRA_ROOT') != os.path.join(os.environ.get('CALIPTRA_WORKSPACE'), "chipsalliance", "caliptra-rtl"))):
        logger.error(f"CALIPTRA_ROOT definition [{os.environ.get('CALIPTRA_ROOT')}] is invalid! Expected [{os.path.join(os.environ.get('CALIPTRA_WORKSPACE'), 'Caliptra')}] or [{os.path.join(os.environ.get('CALIPTRA_WORKSPACE'), 'chipsalliance', 'caliptra-rtl')}]")
        return 1
    # Create a scratch space for run outputs
    scratch = createScratch()
    # Verilate the code into a single pristine obj folder
    verilated = verilateTB(scratch)
    # Parse yaml file for test list
    testnames=getTestNames()
    # Set up args for the multiprocessing Pool
    failcount=0
    printlock=Lock()
    ones = []
    for i in testnames: ones.append(1)
    pending_tests=Array('B', ones, lock=True)
    run_args = [(testname, scratch, verilated, testnames.index(testname)) for testname in testnames]
    # Run all tests in parallel and accumulate error status codes to the global failcount
    async_res = Pool(len(testnames), init_pool, (printlock, pending_tests)).map_async(runTest, run_args)
    while True:
        async_res.wait(60)
        if async_res.ready():
            logger.info("All tests completed, exiting wait loop")
            break
        if not printlock.acquire(timeout=60):
            raise RuntimeError("Failed to get lock in main")
        logger.info(f" >>> Tests still in progress:")
        for idx,sts in enumerate(pending_tests):
            if sts == 1:
                logger.info(f"     * {testnames[idx]}")
        printlock.release()
    logger.info(f"Ending status of multiprocessing pool: {async_res.successful()}")
    test_status_list = async_res.get(None)
    for sts in test_status_list:
        failcount += sts

    # Ending summary
    infoMsg = f"############################################## SUMMARY ##############################################"
    logger.info(infoMsg)
    if failcount == 0:
        infoMsg = f"All tests passed!"
        logger.info(infoMsg)
    else:
        errorMsg = f"Regression failed! Total number of failing tests: {failcount}"
        logger.error(errorMsg)
    return failcount

if __name__ == "__main__":
    sys.exit(main())

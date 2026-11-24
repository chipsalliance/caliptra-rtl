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

import argparse
import sys
import os
import shutil
import yaml
import re
import shlex
import subprocess
import logging
import datetime
from multiprocessing import Pool, Lock, Array
from pathlib import Path
from typing import NamedTuple

logger = logging.getLogger()
logger.setLevel(logging.INFO)
console_handler = logging.StreamHandler()
formatter = logging.Formatter('%(asctime)s | %(levelname)s: %(message)s', '%Y-%m-%d %H:%M:%S')
console_handler.setFormatter(formatter)
logger.addHandler(console_handler)


class RegressionTest(NamedTuple):
    identity: str
    testname: str
    plusargs: tuple
    seed: int


def default_manifest(root, subsystem):
    name = "L0_ss_mode_regression.yml" if subsystem else "L0_regression.yml"
    return Path(root) / "src/integration/stimulus" / name


def make_command(builddir, subsystem, target, test=None):
    command = ["make", "-C", str(builddir), "-f",
               str(Path(os.environ["CALIPTRA_ROOT"]) / "tools/scripts/Makefile"),
               f"CALIPTRA_MODE_SUBSYSTEM={subsystem}", target]
    if test is not None:
        # Quote for the make recipe's shell and preserve literal '$' through make.
        plusargs = " ".join(shlex.quote(arg) for arg in test.plusargs).replace("$", "$$")
        command.extend([f"TESTNAME={test.testname}", f"PLAYBOOK_RANDOM_SEED={test.seed}",
                        "VERILATOR_RUN_ARGS=+CLP_REGRESSION", f"RUN_PLUSARGS={plusargs}"])
    return command


def simulation_passed(status, output):
    return (status == 0 and "* TESTCASE PASSED" in output and
            "* TESTCASE FAILED" not in output and "SVA ERROR" not in output)


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description="Run a Caliptra Verilator regression")
    parser.add_argument("--subsystem", type=int, choices=(0, 1), default=0)
    parser.add_argument("--manifest", type=Path,
                        help="Defaults to the selected profile's L0 manifest")
    return parser.parse_args(argv)

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
    p = subprocess.Popen(cmd, stdin=None, shell=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE )
    result = p.communicate()
    exitCode = p.returncode
    resultOut, resultErr = result
    return exitCode, resultOut, resultErr

def verilateTB(scratch, subsystem):
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
    cmd = make_command(verilatedDir, subsystem, "verilator-build")
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

def load_tests(manifest, default_seed):
    manifest = Path(manifest).resolve()
    with manifest.open() as stream:
        config = yaml.safe_load(stream)
    if not isinstance(config, dict) or not isinstance(config.get("contents"), list):
        raise ValueError(f"{manifest}: expected a contents list")
    tests = []
    identities = set()
    for group in config["contents"]:
        if not isinstance(group, dict) or not isinstance(group.get("tests"), dict):
            raise ValueError(f"{manifest}: expected tests/paths entries")
        paths = group["tests"].get("paths")
        if not isinstance(paths, list):
            raise ValueError(f"{manifest}: tests.paths must be a list")
        for path in paths:
            if not isinstance(path, str):
                raise ValueError(f"{manifest}: test path must be a string")
            path = os.path.expandvars(path)
            if "$" in path:
                raise ValueError(f"{manifest}: unresolved environment variable in {path}")
            test_path = (manifest.parent / path).resolve()
            # Preserve the existing Verilator clock-gating exclusions.
            # https://github.com/chipsalliance/Cores-VeeR-EL2/issues/88
            # https://github.com/chipsalliance/caliptra-rtl/issues/126
            if re.search(r"smoke_test_clk_gating|smoke_test_cg_wdt|smoke_test_mbox_cg|"
                         r"smoke_test_kv_cg|smoke_test_doe_cg|smoke_test_dma|smoke_test_wdt_rst",
                         test_path.parent.name):
                continue
            with test_path.open() as stream:
                test = yaml.safe_load(stream)
            if not isinstance(test, dict):
                raise ValueError(f"{test_path}: expected a test mapping")
            testname = test.get("testname")
            if not isinstance(testname, str) or not re.fullmatch(r"[A-Za-z0-9_]+", testname):
                raise ValueError(f"{test_path}: invalid firmware testname")
            simulators = test.get("simulators", ["verilator", "vcs"])
            if (not isinstance(simulators, list) or not simulators or
                    any(not isinstance(item, str) for item in simulators)):
                raise ValueError(f"{test_path}: simulators must be a nonempty string list")
            if "verilator" not in simulators:
                logger.info("Not run by Verilator: %s requires %s", test_path.stem, ", ".join(simulators))
                continue
            identity = test_path.stem
            if test_path.parent.name != identity:
                identity = test_path.parent.name + "__" + identity
            if not re.fullmatch(r"[A-Za-z0-9_.-]+", identity) or identity in identities:
                raise ValueError(f"{test_path}: invalid or duplicate variant identity {identity}")
            identities.add(identity)
            plusargs = test.get("plusargs") or []
            if not isinstance(plusargs, list):
                raise ValueError(f"{test_path}: plusargs must be a list")
            parsed_plusargs = []
            for arg in plusargs:
                if not isinstance(arg, str) or "\n" in arg or "\r" in arg:
                    raise ValueError(f"{test_path}: plusarg must be a single-line string")
                tokens = shlex.split(arg)
                if len(tokens) != 1 or not tokens[0].startswith("+"):
                    raise ValueError(f"{test_path}: expected one plusarg per list entry")
                parsed_plusargs.append(tokens[0])
            if {"+CLP_DCLS_EN", "+CLP_DCLS_DIS"}.issubset(parsed_plusargs):
                raise ValueError(f"{test_path}: conflicting DCLS enable/disable plusargs")
            seed = test.get("seed", default_seed)
            if seed == "${PLAYBOOK_RANDOM_SEED}":
                seed = os.environ.get("PLAYBOOK_RANDOM_SEED", default_seed)
            if isinstance(seed, str):
                seed = os.path.expandvars(seed)
            if isinstance(seed, bool) or not re.fullmatch(r"[0-9]+", str(seed)):
                raise ValueError(f"{test_path}: seed must resolve to a nonnegative integer")
            tests.append(RegressionTest(identity, testname, tuple(parsed_plusargs), int(seed)))
    if not tests:
        raise ValueError(f"{manifest}: no supported tests selected")
    return tests

def init_pool(lock, arr):
    global printlock
    printlock = lock
    global pending_test_arr
    pending_test_arr = arr

def runTest(args):

    (test, scratch, verilated, idx, subsystem) = args;

    testdir = os.path.join(scratch, test.identity)
    # Reuse pristine verilator-build output for each test
    shutil.copytree(verilated, testdir)
    logfile = os.path.join(testdir, test.identity + ".log")

    # Create a custom logger for logging run results to a file
    testlogger = logging.getLogger(test.identity)

    # Create handlers
    f_handler = logging.FileHandler(logfile)
    f_handler.setLevel(logging.INFO)

    # Create formatters and add it to handlers
    f_format = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    f_handler.setFormatter(f_format)

    # Add handler to the logger
    testlogger.addHandler(f_handler)

    # Invoke makefile for the current test
    cmd = make_command(testdir, subsystem, "verilator", test)
    exitcode, resultout, resulterr = runBashScript(cmd)

    # Parse and log the results
    if not printlock.acquire(timeout=60):
        raise RuntimeError(f"Failed to get lock in RunTest {test.identity}")
    logger.info(f"Test {test.identity} acquired print lock")
    infoMsg = f"############################################## {test.identity} ##############################################"
    logger.info(infoMsg)
    if (exitcode is None):
        errorMsg = f"Running {test.identity} in Verilator failed to complete as expected"
        logger.error(errorMsg)
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        testlogger.error(resulterr.decode())
        teststatus = 1
    elif (exitcode == 0):
        infoMsg = f"Ran {test.identity} in Verilator to completion - parsing output for status"
        logger.info(infoMsg)
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        if simulation_passed(exitcode, resultout.decode() + resulterr.decode()):
            infoMsg = f"{test.identity} passed"
            teststatus = 0
        else:
            infoMsg = f"{test.identity} failed"
            teststatus = 1
        logger.info(infoMsg)
    else:
        logger.error(f"{test.identity} failed to run in Verilator")
        infoMsg = f"Run output logged at: {logfile}"
        logger.info(infoMsg)
        testlogger.info(resultout.decode())
        testlogger.error(resulterr.decode())
        teststatus = 1
    pending_test_arr[idx] = 0
    printlock.release()
    return teststatus

def main(argv=None):
    args = parse_args(argv)
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
    verilated = verilateTB(scratch, args.subsystem)
    # Parse yaml file for test list
    manifest = args.manifest or default_manifest(os.environ["CALIPTRA_ROOT"], args.subsystem)
    seed = int(os.environ.get("PLAYBOOK_RANDOM_SEED", datetime.datetime.now().timestamp()))
    testnames = load_tests(manifest, seed)
    # Set up args for the multiprocessing Pool
    failcount=0
    printlock=Lock()
    ones = []
    for i in testnames: ones.append(1)
    pending_tests=Array('B', ones, lock=True)
    run_args = [(test, scratch, verilated, idx, args.subsystem) for idx, test in enumerate(testnames)]
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
                logger.info(f"     * {testnames[idx].identity}")
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

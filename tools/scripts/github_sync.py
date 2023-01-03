# SPDX-License-Identifier: Apache-2.0
# Copyright 2022 Microsoft Corporation or its affiliates.
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

#######################################################################################
#                              !!IMPORTANT!!                                          #
# You need to be in the PB enviroment to run this script                              #
# Specify complete path to source and destination workspaces ($HOME/<workspace_name>) #
#######################################################################################


import sys
import os
import shutil
import argparse
import yaml
import re
import subprocess
import logging
import codecs

logger = logging.getLogger()
logger.setLevel(logging.INFO)
console_handler = logging.StreamHandler()
formatter = logging.Formatter('%(asctime)s | %(levelname)s: %(message)s', '%Y-%m-%d %H:%M:%S')
console_handler.setFormatter(formatter)
logger.addHandler(console_handler)

# Run command and wait for it to complete before returning the results
def runBashScript(cmd):
    p = subprocess.Popen(cmd, stdin=None, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE )
    stdout, stderr = p.communicate()
    exitCode = p.returncode
    return exitCode, stdout, stderr
    #return os.popen(cmd).read()

def prepDestRepo(inDestWS, inDestRepo, inDestBranch):
    scriptsDir = get_script_dir()
    prepRepoScript = os.path.join(scriptsDir, "prepDestRepo.sh")
    cmd = ". {} -dw {} -dr {} -db {}".format(prepRepoScript, inDestWS, inDestRepo, inDestBranch)
    exitcode, prepRepoStdout, prepRepoStderr = runBashScript(cmd)
    if (exitcode == 0):
        infoMsg = "Destination repo {} setup with branch {}.".format(inDestRepo, inDestBranch)
        logger.info(infoMsg)
    else:
        print(exitcode)
        print(prepRepoStderr.decode())
        return 1

def prepPBSrcRepo(inSrcWS, inSrcRepo):
    scriptsDir = get_script_dir()
    prepRepoScript = os.path.join(scriptsDir, "prepPBSrcRepo.sh")
    cmd = ". {} -sw {} -sr {}".format(prepRepoScript, inSrcWS, inSrcRepo)
    exitcode, prepRepoStdout, prepRepoStderr = runBashScript(cmd)
    if (exitcode == 0):
        infoMsg = "Source repo {} setup with branch {}.".format(inSrcRepo, "master")
        logger.info(infoMsg)
    else:
        print(exitcode)
        print(prepRepoStderr.decode())

def get_script_dir():
    return os.path.dirname(os.path.realpath(__file__))

def listdir_nohidden(dirpath):
    fileList = []
    dirList = []
    for f in os.listdir(dirpath):
        f_fullPath = os.path.join(dirpath, f)
        if not f.startswith('.'):
            if os.path.isfile(f_fullPath):
                fileList.append(f)
            else:
                dirList.append(f)
    return fileList, dirList

def copy_tree(src, dest):
    if (os.path.exists(dest)):
        infoMsg = "Copying directory {}".format(src)
        logger.info(infoMsg)
        shutil.rmtree(dest)
        shutil.copytree(src,dest)

def create_directory(dest):
    if (not os.path.exists(dest)):
        infoMsg = "Creating directory {}".format(dest)
        logger.info(infoMsg)
        os.mkdir(dest)
    else:
        infoMsg = "Destination directory {} already exists".format(dest)
        logger.info(infoMsg)

def copy_file(file, srcDir,destDir):
    src = os.path.join(srcDir, file)
    dest = os.path.join(destDir, file)
    infoMsg = "Copying file {}".format(src)
    logger.info(infoMsg)
    shutil.copy(src, dest)


def copyFilesSrcToDest(sWorkspace, sRepo, dWorkspace, dRepo):
    blacklistRepoDirsFiles = ["etc", "config", "dvt_build.log"]
    blacklistIpDirsFiles = ["aes", "sim_irq_gen", "syn"]
    blacklistScriptsDirsFiles = ["gen_pb_file_lists.sh", "README.md", "sim_config_parse.py", "github_sync.py", "prepDestRepo.sh", "prepPBSrcRepo.sh", "run_test_makefile", "syn"]
    integrationTestSuiteList = ['caliptra_demo', 'caliptra_isr', 'includes', 'printf']

    srcCaliptraDir = os.path.join(sWorkspace, sRepo)
    destCaliptraDir = os.path.join(dWorkspace, dRepo)
    repoFiles, repoDirs = listdir_nohidden(srcCaliptraDir)

    ipList = []
    for f in repoFiles:
        if (not f in blacklistRepoDirsFiles):
            copy_file(f, srcCaliptraDir, destCaliptraDir)

    for dir in repoDirs:
        if (not dir in blacklistRepoDirsFiles):
            srcDir_FullPath = os.path.join(srcCaliptraDir, dir)
            destDir_FullPath = os.path.join(destCaliptraDir, dir)
            if (dir == 'src'):
                ipFileList, ipDirList = listdir_nohidden(srcDir_FullPath)
                create_directory(destDir_FullPath)
                for ipDir in ipDirList:
                    if (not ipDir in blacklistIpDirsFiles):
                        src = os.path.join(srcDir_FullPath, str(ipDir))
                        dest = os.path.join(destDir_FullPath, str(ipDir))
                        copy_tree(src, dest)
            elif (dir == 'tools'):
                toolsFileList, toolsDirList = listdir_nohidden(srcDir_FullPath)
                create_directory(destDir_FullPath)
                for dir in toolsDirList:
                    if (dir == 'scripts'):
                        scriptsSrcDir_Full_Path = os.path.join(srcDir_FullPath, dir)
                        scriptsDestDir_Full_Path = os.path.join(destDir_FullPath, dir)
                        create_directory(scriptsDestDir_Full_Path)
                        scriptsFileList, scriptsDirList = listdir_nohidden(scriptsSrcDir_Full_Path)
                        for f in scriptsFileList:
                            if (not f in blacklistScriptsDirsFiles):
                                copy_file(f, scriptsSrcDir_Full_Path,  scriptsDestDir_Full_Path)
                        for d in scriptsDirList:
                            if (not d in blacklistScriptsDirsFiles):
                                copy_file(d, scriptsSrcDir_Full_Path,  scriptsDestDir_Full_Path)
                    else:
                        src = os.path.join(srcDir_FullPath, dir)
                        dest = os.path.join(destDir_FullPath, dir)
                        copy_tree(src, dest)
                for f in toolsFileList:
                    if (not f in blacklistScriptsDirsFiles):
                        copy_file(f, srcDir_FullPath, destDir_FullPath)

    #Remove tests not in the regression suite
    os.chdir(os.path.join(destCaliptraDir, "src/integration"))
    curDir = os.getcwd()
    l0_regress_file = os.path.join(curDir, "stimulus/L0_regression.yml")
    testPaths = []
    x = ''

    with open (l0_regress_file) as f:
        dict = yaml.load(f, Loader=yaml.FullLoader)
        for item in dict["contents"]:
            for key in item.keys():
                for testKey in item[key].keys():
                    if (testKey == 'paths'):
                        testPaths = item[key][testKey]

    for testYml in testPaths:
        x = re.search(r'../test_suites/(\S+)/\S+.yml', testYml)
        integrationTestSuiteList.append(x.groups()[0])

    infoMsg = "Cleaning up integration/test_suites directory"
    logger.info(infoMsg)

    os.chdir("test_suites")
    curDir = os.getcwd()
    testfiles, testdirs = listdir_nohidden(curDir)

    for test in testdirs:
        if (not test in integrationTestSuiteList):
                shutil.rmtree(test)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-sw", "--srcWorkspace",
                        action="store",
                        help="path to internal Caliptra repo workspace")
    parser.add_argument("-sr", "--srcRepo",
                        action="store",
                        help="src repository name")
    parser.add_argument("-dw", "--destWorkspace",
                        action="store",
                        help="path to external Caliptra repo workspace")
    parser.add_argument("-dr", "--destRepo",
                        action="store",
                        help="destination repository name") 
    parser.add_argument("-db", "--destBranch",
                        action="store",
                        help="destination repo branch for updates")                   
    args = parser.parse_args()

    sWorkspace = args.srcWorkspace
    sRepo = args.srcRepo
    dWorkspace = args.destWorkspace
    dRepo = args.destRepo
    dBranch = args.destBranch

    infoMsg = "Command: {} {} {} {} {} {} {} {} {} {} {}".format(sys.argv[0], sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], sys.argv[6], sys.argv[7], sys.argv[8], sys.argv[9], sys.argv[10])
    logger.info(infoMsg)

    logger.info("Prepping Dest Repo")
    prepDestRepo(dWorkspace, dRepo, dBranch)
    logger.info("Prepping Src Repo")
    prepPBSrcRepo(sWorkspace, sRepo)
    logger.info("Copying files")
    copyFilesSrcToDest(sWorkspace, sRepo, dWorkspace, dRepo)
    logger.info("Done copying files")

    
if __name__ == "__main__":
    main()



    




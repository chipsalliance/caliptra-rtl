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

#################################################
#        REQUIRES Python Version >= 3.8         #
#################################################


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

###############
# Global Variables

global prepADORepoScript
global prepGitHubRepoScript
global commitAndPushScript

global blacklistRepoDirsFiles
global blacklistIpDirsFiles
global blacklistScriptsDirsFiles
global blacklistConfigDirsFiles
global integrationTestSuiteList
global ignoreFiles 

prepADORepoScript = "prepADORepo.sh"
prepGitHubRepoScript = "prepGitHubRepo.sh"
commitAndPushScript = "commitChangesToGitHub.sh"

blacklistRepoDirsFiles = ["etc", "config", "dvt_build.log"]
blacklistIpDirsFiles = ["sim_irq_gen", "syn", "aes_secworks", "uvmf_kv"]
blacklistScriptsDirsFiles = ["licenseHeaderCheck.sh", "gen_pb_file_lists.sh", "README.md", "sim_config_parse.py", "github_sync.py", "prepADORepo.sh", "prepGitHubRepo.sh", "commitChangesToGitHub.sh", "run_test_makefile", "syn"]
blacklistConfigDirsFiles = ["design_lint"]
integrationTestSuiteList = ['caliptra_top', 'caliptra_demo', 'caliptra_fmc', 'caliptra_rt', 'smoke_test_trng', 'includes', 'libs']
ignoreFiles = [".dvt", "dvt_build.log", ".git", ".git-comodules", ".gitignore"]

# End global variables
#######################


logger = logging.getLogger()
logger.setLevel(logging.INFO)
console_handler = logging.StreamHandler()
formatter = logging.Formatter('%(asctime)s | %(levelname)s: %(message)s', '%Y-%m-%d %H:%M:%S')
console_handler.setFormatter(formatter)
logger.addHandler(console_handler)

#########################################################################
# Function:     runBashScript                                           #
# Description:  Run command and wait for it to complete before          #
#               returning the results                                   #
#########################################################################

def runBashScript(cmd):
    p = subprocess.Popen(cmd, stdin=None, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE )
    stdout, stderr = p.communicate()
    exitCode = p.returncode
    return exitCode, stdout, stderr
    #return os.popen(cmd).read()

#########################################################################
# Function:     prepDestRepo                                            #
# Description:  Prepare destination repository for syncing all changes  #
#########################################################################

def prepDestRepo(inDestWS, inDestRepo, inDestBranch, ignoreReadme, ignoreReleaseNotes, syncADO2GitHub):
    scriptsDir = get_script_dir()
    if ignoreReadme == True:
        ignoreOpt = "-ir"
    else:
        ignoreOpt = ""
    if ignoreReleaseNotes == True:
        ignoreRelOpt = "-in"
    else:
        ignoreRelOpt = ""
    if syncADO2GitHub == True:
        prepRepoScript = os.path.join(scriptsDir, prepGitHubRepoScript)
        cmd = ". {} -ws {} -db {} -a2g".format(prepRepoScript, inDestWS, inDestBranch)
    else:
        prepRepoScript = os.path.join(scriptsDir, prepADORepoScript)
        cmd = ". {} -ws {} -db {} {} {}".format(prepRepoScript, inDestWS, inDestBranch, ignoreOpt, ignoreRelOpt)
    exitcode, prepRepoStdout, prepRepoStderr = runBashScript(cmd)
    if (exitcode == 0):
        infoMsg = "Destination repo {} setup with branch {}.".format(inDestRepo, inDestBranch)
        logger.info(infoMsg)
        for line in prepRepoStdout.decode().splitlines():
            logger.info(line)
    else:
        errorMsg = f"{prepRepoScript} failed with code: {exitcode}"
        logger.error(errorMsg)
        for line in prepRepoStderr.decode().splitlines():
            logger.error(line)
    return exitcode

#########################################################################
# Function:     prepSrcRepo                                             #
# Description:  Prepare source repository for syncing all changes  #
#########################################################################

def prepSrcRepo(inSrcWS, inSrcRepo, inSrcBranch, ignoreReadme, ignoreReleaseNotes, syncADO2GitHub):
    scriptsDir = get_script_dir()
    if ignoreReadme == True:
        ignoreOpt = "-ir"
    else:
        ignoreOpt = ""
    if ignoreReleaseNotes == True:
        ignoreRelOpt = "-in"
    else:
        ignoreRelOpt = ""
    if syncADO2GitHub == True:
        prepRepoScript = os.path.join(scriptsDir, prepADORepoScript)
        cmd = ". {} -ws {} -a2g {} {}".format(prepRepoScript, inSrcWS, ignoreOpt, ignoreRelOpt)
    else:
        prepRepoScript = os.path.join(scriptsDir, prepGitHubRepoScript)
        cmd = ". {} -ws {}".format(prepRepoScript, inSrcWS)
    exitcode, prepRepoStdout, prepRepoStderr = runBashScript(cmd)
    if (exitcode == 0):
        # FIXME inSrcBranch unused
        infoMsg = "Source repo {} setup with branch {}.".format(inSrcRepo, inSrcBranch)
        logger.info(infoMsg)
        for line in prepRepoStdout.decode().splitlines():
            logger.info(line)
    else:
        errorMsg = f"{prepRepoScript} failed with code: {exitcode}"
        logger.error(errorMsg)
        for line in prepRepoStderr.decode().splitlines():
            logger.error(line)
    return exitcode

#########################################################################
# Function:     commitChangesAndPushBranch                              #
# Description:  Commits all changes in the destination repo/branch      #
#               and pushes branch to remote                             #
#########################################################################

def commitChangesAndPushBranch(inDestWS, inDestRepo, inDestBranch):
    scriptsDir = get_script_dir()
    commitScript = os.path.join(scriptsDir, commitAndPushScript)
    
    cmd = ". {} -ws {} -db {}".format(commitScript, inDestWS, inDestRepo, inDestBranch)
    exitcode, commitStdout, commitStderr = runBashScript(cmd)
    if (exitcode == 0):
        infoMsg = f"Successfully commited all changes to Repo: {inDestRepo} Branch: {inDestBranch}"
        logger.info(infoMsg)
    else:
        errorMsg = f"{commitScript} failed with code: {exitcode}"
        logger.error(errorMsg)
        for line in commitStderr.decode().splitlines():
            logger.error(line)
    return exitcode

#########################################################################
# Helper Functions                                                      #
#########################################################################

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
        infoMsg = "Copying directory {} to {}".format(src, dest)
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
    infoMsg = "Copying file {} to {}".format(src, dest)
    logger.info(infoMsg)
    shutil.copy(src, dest)

#########################################################################
# Function:     copyFilesADOToGitHub               #for ipDir in ipDirList:
                #    if (not ipDir in blacklistIpDirsFiles):
                #        src = os.path.join(srcDir_FullPath, str(ipDir))
                #        dest = os.path.join(destDir_FullPath, str(ipDir))
                #        copy_tree(src, dest)                     #
# Description:  Copies files from ADO to GitHub                         #
#########################################################LICENSE################

def copyFilesADOToGitHub_old(sWorkspace, sRepo, dWorkspace, dRepo):
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
                    elif (dir == 'config'):
                        configSrcDir_Full_Path = os.path.join(srcDir_FullPath, dir)
                        configDestDir_Full_Path = os.path.join(destDir_FullPath, dir)
                        create_directory(configDestDir_Full_Path)
                        configFileList, configDirList = listdir_nohidden(configSrcDir_Full_Path)
                        for f in configFileList:
                            if (not f in blacklistConfigDirsFiles):
                                copy_file(f, configSrcDir_Full_Path,  configDestDir_Full_Path)
                        for d in configDirList:
                            if (not d in blacklistConfigDirsFiles):
                                copy_file(d, configSrcDir_Full_Path,  configDestDir_Full_Path)
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

def copyFilesADOToGitHub(sWorkspace, sRepo, dWorkspace, dRepo):
    srcCaliptraDir = os.path.join(sWorkspace, sRepo)
    destCaliptraDir = os.path.join(dWorkspace, dRepo)
    # NOTE: blacklistRepoDirsFiles is not included in ignore_patterns option as that causes
    # all directories named 'config' to be excluded. 
    # Instead, repo level config directory is removedi in the cleanup stage that runs
    # after all files have been copied to GitHub
    shutil.copytree(srcCaliptraDir, destCaliptraDir, ignore=shutil.ignore_patterns(*ignoreFiles,*blacklistConfigDirsFiles,*blacklistIpDirsFiles,*blacklistScriptsDirsFiles), dirs_exist_ok=True)
    # Manually copy README.md because it is in the blacklist, but
    # we want to keep it in the blacklist to clobber a whole bunch of
    # other README files
    shutil.copy(os.path.join(srcCaliptraDir, "README.md"), destCaliptraDir)
    
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

#########################################################################
# Function:     copyFilesGitHubToADO                                    #
# Description:  Copies files from GitHub to ADO                         #
#########################################################################

def copyFilesGitHubToADO(sWorkspace, sRepo, dWorkspace, dRepo):
    srcCaliptraDir = os.path.join(sWorkspace, sRepo)
    destCaliptraDir = os.path.join(dWorkspace, dRepo)
    repoFiles, repoDirs = listdir_nohidden(srcCaliptraDir)

    ipList = []
    for f in repoFiles:
        copy_file(f, srcCaliptraDir, destCaliptraDir)

    for dir in repoDirs:
        srcDir_FullPath = os.path.join(srcCaliptraDir, dir)
        destDir_FullPath = os.path.join(destCaliptraDir, dir)
        shutil.copytree(srcDir_FullPath, destDir_FullPath, dirs_exist_ok=True)

#########################################################################
# Function:     cleanUpBlackListFilesDirsFromGitHub                     #
# Description:  This is run after ADO to GitHub copy has been           #
#               completed. This deletes any blacklisted files and       #
#               directories that may be present in GitHub repo from     #
#               a previous sync that did not originally blacklist       #
#               the same files and/or directories.                      #
#########################################################################

def cleanUpBlackListFilesDirsFromGitHub(dWorkspace, dRepo):
    infoMsg = "Cleaning up blacklisted files and directories in GitHub Repository"
    logger.info(infoMsg)
    destCaliptraDir = os.path.join(dWorkspace, dRepo)
    os.chdir(destCaliptraDir)
    repoFiles, repoDirs = listdir_nohidden(destCaliptraDir)

    for f in repoFiles:
        if (f in blacklistRepoDirsFiles):
            file_path = os.path.join(destCaliptraDir, f)
            infoMsg = "Removing {}".format(file_path)
            logger.info(infoMsg)
            os.remove(file_path)

    for dir in repoDirs:
        destDir_FullPath = os.path.join(destCaliptraDir, dir)
        if (dir in blacklistRepoDirsFiles):
            infoMsg = "Removing {}".format(dir)
            logger.info(infoMsg)
            shutil.rmtree(dir)
        elif (dir == 'src'):
            ipFileList, ipDirList = listdir_nohidden(destDir_FullPath)
            for ipDir in ipDirList:
                ipDir_FullPath = os.path.join(destDir_FullPath, ipDir)
                docs_path = os.path.join(ipDir_FullPath, "docs")
                if (ipDir in blacklistIpDirsFiles):
                    infoMsg = "Removing {}".format(ipDir_FullPath)
                    logger.info(infoMsg)
                    shutil.rmtree(ipDir_FullPath)
                # FIXME hardcoded 'docs' folder as a blacklist entry.
                elif (os.path.exists(docs_path)):
                    infoMsg = "Removing {}".format(docs_path)
                    logger.info(infoMsg)
                    shutil.rmtree(docs_path)
        elif (dir == 'tools'):
            toolsDir_Full_Path = os.path.join(destDir_FullPath, dir)
            toolsFileList, toolsDirList = listdir_nohidden(destDir_FullPath)
            for dir in toolsDirList:
                if (dir == 'scripts'):
                    scriptsDestDir_Full_Path = os.path.join(destDir_FullPath, dir)
                    scriptsFileList, scriptsDirList = listdir_nohidden(scriptsDestDir_Full_Path)
                    for f in scriptsFileList:
                        if (f in blacklistScriptsDirsFiles):
                            file_path = os.path.join(scriptsDestDir_Full_Path, f)
                            infoMsg = "Removing {}".format(file_path)
                            logger.info(infoMsg)
                            os.remove(file_path)
                    for d in scriptsDirList:
                        if (d in blacklistScriptsDirsFiles):
                            dir_path = os.path.join(scriptsDestDir_Full_Path, d)
                            infoMsg = "Removing {}".format(dir_path)
                            logger.info(infoMsg)
                            shutil.rmtree(dir_path)
                elif (dir == 'config'):
                    configDestDir_Full_Path = os.path.join(destDir_FullPath, dir)
                    configFileList, configDirList = listdir_nohidden(configDestDir_Full_Path)
                    for f in configFileList:
                        if (f in blacklistConfigDirsFiles):
                            file_path = os.path.join(configDestDir_Full_Path, f)
                            infoMsg = "Removing {}".format(file_path)
                            logger.info(infoMsg)
                            os.remove(file_path)
                    for d in configDirList:
                        if (d in blacklistConfigDirsFiles):
                            dir_path = os.path.join(configDestDir_Full_Path, d)
                            infoMsg = "Removing {}".format(dir_path)
                            logger.info(infoMsg)
                            shutil.rmtree(dir_path)
            # FIXME this doesn't match anything - incorrect usage of blacklistScriptsDirsFiles?
            for f in toolsFileList:
                if (f in blacklistScriptsDirsFiles):
                    file_path = os.path.join(toolsDir_Full_Path, f)
                    infoMsg = "Removing {}".format(file_path)
                    logger.info(infoMsg)
                    os.remove(file_path)

#########################################################################
# Function:     main                                                    #
# Description:  Main Function :)                                        #
#########################################################################

def main():
    parser = argparse.ArgumentParser()
    groupSyncDir = parser.add_mutually_exclusive_group()
    groupSyncDir.add_argument("-a2g", "--ado_to_github",
                        action="store_true",
                        help="Sets sync direction to sync from internal ADO repo to external GitHub Repo" )
    groupSyncDir.add_argument("-g2a", "--github_to_ado",
                        action="store_true",
                        help="Set sync direction to sync from external GitHub repo to ADO repo")
    parser.add_argument("-aw", "--adoWorkspace",
                        action="store",
                        help="path to source repo workspace")
    parser.add_argument("-gw", "--githubWorkspace",
                        action="store",
                        help="path to destination repo workspace")
    parser.add_argument("-db", "--destBranch",
                        action="store",
                        help="destination repo branch for updates")                   
    parser.add_argument("-ir", "--ignoreReadme",
                        action="store_true",
                        help="Ignore README timestamp check in source repo")                   
    parser.add_argument("-in", "--ignoreReleaseNotes",
                        action="store_true",
                        help="Ignore ReleaseNotes.txt timestamp check in source repo")                   
    args = parser.parse_args()

    if args.ado_to_github:
        syncADO2GitHub = True
    elif args.github_to_ado:
        syncADO2GitHub = False

    adoWorkspace = args.adoWorkspace
    githubWorkspace = args.githubWorkspace
    dBranch = args.destBranch
    ignoreReadme = args.ignoreReadme
    ignoreReleaseNotes = args.ignoreReleaseNotes

    adoRepo = "Caliptra"
    adoRootBranch = "master"

    githubRepo = "caliptra-rtl"
    githubRootBranch = "dev-msft"

    if syncADO2GitHub == True:
        sWorkspace = adoWorkspace
        sRepo = adoRepo
        sBranch = adoRootBranch
        dWorkspace = githubWorkspace
        dRepo = githubRepo
    else:
        sWorkspace =githubWorkspace
        sRepo = githubRepo
        sBranch = githubRootBranch
        dWorkspace = adoWorkspace
        dRepo = adoRepo   

    print(len(sys.argv))
    infoMsg = "Command:"
    for idx in range(len(sys.argv)):
        infoMsg += " {}".format(sys.argv[idx])
    logger.info(infoMsg)

    if syncADO2GitHub:
        infoMsg = "Syncing internal ADO repo {} {} branch to external GitHub repo {} {} branch)".format(sRepo, sBranch, dRepo, dBranch)
    else:
        infoMsg = "Syncing external GitHub repo {} {} branch to internal ADO repo {} {} branch".format(sRepo, sBranch, dRepo, dBranch)
    logger.info(infoMsg)
    
    # Kill the operation when README is out of date for syncs to
    # GitHub repo, but allow an exception for periodic development updates
    # when automated syncs won't be updating README

    # Prep destination repository
    logger.info("Prepping Destination repository for syncing.")
    if prepDestRepo(dWorkspace, dRepo, dBranch, ignoreReadme, ignoreReleaseNotes, syncADO2GitHub) != 0:
        return 1

    # Prep source repository
    logger.info("Prepping Source repository for syncing")
    if prepSrcRepo(sWorkspace, sRepo, sBranch, ignoreReadme, ignoreReleaseNotes, syncADO2GitHub) != 0:
        return 1
    
    # Copy files from source to destination repository
    if syncADO2GitHub == True:
        logger.info("Syncing files from ADO Repository to GitHub Respository")
        copyFilesADOToGitHub(sWorkspace, sRepo, dWorkspace, dRepo)
        cleanUpBlackListFilesDirsFromGitHub(dWorkspace, dRepo)
        logger.info("Sync Complete")
    else:
        logger.info("Syncing files from GitHub Repository to ADO Respository")
        copyFilesGitHubToADO(sWorkspace, sRepo, dWorkspace, dRepo)
        logger.info("Sync complete")

    # Commit changes and push destination branch    
    #infoMsg = f"Commiting all changes in {dBranch} of {dRepo}"
    #logger.info(infoMsg)
    #commitChangesAndPushBranch(dWorkspace, dRepo, dBranch)

    return 0


if __name__ == "__main__":
    sys.exit(main())

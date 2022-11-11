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


import sys
import os
import shutil
import argparse
import yaml
import re

blacklistRepoDirsFiles = ["SCA", "etc", "config", "dvt_build.log"]
blacklistIpDirsFiles = ["aes", "sim_irq_gen", "syn"]
blacklistScriptsDirsFiles = ["gen_pb_file_lists.sh", "README.md", "sim_config_parse.py", "github_sync.py", "syn"]
#regressionTestList = ['smoke_test_swerv', 'smoke_test_mbox', 'smoke_test_sha512', 'memCpy_ROM_to_dccm', 'memCpy_dccm_to_iccm', 'c_intr_handler', 'smoke_test_ecc', 'smoke_test_hmac', 'smoke_test_kv']

def listdir_nohidden(dirpath):
    fileList = []
    dirList = []
    for f in os.listdir(dirpath):
        f_fullPath = os.path.join(dirpath, f)
        if not f.startswith('.'):
            if os.path.isfile(f_fullPath):
                print(f + "is a file")
                fileList.append(f)
            else:
                dirList.append(f)
    return fileList, dirList

parser = argparse.ArgumentParser()
parser.add_argument("-s", "--srcCaliptra",
                    action="store",
                    help="path to internal Caliptra repo")
parser.add_argument("-d", "--destCaliptra",
                    action="store",
                    help="path to external Caliptra repo")
args = parser.parse_args()

repoFiles, repoDirs = listdir_nohidden(args.srcCaliptra)
print (repoDirs)
print (repoFiles)

print(args.srcCaliptra)
print(args.destCaliptra)

ipList = []
for f in repoFiles:
    if (not f in blacklistRepoDirsFiles):
        src = args.srcCaliptra + "/" + f 
        dest = args.destCaliptra + "/" + f 
        shutil.copy(src, dest)

for dir in repoDirs:
    if (not dir in blacklistRepoDirsFiles):
        srcDir_FullPath = args.srcCaliptra + "/" + dir 
        destDir_FullPath = args.destCaliptra + "/" + dir 
        if (dir == 'src'):
            ipFileList, ipDirList = listdir_nohidden(srcDir_FullPath)
            print(ipDirList)
            os.mkdir(destDir_FullPath)
            for ipDir in ipDirList:
                print(ipDir)
                if (not ipDir in blacklistIpDirsFiles):
                    src = srcDir_FullPath +  "/" + str(ipDir)
                    dest = destDir_FullPath + "/" + str(ipDir)
                    shutil.copytree(src, dest)
        elif (dir == 'tools'):
            toolsFileList, toolsDirList = listdir_nohidden(srcDir_FullPath)
            print(toolsDirList)
            os.mkdir(destDir_FullPath)
            for dir in toolsDirList:
                if (dir == 'scripts'):
                    scriptsSrcDir_Full_Path = srcDir_FullPath + "/" + dir
                    scriptsDestDir_Full_Path = destDir_FullPath + "/" + dir
                    os.mkdir(scriptsDestDir_Full_Path)
                    scriptsFileList, scriptsDirList = listdir_nohidden(scriptsSrcDir_Full_Path)
                    for f in scriptsFileList:
                        if (not f in blacklistScriptsDirsFiles):
                            shutil.copy(scriptsSrcDir_Full_Path + "/" + f,  scriptsDestDir_Full_Path)
                    for d in scriptsDirList:
                        if (not d in blacklistScriptsDirsFiles):
                            shutil.copy(scriptsSrcDir_Full_Path + "/" + d,  scriptsDestDir_Full_Path)
                else:
                    src = srcDir_FullPath + "/" + dir
                    dest = destDir_FullPath + "/" + dir
                    shutil.copytree(src, dest)
            for f in toolsFileList:
                if (not f in blacklistScriptsDirsFiles):
                    src = srcDir_FullPath + "/" + f
                    dest = destDir_FullPath + "/" + f
                    shutil.copy(src, dest)

#Remove tests not in the regression suite
os.chdir(args.destCaliptra + "/src/integration")
curDir = os.getcwd()
print("Current directory is ")
print (curDir)
l0_regress_file = curDir + "/stimulus/L0_regression.yml"
testPaths = []
l0_test_list = []
x = ''

with open (l0_regress_file) as f:
    dict = yaml.load(f, Loader=yaml.FullLoader)
    #print (dict)
    print (dict["contents"])
    print(type(dict["contents"]))
    for item in dict["contents"]:
        #print(type(item))
        for key in item.keys():
            #print(key)
            #print (item[key])
            #print(type(item[key]))
            for testKey in item[key].keys():
                print(testKey)
                if (testKey == 'paths'):
                    testPaths = item[key][testKey]
                    #print(testPaths)

for testYml in testPaths:
    print(testYml)
    x = re.search(r'../test_suites/(\S+)/\S+.yml', testYml)
    #print (x.groups()[0])
    l0_test_list.append(x.groups()[0])
    print (l0_test_list)
    #x = re.search('*/test_suites/(.*)/.*.yml', testYml)

os.chdir("test_suites")
curDir = os.getcwd()
testfiles, testdirs = listdir_nohidden(curDir)
print(testdirs)

for t in testdirs:
    if (not t in l0_test_list and ((t != 'caliptra_demo') or (t != 'includes') or (t != 'printf') or (c != 'caliptra_isr'))):
        shutil.rmtree(t)





    




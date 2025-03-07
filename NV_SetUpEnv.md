
# **Set up Caliptra development environment on NV Farm Guide** #
_*Last Update: 2025/03/07*_
## **Set up SSH Keys first** ##
You're going to need to add an SSH key to your Gitlab account.
https://confluence.nvidia.com/display/WFO/SSH+Keys+for+Git+Repository+Cloning
## **Clone Caliptra from Gitlab** ##
You can refer to this guide:
https://confluence.nvidia.com/display/FalconSecurityIPUserSpace/Run+Caliptra+SHA256+integration+test+on+Farm
## **Equivalent Commands for Git and Perforce (P4):** ##
| Function        | Git Command                   | P4 Command                   |
| --------------- | ----------------------------- | ---------------------------- |
| Initialize Repo | `git init`                    | `p4 depot`                   |
| Clone Repo      | `git clone <repo>`            | `p4 sync //depot/path/...`   |
| Add File        | `git add <file>`              | `p4 add <file>`              |
| Edit File       | *Directly edit the file*      | `p4 edit <file>`             |
| Commit Changes  | `git commit -m "message"`     | `p4 submit -d "message"`     |
| Check Status    | `git status`                  | `p4 opened`                  |
| View Log        | `git log`                     | `p4 changes`                 |
| Branch Management | `git branch`                | `p4 branches`                |
| Switch Branch   | `git checkout <branch>`       | `p4 switch <branch>`         |
| Merge Branch    | `git merge <branch>`          | `p4 integrate <branch>`      |
| Pull Updates    | `git pull`                    | `p4 sync`                    |
| Push Updates    | `git push`                    | `p4 submit`                  |
| Delete File     | `git rm <file>`               | `p4 delete <file>`           |
| View Diff       | `git diff`                    | `p4 diff`                    |
| Revert Changes  | `git revert <commit>`         | `p4 revert`                  
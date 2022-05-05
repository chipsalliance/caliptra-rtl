# **aha_poc** #

## **Workspace Setup** ##

### 1. Create a workspace as shown [here](https://dev.azure.com/ms-tsd/Documents/_wiki/wikis/Documents.wiki/114/Workspace-Commands).

Preferred command for making a workspace with this repo,

`make-workspace --project AHA_POC --top <Please_Add_TOP_NAME_Here> --directory integration_lib`


or,


`make-workspace --url git@ssh.dev.azure.com:v3/ms-tsd/AHA_POC/Caliptra --directory integration_lib`

### 2. Add comodules and then, recursively pull all comodules into the workspace (as per the tags specified in .git-comodules).

`pb workspace update`

<br>

# **Build Command:** #

`pb fe build --tb <top_from_compilespecs>::<compile_unit_name>_tb`


or,


`pb fe build --tb integration_lib::integration_tb`


or,


`pb fe build --tb integration_lib::integration_top`


or with IUS,


`pb fe build --tb integration_lib::integration_top --tool ius --targets packages rtl elab --options rtl="+define+TSD_DISABLE_ASSERTIONS"`


<br>

# **Lint Command:** #


`pb fe lint rtl --tb <top_from_compilespecs>::<compile_unit_name>_tb`


or,


`pb fe lint rtl --tb integration_lib::integration_top`


<br>



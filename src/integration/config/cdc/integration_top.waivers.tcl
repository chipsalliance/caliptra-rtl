##### Add Waivers here
##### Example below: Can dump these commands from GUI as well.

#*****************no_sync violations*****************

cdc report item -scheme no_sync -from "type in src path, careful with wildcards*" -to "*type in dest path, careful with wildcards" -module integration_top -status waived -message {<user_id>  <date>:  <Detailed reason for this waiver>}


#*****************multi_bits violations*****************
cdc report item -scheme multi_bits -from " type in src path, careful with wildcards*" -to "*type in dest path, careful with wildcards" -module integration_top -status waived -message {<user_id>  <date>:  <Detailed reason for this waiver>}

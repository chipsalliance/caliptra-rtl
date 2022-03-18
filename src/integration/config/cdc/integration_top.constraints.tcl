#### Add directives/block specific constraints here

#***************************************************************************************************
# Section 1: Clock Constraints
#***************************************************************************************************

netlist clock    { clk1 } -module { integration_top }  -group { Group_AXI_CLK}

#***************************************************************************************************
# Section 2: Reset Constraints
#***************************************************************************************************

netlist reset    { reset1 } -active_high -async -module { integration_top }

#***************************************************************************************************
# Section 3: Port Constraints
#***************************************************************************************************

# INPUT PORTS

netlist port domain { input_port1 }    -clock { clk1 }    -combo_logic   -module { integration_top}


# OUTPUT PORTS

netlist port domain { output_port1 }         -clock { clk2 }              -module { integration_top }

#***************************************************************************************************
# Section 4: Local constraints i.e. Constants, Blackboxes (blackboxing discouraged...last resort) etc
#***************************************************************************************************

#Constants
netlist constant SIGNALX 0

#Blackbox
netlist blackbox module_name

from systemrdl import RDLCompiler, RDLCompileError
from peakrdl_regblock import RegblockExporter
from peakrdl_regblock.cpuif.passthrough import PassthroughCpuif
import sys
import os

output_dir = os.path.abspath(sys.argv[2])

# Create an instance of the compiler
rdlc = RDLCompiler()
try:
    # Compile your RDL files
    rdlc.compile_file(sys.argv[1])

    # Elaborate the design
    root = rdlc.elaborate()

    # checking if the out directory exists or not.
    if not os.path.exists(output_dir):
      
        # if the out directory is not present then create it.
        os.makedirs(output_dir)
    
    # Export a SystemVerilog implementation
    exporter = RegblockExporter()
    exporter.export(
        root, sys.argv[2],
        cpuif_cls=PassthroughCpuif,
        retime_read_response=False
    )
except RDLCompileError:
    # A compilation error occurred. Exit with error code
    sys.exit(1)

# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Link soc_access libraries (SoC access through generic wires)
OFILES += soc_access.o
AUX_LIB_DIR += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/soc_access
AUX_HEADER_FILES += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/soc_access/soc_access.h
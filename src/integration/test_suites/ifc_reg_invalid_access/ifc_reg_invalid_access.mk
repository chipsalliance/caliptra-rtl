# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Link ifc_reg and soc_access libraries (register testing library)
OFILES += ifc_reg.o
AUX_LIB_DIR += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/ifc_reg
AUX_HEADER_FILES += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/ifc_reg/ifc_reg.h

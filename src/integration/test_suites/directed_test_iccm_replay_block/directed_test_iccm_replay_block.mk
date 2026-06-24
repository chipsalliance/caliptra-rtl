# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Link iccm_hash shared library (helpers for SHA acc lock, ICCM hash flow,
# sha512_ctrl extend driver, and PCR checkers)
OFILES += iccm_hash.o
AUX_LIB_DIR += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/iccm_hash
AUX_HEADER_FILES += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/iccm_hash/iccm_hash.h

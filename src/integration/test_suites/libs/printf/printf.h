// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

#ifndef PRINTF_H
  #define PRINTF_H

/* --------------- symbols/typedefs --------------- */
// When setting global verbosity variable:
//   A lower number results in fewer messages being printed
// When passing an argument to VPRINTF:
//   A lower number results in the message being printed more forcefully
enum printf_verbosity {
    FATAL   = 0,
    ERROR   = 1,
    WARNING = 2,
    LOW     = 3,
    MEDIUM  = 4,
    HIGH    = 5,
    ALL     = 6
};
// Global verbosity defined in the test file
extern enum printf_verbosity verbosity_g;

/* --------------- Function Prototypes --------------- */
int putchar(int c);
int puts(const char* s);
int printf(const char* format, ...);

#define VPRINTF(VERBOSITY, ...) \
    if (VERBOSITY <= verbosity_g) { \
        printf(__VA_ARGS__); \
    }
inline int SEND_STDOUT_CTRL(char ctrl) {putchar(ctrl);}

#endif // PRINTF_H

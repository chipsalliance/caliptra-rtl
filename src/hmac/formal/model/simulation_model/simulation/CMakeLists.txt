########################## Configuration ##########################

# Set the path to the directory where the 'Interfaces.h' header can be found
set(INTERFACES_DIR "/home/advaith-sreevalsan/.vscode-server/extensions/lubis.lubis-vsc-plugin-2023.3.2/LUBIS/include/interfaces")
# Set TRUE if this CMakeLists should download and install SystemC by itself,
# otherwise set to FALSE and give a directory path to another SystemC installation
set(INSTALL_SYSTEMC TRUE)
set(SYSTEMC_INCLUDE_DIR "/home/advaith-sreevalsan/.vscode-server/extensions/lubis.lubis-vsc-plugin-2023.3.2/LUBIS/include/systemc")
set(SYSTEMC_LIB_DIR "")

###################################################################

include(FetchContent)

cmake_minimum_required(VERSION 3.10)
project(LUBIS_Simulation)
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)

if(INSTALL_SYSTEMC)
  FetchContent_Declare(SYSTEMC
    GIT_REPOSITORY https://github.com/accellera-official/systemc
    GIT_TAG 2.3.3
    GIT_SHALLOW TRUE
    GIT_PROGRESS TRUE
  )
  FetchContent_MakeAvailable(SYSTEMC)
  include_directories(
    ${CMAKE_CACHEFILE_DIR}/_deps/systemc-src/src
  )
else()
  include_directories(
    ${SYSTEMC_INCLUDE_DIR}
  )
  link_directories(
    ${SYSTEMC_LIB_DIR}
  )
endif()

include_directories(
  ${INTERFACES_DIR}
)

add_executable(hmac_tests
  hmac_main.cpp
)

target_link_libraries(hmac_tests PRIVATE
  systemc
)

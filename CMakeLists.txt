################################################################
# general configuration
################################################################
cmake_minimum_required (VERSION 3.14.0)
project(VIRAS)

# require the compiler to use C++17
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

file(GLOB_RECURSE sources src/*.cpp src/*.h)

set(CPACK_PACKAGE_NAME "VIRAS")
set(CPACK_PACKAGE_VERSION "0.0.0")


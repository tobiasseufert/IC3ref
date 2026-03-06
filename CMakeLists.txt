cmake_minimum_required(VERSION 3.12)

project(IC3ref LANGUAGES C CXX)

include(CheckIPOSupported)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3 -DNDEBUG")

check_ipo_supported(RESULT IPO_SUPPORTED OUTPUT IPO_ERROR)
if(IPO_SUPPORTED)
  set(CMAKE_INTERPROCEDURAL_OPTIMIZATION_RELEASE ON)
endif()

add_library(aiger STATIC
  aiger/aiger.c
)

target_include_directories(aiger
  PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/aiger
)

add_subdirectory(minisat EXCLUDE_FROM_ALL)

add_executable(IC3
  Certificate.cpp
  IC3.cpp
  Model.cpp
  main.cpp
)

target_include_directories(IC3
  PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/aiger
    ${CMAKE_CURRENT_SOURCE_DIR}/minisat
    ${CMAKE_CURRENT_SOURCE_DIR}/minisat/minisat/core
    ${CMAKE_CURRENT_SOURCE_DIR}/minisat/minisat/mtl
    ${CMAKE_CURRENT_SOURCE_DIR}/minisat/minisat/simp
)

target_compile_definitions(IC3
  PRIVATE
    __STDC_LIMIT_MACROS
    __STDC_FORMAT_MACROS
)

target_compile_options(IC3
  PRIVATE
    -Wall
)

target_link_libraries(IC3
  PRIVATE
    aiger
    minisat-lib-static
)

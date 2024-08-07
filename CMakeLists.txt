cmake_minimum_required(VERSION 3.21)
project(bigint)

set(CMAKE_CXX_STANDARD 17)

find_package(GTest REQUIRED)

add_executable(tests tests.cpp big_integer.cpp)

if (NOT MSVC)
    target_compile_options(tests PRIVATE -Wall -Wno-sign-compare -pedantic)
endif()

option(USE_SANITIZERS "Enable to build with undefined,leak and address sanitizers" OFF)
if (USE_SANITIZERS)
    target_compile_options(tests PUBLIC -fsanitize=address,undefined,leak -fno-sanitize-recover=all)
    target_link_options(tests PUBLIC -fsanitize=address,undefined,leak)
endif()

if (CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    target_compile_options(tests PUBLIC -stdlib=libc++)
endif()

if (CMAKE_BUILD_TYPE MATCHES "Debug")
    target_compile_options(tests PUBLIC -D_GLIBCXX_DEBUG)
endif()

target_link_libraries(tests GTest::gtest GTest::gtest_main)

if (ENABLE_SLOW_TEST)
    target_sources(tests PRIVATE
            ci-extra/big_integer_gmp.h
            ci-extra/big_integer_gmp.cpp
            ci-extra/randomized_tests.cpp)

    target_link_libraries(tests gmp)
endif()

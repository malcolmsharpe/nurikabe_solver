cmake_minimum_required (VERSION 3.1.3)
project (solve)
add_executable(solve solve.cc)
target_compile_options(solve PRIVATE -O -Wall -std=c++11)

# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 2.8

# Default target executed when no arguments are given to make.
default_target: all
.PHONY : default_target

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list

# Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The program to use to edit the cache.
CMAKE_EDIT_COMMAND = /usr/bin/cmake-gui

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/ubuntu/Desktop/Diplomka/git

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/ubuntu/Desktop/Diplomka/git

#=============================================================================
# Targets provided globally by CMake.

# Special rule for the target edit_cache
edit_cache:
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --cyan "Running CMake cache editor..."
	/usr/bin/cmake-gui -H$(CMAKE_SOURCE_DIR) -B$(CMAKE_BINARY_DIR)
.PHONY : edit_cache

# Special rule for the target edit_cache
edit_cache/fast: edit_cache
.PHONY : edit_cache/fast

# Special rule for the target rebuild_cache
rebuild_cache:
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --cyan "Running CMake to regenerate build system..."
	/usr/bin/cmake -H$(CMAKE_SOURCE_DIR) -B$(CMAKE_BINARY_DIR)
.PHONY : rebuild_cache

# Special rule for the target rebuild_cache
rebuild_cache/fast: rebuild_cache
.PHONY : rebuild_cache/fast

# The main all target
all: cmake_check_build_system
	$(CMAKE_COMMAND) -E cmake_progress_start /home/ubuntu/Desktop/Diplomka/git/CMakeFiles /home/ubuntu/Desktop/Diplomka/git/CMakeFiles/progress.marks
	$(MAKE) -f CMakeFiles/Makefile2 all
	$(CMAKE_COMMAND) -E cmake_progress_start /home/ubuntu/Desktop/Diplomka/git/CMakeFiles 0
.PHONY : all

# The main clean target
clean:
	$(MAKE) -f CMakeFiles/Makefile2 clean
.PHONY : clean

# The main clean target
clean/fast: clean
.PHONY : clean/fast

# Prepare targets for installation.
preinstall: all
	$(MAKE) -f CMakeFiles/Makefile2 preinstall
.PHONY : preinstall

# Prepare targets for installation.
preinstall/fast:
	$(MAKE) -f CMakeFiles/Makefile2 preinstall
.PHONY : preinstall/fast

# clear depends
depend:
	$(CMAKE_COMMAND) -H$(CMAKE_SOURCE_DIR) -B$(CMAKE_BINARY_DIR) --check-build-system CMakeFiles/Makefile.cmake 1
.PHONY : depend

#=============================================================================
# Target rules for targets named dip

# Build rule for target.
dip: cmake_check_build_system
	$(MAKE) -f CMakeFiles/Makefile2 dip
.PHONY : dip

# fast build rule for target.
dip/fast:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/build
.PHONY : dip/fast

src/app/Frontend/ast.o: src/app/Frontend/ast.cpp.o
.PHONY : src/app/Frontend/ast.o

# target to build an object file
src/app/Frontend/ast.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ast.cpp.o
.PHONY : src/app/Frontend/ast.cpp.o

src/app/Frontend/ast.i: src/app/Frontend/ast.cpp.i
.PHONY : src/app/Frontend/ast.i

# target to preprocess a source file
src/app/Frontend/ast.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ast.cpp.i
.PHONY : src/app/Frontend/ast.cpp.i

src/app/Frontend/ast.s: src/app/Frontend/ast.cpp.s
.PHONY : src/app/Frontend/ast.s

# target to generate assembly for a file
src/app/Frontend/ast.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ast.cpp.s
.PHONY : src/app/Frontend/ast.cpp.s

src/app/Frontend/astdump.o: src/app/Frontend/astdump.cpp.o
.PHONY : src/app/Frontend/astdump.o

# target to build an object file
src/app/Frontend/astdump.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/astdump.cpp.o
.PHONY : src/app/Frontend/astdump.cpp.o

src/app/Frontend/astdump.i: src/app/Frontend/astdump.cpp.i
.PHONY : src/app/Frontend/astdump.i

# target to preprocess a source file
src/app/Frontend/astdump.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/astdump.cpp.i
.PHONY : src/app/Frontend/astdump.cpp.i

src/app/Frontend/astdump.s: src/app/Frontend/astdump.cpp.s
.PHONY : src/app/Frontend/astdump.s

# target to generate assembly for a file
src/app/Frontend/astdump.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/astdump.cpp.s
.PHONY : src/app/Frontend/astdump.cpp.s

src/app/Frontend/code.o: src/app/Frontend/code.cpp.o
.PHONY : src/app/Frontend/code.o

# target to build an object file
src/app/Frontend/code.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/code.cpp.o
.PHONY : src/app/Frontend/code.cpp.o

src/app/Frontend/code.i: src/app/Frontend/code.cpp.i
.PHONY : src/app/Frontend/code.i

# target to preprocess a source file
src/app/Frontend/code.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/code.cpp.i
.PHONY : src/app/Frontend/code.cpp.i

src/app/Frontend/code.s: src/app/Frontend/code.cpp.s
.PHONY : src/app/Frontend/code.s

# target to generate assembly for a file
src/app/Frontend/code.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/code.cpp.s
.PHONY : src/app/Frontend/code.cpp.s

src/app/Frontend/codedump.o: src/app/Frontend/codedump.cpp.o
.PHONY : src/app/Frontend/codedump.o

# target to build an object file
src/app/Frontend/codedump.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codedump.cpp.o
.PHONY : src/app/Frontend/codedump.cpp.o

src/app/Frontend/codedump.i: src/app/Frontend/codedump.cpp.i
.PHONY : src/app/Frontend/codedump.i

# target to preprocess a source file
src/app/Frontend/codedump.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codedump.cpp.i
.PHONY : src/app/Frontend/codedump.cpp.i

src/app/Frontend/codedump.s: src/app/Frontend/codedump.cpp.s
.PHONY : src/app/Frontend/codedump.s

# target to generate assembly for a file
src/app/Frontend/codedump.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codedump.cpp.s
.PHONY : src/app/Frontend/codedump.cpp.s

src/app/Frontend/codesubst.o: src/app/Frontend/codesubst.cpp.o
.PHONY : src/app/Frontend/codesubst.o

# target to build an object file
src/app/Frontend/codesubst.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codesubst.cpp.o
.PHONY : src/app/Frontend/codesubst.cpp.o

src/app/Frontend/codesubst.i: src/app/Frontend/codesubst.cpp.i
.PHONY : src/app/Frontend/codesubst.i

# target to preprocess a source file
src/app/Frontend/codesubst.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codesubst.cpp.i
.PHONY : src/app/Frontend/codesubst.cpp.i

src/app/Frontend/codesubst.s: src/app/Frontend/codesubst.cpp.s
.PHONY : src/app/Frontend/codesubst.s

# target to generate assembly for a file
src/app/Frontend/codesubst.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codesubst.cpp.s
.PHONY : src/app/Frontend/codesubst.cpp.s

src/app/Frontend/codetable.o: src/app/Frontend/codetable.cpp.o
.PHONY : src/app/Frontend/codetable.o

# target to build an object file
src/app/Frontend/codetable.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codetable.cpp.o
.PHONY : src/app/Frontend/codetable.cpp.o

src/app/Frontend/codetable.i: src/app/Frontend/codetable.cpp.i
.PHONY : src/app/Frontend/codetable.i

# target to preprocess a source file
src/app/Frontend/codetable.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codetable.cpp.i
.PHONY : src/app/Frontend/codetable.cpp.i

src/app/Frontend/codetable.s: src/app/Frontend/codetable.cpp.s
.PHONY : src/app/Frontend/codetable.s

# target to generate assembly for a file
src/app/Frontend/codetable.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/codetable.cpp.s
.PHONY : src/app/Frontend/codetable.cpp.s

src/app/Frontend/expnf.o: src/app/Frontend/expnf.cpp.o
.PHONY : src/app/Frontend/expnf.o

# target to build an object file
src/app/Frontend/expnf.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/expnf.cpp.o
.PHONY : src/app/Frontend/expnf.cpp.o

src/app/Frontend/expnf.i: src/app/Frontend/expnf.cpp.i
.PHONY : src/app/Frontend/expnf.i

# target to preprocess a source file
src/app/Frontend/expnf.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/expnf.cpp.i
.PHONY : src/app/Frontend/expnf.cpp.i

src/app/Frontend/expnf.s: src/app/Frontend/expnf.cpp.s
.PHONY : src/app/Frontend/expnf.s

# target to generate assembly for a file
src/app/Frontend/expnf.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/expnf.cpp.s
.PHONY : src/app/Frontend/expnf.cpp.s

src/app/Frontend/freevars.o: src/app/Frontend/freevars.cpp.o
.PHONY : src/app/Frontend/freevars.o

# target to build an object file
src/app/Frontend/freevars.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/freevars.cpp.o
.PHONY : src/app/Frontend/freevars.cpp.o

src/app/Frontend/freevars.i: src/app/Frontend/freevars.cpp.i
.PHONY : src/app/Frontend/freevars.i

# target to preprocess a source file
src/app/Frontend/freevars.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/freevars.cpp.i
.PHONY : src/app/Frontend/freevars.cpp.i

src/app/Frontend/freevars.s: src/app/Frontend/freevars.cpp.s
.PHONY : src/app/Frontend/freevars.s

# target to generate assembly for a file
src/app/Frontend/freevars.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/freevars.cpp.s
.PHONY : src/app/Frontend/freevars.cpp.s

src/app/Frontend/ident.o: src/app/Frontend/ident.cpp.o
.PHONY : src/app/Frontend/ident.o

# target to build an object file
src/app/Frontend/ident.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ident.cpp.o
.PHONY : src/app/Frontend/ident.cpp.o

src/app/Frontend/ident.i: src/app/Frontend/ident.cpp.i
.PHONY : src/app/Frontend/ident.i

# target to preprocess a source file
src/app/Frontend/ident.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ident.cpp.i
.PHONY : src/app/Frontend/ident.cpp.i

src/app/Frontend/ident.s: src/app/Frontend/ident.cpp.s
.PHONY : src/app/Frontend/ident.s

# target to generate assembly for a file
src/app/Frontend/ident.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ident.cpp.s
.PHONY : src/app/Frontend/ident.cpp.s

src/app/Frontend/lib.o: src/app/Frontend/lib.cpp.o
.PHONY : src/app/Frontend/lib.o

# target to build an object file
src/app/Frontend/lib.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/lib.cpp.o
.PHONY : src/app/Frontend/lib.cpp.o

src/app/Frontend/lib.i: src/app/Frontend/lib.cpp.i
.PHONY : src/app/Frontend/lib.i

# target to preprocess a source file
src/app/Frontend/lib.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/lib.cpp.i
.PHONY : src/app/Frontend/lib.cpp.i

src/app/Frontend/lib.s: src/app/Frontend/lib.cpp.s
.PHONY : src/app/Frontend/lib.s

# target to generate assembly for a file
src/app/Frontend/lib.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/lib.cpp.s
.PHONY : src/app/Frontend/lib.cpp.s

src/app/Frontend/makeguide.o: src/app/Frontend/makeguide.cpp.o
.PHONY : src/app/Frontend/makeguide.o

# target to build an object file
src/app/Frontend/makeguide.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/makeguide.cpp.o
.PHONY : src/app/Frontend/makeguide.cpp.o

src/app/Frontend/makeguide.i: src/app/Frontend/makeguide.cpp.i
.PHONY : src/app/Frontend/makeguide.i

# target to preprocess a source file
src/app/Frontend/makeguide.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/makeguide.cpp.i
.PHONY : src/app/Frontend/makeguide.cpp.i

src/app/Frontend/makeguide.s: src/app/Frontend/makeguide.cpp.s
.PHONY : src/app/Frontend/makeguide.s

# target to generate assembly for a file
src/app/Frontend/makeguide.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/makeguide.cpp.s
.PHONY : src/app/Frontend/makeguide.cpp.s

src/app/Frontend/offsets.o: src/app/Frontend/offsets.cpp.o
.PHONY : src/app/Frontend/offsets.o

# target to build an object file
src/app/Frontend/offsets.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/offsets.cpp.o
.PHONY : src/app/Frontend/offsets.cpp.o

src/app/Frontend/offsets.i: src/app/Frontend/offsets.cpp.i
.PHONY : src/app/Frontend/offsets.i

# target to preprocess a source file
src/app/Frontend/offsets.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/offsets.cpp.i
.PHONY : src/app/Frontend/offsets.cpp.i

src/app/Frontend/offsets.s: src/app/Frontend/offsets.cpp.s
.PHONY : src/app/Frontend/offsets.s

# target to generate assembly for a file
src/app/Frontend/offsets.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/offsets.cpp.s
.PHONY : src/app/Frontend/offsets.cpp.s

src/app/Frontend/parser.o: src/app/Frontend/parser.cpp.o
.PHONY : src/app/Frontend/parser.o

# target to build an object file
src/app/Frontend/parser.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/parser.cpp.o
.PHONY : src/app/Frontend/parser.cpp.o

src/app/Frontend/parser.i: src/app/Frontend/parser.cpp.i
.PHONY : src/app/Frontend/parser.i

# target to preprocess a source file
src/app/Frontend/parser.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/parser.cpp.i
.PHONY : src/app/Frontend/parser.cpp.i

src/app/Frontend/parser.s: src/app/Frontend/parser.cpp.s
.PHONY : src/app/Frontend/parser.s

# target to generate assembly for a file
src/app/Frontend/parser.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/parser.cpp.s
.PHONY : src/app/Frontend/parser.cpp.s

src/app/Frontend/predlib.o: src/app/Frontend/predlib.cpp.o
.PHONY : src/app/Frontend/predlib.o

# target to build an object file
src/app/Frontend/predlib.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/predlib.cpp.o
.PHONY : src/app/Frontend/predlib.cpp.o

src/app/Frontend/predlib.i: src/app/Frontend/predlib.cpp.i
.PHONY : src/app/Frontend/predlib.i

# target to preprocess a source file
src/app/Frontend/predlib.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/predlib.cpp.i
.PHONY : src/app/Frontend/predlib.cpp.i

src/app/Frontend/predlib.s: src/app/Frontend/predlib.cpp.s
.PHONY : src/app/Frontend/predlib.s

# target to generate assembly for a file
src/app/Frontend/predlib.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/predlib.cpp.s
.PHONY : src/app/Frontend/predlib.cpp.s

src/app/Frontend/printline.o: src/app/Frontend/printline.cpp.o
.PHONY : src/app/Frontend/printline.o

# target to build an object file
src/app/Frontend/printline.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/printline.cpp.o
.PHONY : src/app/Frontend/printline.cpp.o

src/app/Frontend/printline.i: src/app/Frontend/printline.cpp.i
.PHONY : src/app/Frontend/printline.i

# target to preprocess a source file
src/app/Frontend/printline.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/printline.cpp.i
.PHONY : src/app/Frontend/printline.cpp.i

src/app/Frontend/printline.s: src/app/Frontend/printline.cpp.s
.PHONY : src/app/Frontend/printline.s

# target to generate assembly for a file
src/app/Frontend/printline.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/printline.cpp.s
.PHONY : src/app/Frontend/printline.cpp.s

src/app/Frontend/reduce.o: src/app/Frontend/reduce.cpp.o
.PHONY : src/app/Frontend/reduce.o

# target to build an object file
src/app/Frontend/reduce.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/reduce.cpp.o
.PHONY : src/app/Frontend/reduce.cpp.o

src/app/Frontend/reduce.i: src/app/Frontend/reduce.cpp.i
.PHONY : src/app/Frontend/reduce.i

# target to preprocess a source file
src/app/Frontend/reduce.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/reduce.cpp.i
.PHONY : src/app/Frontend/reduce.cpp.i

src/app/Frontend/reduce.s: src/app/Frontend/reduce.cpp.s
.PHONY : src/app/Frontend/reduce.s

# target to generate assembly for a file
src/app/Frontend/reduce.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/reduce.cpp.s
.PHONY : src/app/Frontend/reduce.cpp.s

src/app/Frontend/scanner.o: src/app/Frontend/scanner.cpp.o
.PHONY : src/app/Frontend/scanner.o

# target to build an object file
src/app/Frontend/scanner.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/scanner.cpp.o
.PHONY : src/app/Frontend/scanner.cpp.o

src/app/Frontend/scanner.i: src/app/Frontend/scanner.cpp.i
.PHONY : src/app/Frontend/scanner.i

# target to preprocess a source file
src/app/Frontend/scanner.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/scanner.cpp.i
.PHONY : src/app/Frontend/scanner.cpp.i

src/app/Frontend/scanner.s: src/app/Frontend/scanner.cpp.s
.PHONY : src/app/Frontend/scanner.s

# target to generate assembly for a file
src/app/Frontend/scanner.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/scanner.cpp.s
.PHONY : src/app/Frontend/scanner.cpp.s

src/app/Frontend/signature.o: src/app/Frontend/signature.cpp.o
.PHONY : src/app/Frontend/signature.o

# target to build an object file
src/app/Frontend/signature.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/signature.cpp.o
.PHONY : src/app/Frontend/signature.cpp.o

src/app/Frontend/signature.i: src/app/Frontend/signature.cpp.i
.PHONY : src/app/Frontend/signature.i

# target to preprocess a source file
src/app/Frontend/signature.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/signature.cpp.i
.PHONY : src/app/Frontend/signature.cpp.i

src/app/Frontend/signature.s: src/app/Frontend/signature.cpp.s
.PHONY : src/app/Frontend/signature.s

# target to generate assembly for a file
src/app/Frontend/signature.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/signature.cpp.s
.PHONY : src/app/Frontend/signature.cpp.s

src/app/Frontend/st_dfa.o: src/app/Frontend/st_dfa.cpp.o
.PHONY : src/app/Frontend/st_dfa.o

# target to build an object file
src/app/Frontend/st_dfa.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/st_dfa.cpp.o
.PHONY : src/app/Frontend/st_dfa.cpp.o

src/app/Frontend/st_dfa.i: src/app/Frontend/st_dfa.cpp.i
.PHONY : src/app/Frontend/st_dfa.i

# target to preprocess a source file
src/app/Frontend/st_dfa.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/st_dfa.cpp.i
.PHONY : src/app/Frontend/st_dfa.cpp.i

src/app/Frontend/st_dfa.s: src/app/Frontend/st_dfa.cpp.s
.PHONY : src/app/Frontend/st_dfa.s

# target to generate assembly for a file
src/app/Frontend/st_dfa.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/st_dfa.cpp.s
.PHONY : src/app/Frontend/st_dfa.cpp.s

src/app/Frontend/st_gta.o: src/app/Frontend/st_gta.cpp.o
.PHONY : src/app/Frontend/st_gta.o

# target to build an object file
src/app/Frontend/st_gta.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/st_gta.cpp.o
.PHONY : src/app/Frontend/st_gta.cpp.o

src/app/Frontend/st_gta.i: src/app/Frontend/st_gta.cpp.i
.PHONY : src/app/Frontend/st_gta.i

# target to preprocess a source file
src/app/Frontend/st_gta.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/st_gta.cpp.i
.PHONY : src/app/Frontend/st_gta.cpp.i

src/app/Frontend/st_gta.s: src/app/Frontend/st_gta.cpp.s
.PHONY : src/app/Frontend/st_gta.s

# target to generate assembly for a file
src/app/Frontend/st_gta.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/st_gta.cpp.s
.PHONY : src/app/Frontend/st_gta.cpp.s

src/app/Frontend/symboltable.o: src/app/Frontend/symboltable.cpp.o
.PHONY : src/app/Frontend/symboltable.o

# target to build an object file
src/app/Frontend/symboltable.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/symboltable.cpp.o
.PHONY : src/app/Frontend/symboltable.cpp.o

src/app/Frontend/symboltable.i: src/app/Frontend/symboltable.cpp.i
.PHONY : src/app/Frontend/symboltable.i

# target to preprocess a source file
src/app/Frontend/symboltable.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/symboltable.cpp.i
.PHONY : src/app/Frontend/symboltable.cpp.i

src/app/Frontend/symboltable.s: src/app/Frontend/symboltable.cpp.s
.PHONY : src/app/Frontend/symboltable.s

# target to generate assembly for a file
src/app/Frontend/symboltable.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/symboltable.cpp.s
.PHONY : src/app/Frontend/symboltable.cpp.s

src/app/Frontend/timer.o: src/app/Frontend/timer.cpp.o
.PHONY : src/app/Frontend/timer.o

# target to build an object file
src/app/Frontend/timer.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/timer.cpp.o
.PHONY : src/app/Frontend/timer.cpp.o

src/app/Frontend/timer.i: src/app/Frontend/timer.cpp.i
.PHONY : src/app/Frontend/timer.i

# target to preprocess a source file
src/app/Frontend/timer.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/timer.cpp.i
.PHONY : src/app/Frontend/timer.cpp.i

src/app/Frontend/timer.s: src/app/Frontend/timer.cpp.s
.PHONY : src/app/Frontend/timer.s

# target to generate assembly for a file
src/app/Frontend/timer.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/timer.cpp.s
.PHONY : src/app/Frontend/timer.cpp.s

src/app/Frontend/untyped.o: src/app/Frontend/untyped.cpp.o
.PHONY : src/app/Frontend/untyped.o

# target to build an object file
src/app/Frontend/untyped.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/untyped.cpp.o
.PHONY : src/app/Frontend/untyped.cpp.o

src/app/Frontend/untyped.i: src/app/Frontend/untyped.cpp.i
.PHONY : src/app/Frontend/untyped.i

# target to preprocess a source file
src/app/Frontend/untyped.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/untyped.cpp.i
.PHONY : src/app/Frontend/untyped.cpp.i

src/app/Frontend/untyped.s: src/app/Frontend/untyped.cpp.s
.PHONY : src/app/Frontend/untyped.s

# target to generate assembly for a file
src/app/Frontend/untyped.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/untyped.cpp.s
.PHONY : src/app/Frontend/untyped.cpp.s

src/app/Frontend/ws1s-formula-to-automaton.o: src/app/Frontend/ws1s-formula-to-automaton.cpp.o
.PHONY : src/app/Frontend/ws1s-formula-to-automaton.o

# target to build an object file
src/app/Frontend/ws1s-formula-to-automaton.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ws1s-formula-to-automaton.cpp.o
.PHONY : src/app/Frontend/ws1s-formula-to-automaton.cpp.o

src/app/Frontend/ws1s-formula-to-automaton.i: src/app/Frontend/ws1s-formula-to-automaton.cpp.i
.PHONY : src/app/Frontend/ws1s-formula-to-automaton.i

# target to preprocess a source file
src/app/Frontend/ws1s-formula-to-automaton.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ws1s-formula-to-automaton.cpp.i
.PHONY : src/app/Frontend/ws1s-formula-to-automaton.cpp.i

src/app/Frontend/ws1s-formula-to-automaton.s: src/app/Frontend/ws1s-formula-to-automaton.cpp.s
.PHONY : src/app/Frontend/ws1s-formula-to-automaton.s

# target to generate assembly for a file
src/app/Frontend/ws1s-formula-to-automaton.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ws1s-formula-to-automaton.cpp.s
.PHONY : src/app/Frontend/ws1s-formula-to-automaton.cpp.s

src/app/Frontend/ws2s-formula-to-automaton.o: src/app/Frontend/ws2s-formula-to-automaton.cpp.o
.PHONY : src/app/Frontend/ws2s-formula-to-automaton.o

# target to build an object file
src/app/Frontend/ws2s-formula-to-automaton.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ws2s-formula-to-automaton.cpp.o
.PHONY : src/app/Frontend/ws2s-formula-to-automaton.cpp.o

src/app/Frontend/ws2s-formula-to-automaton.i: src/app/Frontend/ws2s-formula-to-automaton.cpp.i
.PHONY : src/app/Frontend/ws2s-formula-to-automaton.i

# target to preprocess a source file
src/app/Frontend/ws2s-formula-to-automaton.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ws2s-formula-to-automaton.cpp.i
.PHONY : src/app/Frontend/ws2s-formula-to-automaton.cpp.i

src/app/Frontend/ws2s-formula-to-automaton.s: src/app/Frontend/ws2s-formula-to-automaton.cpp.s
.PHONY : src/app/Frontend/ws2s-formula-to-automaton.s

# target to generate assembly for a file
src/app/Frontend/ws2s-formula-to-automaton.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/Frontend/ws2s-formula-to-automaton.cpp.s
.PHONY : src/app/Frontend/ws2s-formula-to-automaton.cpp.s

src/app/main.o: src/app/main.cpp.o
.PHONY : src/app/main.o

# target to build an object file
src/app/main.cpp.o:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/main.cpp.o
.PHONY : src/app/main.cpp.o

src/app/main.i: src/app/main.cpp.i
.PHONY : src/app/main.i

# target to preprocess a source file
src/app/main.cpp.i:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/main.cpp.i
.PHONY : src/app/main.cpp.i

src/app/main.s: src/app/main.cpp.s
.PHONY : src/app/main.s

# target to generate assembly for a file
src/app/main.cpp.s:
	$(MAKE) -f CMakeFiles/dip.dir/build.make CMakeFiles/dip.dir/src/app/main.cpp.s
.PHONY : src/app/main.cpp.s

# Help Target
help:
	@echo "The following are some of the valid targets for this Makefile:"
	@echo "... all (the default if no target is provided)"
	@echo "... clean"
	@echo "... depend"
	@echo "... dip"
	@echo "... edit_cache"
	@echo "... rebuild_cache"
	@echo "... src/app/Frontend/ast.o"
	@echo "... src/app/Frontend/ast.i"
	@echo "... src/app/Frontend/ast.s"
	@echo "... src/app/Frontend/astdump.o"
	@echo "... src/app/Frontend/astdump.i"
	@echo "... src/app/Frontend/astdump.s"
	@echo "... src/app/Frontend/code.o"
	@echo "... src/app/Frontend/code.i"
	@echo "... src/app/Frontend/code.s"
	@echo "... src/app/Frontend/codedump.o"
	@echo "... src/app/Frontend/codedump.i"
	@echo "... src/app/Frontend/codedump.s"
	@echo "... src/app/Frontend/codesubst.o"
	@echo "... src/app/Frontend/codesubst.i"
	@echo "... src/app/Frontend/codesubst.s"
	@echo "... src/app/Frontend/codetable.o"
	@echo "... src/app/Frontend/codetable.i"
	@echo "... src/app/Frontend/codetable.s"
	@echo "... src/app/Frontend/expnf.o"
	@echo "... src/app/Frontend/expnf.i"
	@echo "... src/app/Frontend/expnf.s"
	@echo "... src/app/Frontend/freevars.o"
	@echo "... src/app/Frontend/freevars.i"
	@echo "... src/app/Frontend/freevars.s"
	@echo "... src/app/Frontend/ident.o"
	@echo "... src/app/Frontend/ident.i"
	@echo "... src/app/Frontend/ident.s"
	@echo "... src/app/Frontend/lib.o"
	@echo "... src/app/Frontend/lib.i"
	@echo "... src/app/Frontend/lib.s"
	@echo "... src/app/Frontend/makeguide.o"
	@echo "... src/app/Frontend/makeguide.i"
	@echo "... src/app/Frontend/makeguide.s"
	@echo "... src/app/Frontend/offsets.o"
	@echo "... src/app/Frontend/offsets.i"
	@echo "... src/app/Frontend/offsets.s"
	@echo "... src/app/Frontend/parser.o"
	@echo "... src/app/Frontend/parser.i"
	@echo "... src/app/Frontend/parser.s"
	@echo "... src/app/Frontend/predlib.o"
	@echo "... src/app/Frontend/predlib.i"
	@echo "... src/app/Frontend/predlib.s"
	@echo "... src/app/Frontend/printline.o"
	@echo "... src/app/Frontend/printline.i"
	@echo "... src/app/Frontend/printline.s"
	@echo "... src/app/Frontend/reduce.o"
	@echo "... src/app/Frontend/reduce.i"
	@echo "... src/app/Frontend/reduce.s"
	@echo "... src/app/Frontend/scanner.o"
	@echo "... src/app/Frontend/scanner.i"
	@echo "... src/app/Frontend/scanner.s"
	@echo "... src/app/Frontend/signature.o"
	@echo "... src/app/Frontend/signature.i"
	@echo "... src/app/Frontend/signature.s"
	@echo "... src/app/Frontend/st_dfa.o"
	@echo "... src/app/Frontend/st_dfa.i"
	@echo "... src/app/Frontend/st_dfa.s"
	@echo "... src/app/Frontend/st_gta.o"
	@echo "... src/app/Frontend/st_gta.i"
	@echo "... src/app/Frontend/st_gta.s"
	@echo "... src/app/Frontend/symboltable.o"
	@echo "... src/app/Frontend/symboltable.i"
	@echo "... src/app/Frontend/symboltable.s"
	@echo "... src/app/Frontend/timer.o"
	@echo "... src/app/Frontend/timer.i"
	@echo "... src/app/Frontend/timer.s"
	@echo "... src/app/Frontend/untyped.o"
	@echo "... src/app/Frontend/untyped.i"
	@echo "... src/app/Frontend/untyped.s"
	@echo "... src/app/Frontend/ws1s-formula-to-automaton.o"
	@echo "... src/app/Frontend/ws1s-formula-to-automaton.i"
	@echo "... src/app/Frontend/ws1s-formula-to-automaton.s"
	@echo "... src/app/Frontend/ws2s-formula-to-automaton.o"
	@echo "... src/app/Frontend/ws2s-formula-to-automaton.i"
	@echo "... src/app/Frontend/ws2s-formula-to-automaton.s"
	@echo "... src/app/main.o"
	@echo "... src/app/main.i"
	@echo "... src/app/main.s"
.PHONY : help



#=============================================================================
# Special targets to cleanup operation of make.

# Special rule to run CMake to check the build system integrity.
# No rule that depends on this can have commands that come from listfiles
# because they might be regenerated.
cmake_check_build_system:
	$(CMAKE_COMMAND) -H$(CMAKE_SOURCE_DIR) -B$(CMAKE_BINARY_DIR) --check-build-system CMakeFiles/Makefile.cmake 0
.PHONY : cmake_check_build_system


Setup Instructions

For the following commands, replace <andrew_id> with your andrew id

1. Log in

Log into ECE machines
cd /afs/ece.cmu.edu/project/seth_group/

If you don’t have a personal directory:
mkdir <andrew_id>

2. Download and build gcc 12.2.0

At /afs/ece.cmu.edu/project/seth_group/<andrew_id>:

Download gcc 12.2.0 You can download gcc-12.2.0.tar.gz from https://ftp.gnu.org/gnu/gcc/gcc-12.2.0/
Move the file into /afs/ece.cmu.edu/project/seth_group/<andrew_id>

tar -xvf gcc-12.2.0.tar.gz

cd gcc-12.2.0
./contrib/download_prerequisites
cd ..
mkdir gcc-build
cd gcc-build
./../gcc-12.2.0/configure --prefix=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-12.2.0 --program-suffix=-12.2.0 --enable-languages=c,c++,fortran,go
make (this can take a few hours)
make install

3. Download and cmake binaries

At /afs/ece.cmu.edu/project/seth_group/<andrew_id>:

wget https://github.com/Kitware/CMake/releases/download/v3.14.0/cmake-3.14.0-Linux-x86_64.tar.gz
tar -xzvf  cmake-3.14.0-Linux-x86_64.tar.gz

4. Setting up the environment:

Add the following to ~/.bashrc or ~/.bash_profile, replacing <andrew_id> with your andrew id:

# Ninja tool
export PATH=/afs/ece.cmu.edu/usr/seth/opt/ninja/bin:/afs/ece.cmu.edu/usr/seth/opt/binutils.gold/bin:/afs/ece.cmu.edu/usr/seth/opt/cmake/bin:$PATH

# RR tool
export PATH=$PATH:/afs/ece.cmu.edu/usr/cpakha/Public/rr_d/usr/bin/

# GCC tool
export PATH=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-12.2.0/bin:$PATH
export LD_LIBRARY_PATH=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-12.2.0/lib64:/afs/ece/project/seth_group/<andrew_id>/GCC-12.2.0/lib:$LD_LIBRARY_PATH

# Clang/Clang++
export PATH=/afs/ece/project/seth_group/<andrew_id>/uli-opencilk-project/build/bin:$PATH
export LD_LIBRARY_PATH=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/uli-opencilk-project/build/lib:$LD_LIBRARY_PATH

# OpenCilk-runtime 
export LD_LIBRARY_PATH=/afs/ece/project/seth_group/<andrew_id>/cheetah/build/lib:$LD_LIBRARY_PATH

# Uli-runtime
export LIBRARY_PATH=/afs/ece/project/seth_group/<andrew_id>/uli-runtime/runtime:$LD_LIBRARY_PATH

# Include for opencilk
export C_INCLUDE_PATH=/afs/ece/project/seth_group/<andrew_id>/cheetah/include/

export LD_BIND_NOW=1

Then:
source ~/.bashrc or source ~/.bash_profile

5. Download Build the LazyD compiler

At /afs/ece.cmu.edu/project/seth_group/<andrew_id>:

git clone git@github.com:user-level-interrupts/uli-opencilk-project.git

cd uli-opencilk-project
mkdir build

Run the following for debug build (slower in compiling a Cilk code, but gives location of where the segmentation fault occured during compile time)

/afs/ece/project/seth_group/<andrew_id>/cmake-3.14.0-Linux-x86_64/bin/cmake -S llvm -B build -G Ninja  -DLLVM_USE_SPLIT_DWARF=ON -DLLVM_USE_LINKER=gold -DLLVM_LINK_LLVM_DYLIB=true -DLLVM_ENABLE_ASSERTIONS=TRUE -DCMAKE_BUILD_TYPE=Debug -DLLVM_TARGETS_TO_BUILD=X86 -DCMAKE_C_COMPILER=gcc-12.2.0  -DCMAKE_CXX_COMPILER=g++-12.2.0 -DLLVM_ENABLE_PROJECTS="clang;lld" -DCMAKE_INSTALL_PREFIX=/afs/ece/project/seth_group/<andrew_id>/my-opencilk-repo/build -DCMAKE_SHARED_LINKER_FLAGS="-B$ldpath -Wl,--gdb-index" -DCMAKE_EXE_LINKER_FLAGS="-B$ldpath -Wl,--gdb-index" -DLLVM_BINUTILS_INCDIR=/afs/ece.cmu.edu/usr/seth/opt/binutils.gold/include 2>&1 | tee cmake.out.log


Run the following for release build (faster in compiling a Cilk code,  but do not give location of where the segmentation occured during compile time)

/afs/ece/project/seth_group/<andrew_id>/cmake-3.14.0-Linux-x86_64/bin/cmake -S llvm -B build -G Ninja  -DLLVM_USE_SPLIT_DWARF=ON -DLLVM_USE_LINKER=gold -DLLVM_LINK_LLVM_DYLIB=true -DLLVM_ENABLE_ASSERTIONS=TRUE -DCMAKE_BUILD_TYPE=Release -DLLVM_TARGETS_TO_BUILD=X86 -DCMAKE_C_COMPILER=gcc-12.2.0  -DCMAKE_CXX_COMPILER=g++-12.2.0 -DLLVM_ENABLE_PROJECTS="clang;lld" -DCMAKE_INSTALL_PREFIX=/afs/ece/project/seth_group/<andrew_id>/my-opencilk-repo/build -DCMAKE_SHARED_LINKER_FLAGS="-B$ldpath -Wl,--gdb-index" -DCMAKE_EXE_LINKER_FLAGS="-B$ldpath -Wl,--gdb-index" -DLLVM_BINUTILS_INCDIR=/afs/ece.cmu.edu/usr/seth/opt/binutils.gold/include 2>&1 | tee cmake.out.log


In uli-opencilk-repo/build:

ninja -j`nproc`

6. Download and Compile the LazyD runtime

At /afs/ece.cmu.edu/project/seth_group/<andrew_id>:

git clone git@github.com:user-level-interrupts/uli-runtime.git

cd uli-runtime/runtime

make clean && make libunwind_scheduler.a

7. Compile the opencilk-runtime

At /afs/ece.cmu.edu/project/seth_group/<andrew_id>:

git clone git@github.com:user-level-interrupts/cheetah.git

Follow the README.md in cheetah/ to compile opencilk's runtime

8. Compile a cilk5 code

At /afs/ece.cmu.edu/project/seth_group/<andrew_id>:

git clone git@github.com:user-level-interrupts/cilkbench.git

cd cilkbench
bash testCilk5.sh -x=0 -w=0 -uf fib

Try to run the generated binary:

cd cilk5/

Run in serial
CILK_NWORKERS=1 ./fib 42

Run in parallel
CILK_NWORKERS=`nproc` ./fib 42

9. Compile a pbbs_v2 code

At /afs/ece.cmu.edu/project/seth_group/<andrew_id>:

git clone git@github.com:user-level-interrupts/pbbsbench.git

cd cilkbench
ln -s ../pbbsbench/benchmarks pbbs_v2
cd ../pbbsbench/benchmarks 
ln -s ../common common

At /afs/ece.cmu.edu/project/seth_group/cilkbench

cd pbbs_v2/delaunayTriangulation/incrementalDelaunay

make clean && POLL0=1 make

cd ../geometryData/data/

make 2DinCube_10M

cd ../../incrementalDelaunay/

CILK_NWORKERS=`nproc` ./delaunay -r 1 -o 2DinCube_10M.out -i ../geometryData/data/2DinCube_10M

CILK_NWORKERS=1 ../bench/delaunayCheck  ../geometryData/data/2DinCube_10M 2DinCube_10M.out
<Expect no error message>

10. LazyD Docker 
How to run and install the docker can be found in 

https://github.com/chrismanp/pldi24_artifact

It contains command on how to run the script as well. 

11. Known issues

If clang segfaults, rebuild clang by:
cd /afs/ece.cmu.edu/project/seth_group/uli-opencilk-project/build
ninja clean
ninja -j<number of processors>

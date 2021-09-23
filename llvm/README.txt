
Setup Instructions


For the following commands, replace <andrew_id> with your andrew id


1. Log in

Log into ECE machines
cd /afs/ece.cmu.edu/project/seth_group/

If you don’t have a personal directory:
mkdir <andrew_id>



2. Download and build gcc 5.5

Download gcc 5.5. You can download gcc-5.5.0.tar.gz from https://ftp.gnu.org/gnu/gcc/gcc-5.5.0/
Move the file into /afs/ece.cmu.edu/project/seth_group/<andrew_id>

tar -xvf gcc-5.5.0.tar.gz

cd gcc-5.5.0
./contrib/download_prerequisites
cd ..
mkdir gcc-build
cd gcc-build
./../gcc-5.5.0/configure --prefix=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-5.5.0 --enable-languages=c,c++,fortran,go
make (this can take a few hours)
make install
cd ..



3. Clone uli-llvm

git clone --recursive https://github.com/user-level-interrupts/uli-llvm

cd uli-llvm

If you don’t see clang in uli-llvm/tools or clang is empty, link uli-clang to uli-llvm/tools/clang:
    At /afs/ece.cmu.edu/project/seth_group/<andrew_id>
    cd uli-llvm/tools
    rm -r clang (if clang is present)
    ln -s ../../uli-clang clang

Do not do this for compiler-rt and openmp which may be in uli-llvm/projects



4. Compile the compiler

Make sure your home directory is in the ECE space

Add the following to ~/.bashrc, replacing <andrew_id> with your andrew id:

export LD_LIBRARY_PATH=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-5.5.0/lib64:$LD_LIBRARY_PATH
export PATH=/afs/ece.cmu.edu/usr/seth/opt/ninja/bin:/afs/ece.cmu.edu/usr/seth/opt/binutils.gold/bin:/afs/ece.cmu.edu/usr/seth/opt/cmake/bin:$PATH
export PATH=$PATH:/afs/ece.cmu.edu/usr/cpakha/Public/rr_d/usr/bin/
export PATH=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-5.5.0/bin:$PATH
export LD_BIND_NOW=1

Then:
source ~/.bashrc

cd /afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-5.5.0/bin
mv gcc gcc-5.5
mv g++ g++-5.5

In uli-llvm:
mkdir build
cd build

cmake -G Ninja ../ -DCMAKE_C_COMPILER=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-5.5.0/bin/gcc-5.5 -DCMAKE_CXX_COMPILER=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/GCC-5.5.0/bin/g++-5.5 -DCMAKE_INSTALL_PREFIX=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/uli-llvm/build -DLLVM_USE_SPLIT_DWARF=TRUE -DLLVM_ENABLE_ASSERTIONS=TRUE -DCMAKE_BUILD_TYPE=Debug -DCMAKE_SHARED_LINKER_FLAGS="-B$ldpath -Wl,--gdb-index" -DCMAKE_EXE_LINKER_FLAGS="-B$ldpath -Wl,--gdb-index" -DLLDB_TEST_COMPILER=g++-5.5 -DBUILD_SHARED_LIBS=true -DLLVM_TARGETS_TO_BUILD=X86 -DLLVM_BINUTILS_INCDIR=/afs/ece.cmu.edu/usr/seth/opt/binutils.gold/include 2>&1 | tee cmake.out.log

Add the following to ~/.bashrc

export PATH=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/uli-llvm/build/bin:$PATH
export LD_LIBRARY_PATH=/afs/ece.cmu.edu/project/seth_group/<andrew_id>/uli-llvm/build/lib:$LD_LIBRARY_PATH

Then:
source ~/.bashrc

In uli-llvm/build:

lscpu (this tells you the number of processors)
ninja -j<number of processors>
cd ../..



5. Compile fib.clone.bin

At /afs/ece.cmu.edu/project/seth_group/<andrew_id>:

git clone https://github.com/user-level-interrupts/uli.git
cd uli

cd cas_ws/cilk5
mkdir serial_result
mkdir clone_result
cd passes
mkdir build
make
If LiveVariable.so is in the current directory: mv LiveVariable.so build
cd ..
make fib.clone.bin

If this segfaults:
    cd /afs/ece.cmu.edu/project/seth_group/uli-llvm/build
    ninja clean
    ninja -j<number of processors>
    cd /afs/ece.cmu.edu/project/seth_group/<andrew_id>/uli/cas_ws/cilk5/passes
    make
    cd ..
    make fib.clone.bin

Try to run the generated binary:

CILK_NWORKERS=1 ./fib.clone.bin 42
CILK_NWORKERS=14 ./fib.clone.bin 42
CILK_NWORKERS=<number of processors> ./fib.clone.bin 42


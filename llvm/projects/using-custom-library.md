Using LLVM project for implicit seed
- git clone https://github.com/llvm/llvm-project
- We need the following library in our folder libcxx  libcxxabi	libunwind for implicit seed. The rest can be ignored (place in another folder)
- Recompile the llvm as usual (might need to remade the Cmake then call ninja)

- Example of compiling the program :
../../../uli-llvm/build/bin/clang++ -o test_uli-fsim -Xclang -fenable-uli-transform -DULIFSIM -Xclang -fenable-uli-rewrite -rdynamic  -ggdb -O0 -Wall -fno-omit-frame-pointer -I../lib -L../lib test_uli.cpp -lsuli -lflazy -lpthread  -lc++abi -lunwind

- To run the program
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:../compiler/build/lib ./test_uli-fsim

#!/usr/bin/env bash
mkdir -p build
cd build
if [ ! -f build.ninja ]; then
    cmake -G Ninja .. \
    -DLLVM_USE_SPLIT_DWARF=TRUE \
    -DLLVM_ENABLE_ASSERTIONS=TRUE \
    -DCMAKE_BUILD_TYPE=Debug \
    -DCMAKE_INSTALL_PREFIX="$HOME/opt/clang-uli" \
    -DCMAKE_SHARED_LINKER_FLAGS="-Wl,--gdb-index,-fuse-ld=gold" \
    -DCMAKE_EXE_LINKER_FLAGS="-Wl,--gdb-index,-fuse-ld=gold" \
    -DCMAKE_EXE_LINKER_FLAGS="-Wl,--gdb-index,-fuse-ld=gold" \
    -DBUILD_SHARED_LIBS=true \
    -DLLVM_TARGETS_TO_BUILD=X86 \
    -DLLVM_CCACHE_BUILD=true \
    2>&1 | tee cmake.log
fi
timeout 2400 ninja
if [ $? -eq 142 ]; then
    sleep 10
    echo "Build took more than 40 minutes"
    echo "Exiting with success so that cache is saved"
    echo "Rerun build to continue with cached progress"
    exit 0
fi

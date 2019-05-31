# Use the build dir to compile the compiler.

See `../../../../scripts/compile-docker.sh` which will create a container and then launch it ready to compile the compiler with `compile-docker.sh`.

# use the release dir to install the newly compiled compiler into a container

See `../../../../scripts/make-clang-container.sh` which will create a container that can then be used to compile programs, using `runcompiler.sh`

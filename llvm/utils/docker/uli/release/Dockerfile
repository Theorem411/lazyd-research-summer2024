# build the compiler container
FROM seth5744/ulicompbase:latest

LABEL maintainer "ULI group"

# Unpack clang installation into this image.
ADD clang.tar.gz /usr/local/

WORKDIR /home/userincontainer
CMD ["/bin/bash"]

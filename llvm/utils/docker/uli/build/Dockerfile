# Ubuntu Linux as the base image
FROM ubuntu:16.04

# Install packages
RUN apt-get -y update && apt-get -y install git emacs gcc python g++ ccache make texinfo bison flex python3 cmake
# make ld.gold default
run cd /usr/bin && /bin/rm ld && ln -s x86_64-linux-gnu-ld.gold ld
# make sure we use ccache for the future
run echo "export PATH=/usr/lib/ccache:\$PATH" >> ~/.bashrc
# build and install ninja
ADD makeninja.sh /tmp
run cd /tmp && bash ./makeninja.sh

CMD ["bin/bash"]

#!/bin/bash

git clone git://github.com/ninja-build/ninja.git
cd ninja
git checkout release
./configure.py --bootstrap
cp ninja /usr/local/bin

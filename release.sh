#! /bin/zsh
mkdir -p release/build
pushd release/build
cmake ../../src
make
popd
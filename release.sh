#! /bin/zsh
mkdir -p build/release
pushd build/release
cmake ../../src
make
popd
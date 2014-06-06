#!/bin/bash
if [ $# -ne 2 ]; then
    echo "Usage: test.sh [python-interp-path] [file]"
    exit 1
fi
PYTHON=$1
f=$2
echo "-- testing $f"
$PYTHON $f > $f.produced.out 2>&1
RESULT=$?

# Check Memory Leak and return 1
if grep "swig/python detected a memory leak of type" $f.produced.out; then
    echo "-- memory leak detected"
    exit 1
fi

if [ $RESULT = 0 ]; then
    echo "-- worked"
    exit 0
else
    echo "ERROR executing $f, produced output:"
    cat $f.produced.out
    exit 1
fi

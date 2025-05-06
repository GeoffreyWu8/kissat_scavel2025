#!/bin/sh
./configure --competition --test
make all || exit 1
kissat || exit 1
exec install -s kissat ./bin/

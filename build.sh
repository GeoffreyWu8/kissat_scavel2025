#!/bin/sh
chmod +x ./configure
chmod +x ./scripts/*
./configure --competition --test
make all || exit 1
exec install -s ./build/kissat ./bin/

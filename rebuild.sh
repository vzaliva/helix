#!/bin/sh
set -e
git pull
(cd lib/vellvm; git pull --recurse-submodules)
make -C lib/vellvm/src clean
make -j4 -C lib/vellvm/src
make -C lib/vellvm/src test
make distclean
make -j4

#!/bin/sh
set -e
git pull
(cd lib/vellvm; git pull --recurse-submodules)
make -C lib/vellvm/src clean
# Fix for `clean` target in vellvm does not clean everything
rm -f `find lib/vellvm/ -name \*.vo`
make -j4 -C lib/vellvm/src
make -C lib/vellvm/src test
make distclean
make -j4
make test

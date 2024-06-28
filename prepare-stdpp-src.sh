#!/bin/sh

# Rename the logical library name so that we can have both BBV and stdpp
# versions of the library installed by opam at once.

set -e

mkdir src-stdpp
sed 's/PACKAGE_NAME=Sail/PACKAGE_NAME=SailStdpp/' src/Makefile > src-stdpp/Makefile
for f in src/*.v; do sed -e 's/Sail\(\.[^ ]\)/SailStdpp\1/g' -e 's/port Sail\./port SailStdpp./' -e 's/From Sail /From SailStdpp /' $f > src-stdpp/`basename $f`; done
ln -snf MachineWordStdpp.v src-stdpp/MachineWord.v
ln -snf InstancesStdpp.v src-stdpp/Instances.v

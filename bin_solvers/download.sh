#!/bin/bash

# The following is for pysmt
# install mathsat5
pysmt-install --msat --confirm-agreement
# install yices2, it takes a long time, comment it if necessary
pysmt-install --yices --confirm-agreement
# install cvc5, it takes a long time, comment it if necessary
pysmt-install --cvc5 --confirm-agreement
# install boolector, it takes a long time, comment it if necessary
pysmt-install --btor --confirm-agreement

# The following is for linux-binary
z3="https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-x64-glibc-2.31.zip"
mathsat5="https://mathsat.fbk.eu/download.php?file=mathsat-5.6.9-linux-x86_64.tar.gz"
yices2="https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-x86_64-pc-linux-gnu.tar.gz"
cvc5="https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-Linux"

targets=($z3 $mathsat5 $yices2 $cvc5)

for url in "${targets[@]}"; do
    cmd="wget $url"
    $cmd
    echo "Finish downloading $url"
done

# extract all zip/gz files
eval "find . -maxdepth 1 -type f -name '*.gz' | xargs -I{} tar xvf {}"
eval "find . -maxdepth 1 -type f -name '*.zip' | xargs -I{} unzip {}"

pwd
current_dir=$(pwd)

# Download and build Boolector
git clone https://github.com/Boolector/boolector.git
cd boolector
git checkout 43dae91c1070e5e2633e036ebd75ffb13fe261e1

# Download and build Lingeling
./contrib/setup-lingeling.sh

# Download and build BTOR2Tools
./contrib/setup-btor2tools.sh

# Build Boolector
./configure.sh && cd build && make

eval "cd $current_dir"

# Download and build Bitwuzla
git clone https://github.com/bitwuzla/bitwuzla.git
cd bitwuzla
git checkout 0e9f1c26444880463336ff97665b7382006edf10

# Build Bitwuzla
./configure.py
cd build && meson compile

eval "cd $current_dir"

# for installation of q3b
z3_version=z3-4.10.2-x64-glibc-2.31
eval "cp $z3_version/bin/libz3.a /usr/lib"
eval "cp $z3_version/include/* /usr/include/"

git clone https://github.com/martinjonas/Q3B.git
cd Q3B
git checkout 717377fd82e40fde4f33b65ac4b1a374bc45bac4
git submodule update --init --recursive # may fail!!!
cmake -B build -DANTLR_EXECUTABLE=/usr/share/java/antlr-4.11.1-complete.jar
cmake --build build -j4

eval "cd $current_dir"

mkdir bin
smt_binaries=("z3" "mathsat" "yices-smt2" "cvc5-Linux" "boolector" "bitwuzla" "q3b")
match=""
flag=false
for binary in "${smt_binaries[@]}"
do
  if $flag; then
    match+=" -o -name '$binary'"
  else
    match+=" -name '$binary'"
    flag=true
  fi

done

# find smt binaries and cp these files to ./bin
eval "find . -type f \\( $match \\) | xargs -I{} cp {} ./bin/"
eval "find . -maxdepth 1 -type f -name '*.gz' | xargs -I{} rm -f {}"
eval "find . -maxdepth 1 -type f -name '*.zip' | xargs -I{} rm -f {}"
eval "chmod +x ./bin/cvc5-Linux"
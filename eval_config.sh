#!/bin/bash

# set -euo pipefail  # Exit on error, undefined var, pipe failure


engines=("iter" "maxsat" "qsmt")
iter_solvers=("z3" "cvc5" "yices" "msat" "btor")
iter_methods=("ls" "bs")
maxsat_solvers=("FM" "RC2" "OBV-BS")
qsmt_solvers=("z3" "cvc5" "yices" "msat" "bitwuzla" "q3b")

configs=()

for i in "${iter_solvers[@]}"; do
    for j in "${iter_methods[@]}"; do
        configs+=("${engines[0]} ${i}-${j}")
    done
done

for m in "${maxsat_solvers[@]}"; do
    configs+=("${engines[1]} ${m}")
done

for q in "${qsmt_solvers[@]}"; do
    configs+=("${engines[2]} ${q}")
done

printf "%s\n" "${configs[@]}" > eval_config
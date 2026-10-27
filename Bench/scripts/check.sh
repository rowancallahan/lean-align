#!/bin/sh
# Final check: rebuild everything from scratch, rerun the developer checks, then replay the proof
# through the external kernels.   sh Bench/scripts/check.sh
# For quick iteration use Bench/scripts/CI_check.sh (cached build) instead.
set -u
cd "$(dirname "$0")/../.." || exit 1
rm -rf .lake/build
sh Bench/scripts/CI_check.sh || exit 1
sh Bench/scripts/external_checkers.sh full

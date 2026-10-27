#!/bin/sh
# Final check: rebuild everything from scratch, rerun the developer checks, then replay the proof
# through the external kernels.   sh scripts/check.sh
# For quick iteration use scripts/CI_check.sh (cached build) instead.
set -u
cd "$(dirname "$0")/.." || exit 1
rm -rf .lake/build
sh scripts/CI_check.sh || exit 1
sh scripts/external_checkers.sh full

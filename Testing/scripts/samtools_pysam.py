#!/usr/bin/env python3
# `samtools CMD ARGS...` through pysam (pip install pysam), for boxes without a samtools binary.
import sys, pysam
out = getattr(pysam.samtools, sys.argv[1])(*sys.argv[2:], catch_stdout=True)
sys.stdout.write(out if isinstance(out, str) else "")

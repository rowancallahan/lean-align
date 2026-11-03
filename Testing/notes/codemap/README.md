Tools used for the exp/codemap cleanup (see ../CODEMAP.md §7, §10). Not built by lake; paths inside point at a scratch
directory (/tmp/claude-0/codemap/), edit them before reuse.
- Reach.lean: constant-level reachability over the elaborated environment (`lake env lean --run Reach.lean`, reads mods.txt and
  citoks.txt, writes all_decls.txt with LIVE/DEAD and source ranges). Roots: Main, Proofs.*, names in CI-run files, WFA modules;
  follows types, values and @[csimp] targets.
- prune3.py AREA...: deletes DEAD declarations in AREA (never WFA, ReadWindowTrimmer, instances, structures), builds, and on
  each error keeps the deleted names the failing declaration mentions; repeats until the build is clean.
- size.py: lines, chars and the token proxy (CODEMAP §7).

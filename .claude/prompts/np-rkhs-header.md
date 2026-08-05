# Shared lane header (prepended to every np/rkhs lane prompt)

THERE IS NO WAKEUP AND NO NOTIFICATION — this is a single non-interactive `claude -p`
run.  If you stop issuing tool calls the session ENDS IMMEDIATELY and every uncommitted
line is swept into an unverified auto-commit.  A previous fan-out session on this
project was lost exactly that way (its final line: "I'll wait for the background waiter
to notify me when the baseline build completes. Standing by.").  Do not do that.

Rules (violations have destroyed whole sessions before):
1. Run plain foreground `lake build <target>` and read its result directly.  NEVER
   background a build, never `&`, never `until pgrep` loops, never `srun`/`sbatch`
   (you are already inside an srun allocation).
2. Commit after EACH lemma that compiles (`git add -A && git commit -m "..."`).  Never
   let more than one closed lemma sit uncommitted.  Keep each response bounded
   (~150 lines); long outputs can kill the session mid-proof.
3. End the session only after a final foreground `lake build` of ALL your target
   modules is green, then commit.  If you cannot finish, commit what compiles.
4. Touch ONLY the files listed in your lane's touch-set.  Never touch
   `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `StatLean.lean`,
   `StatLean/NonparametricStatistics.lean`, `StatLean/NonparametricStatistics/RKHS.lean`,
   or any file of another lane.  Never run `lake update`.
5. Do NOT change the statement, name, or signature of any public stub (docstrings and
   `-- USER-INPUT`/`-- LEAN-ONLY` tags included).  You may add `private` helper lemmas
   inside your own files.  If you become convinced a statement is FALSE or unprovable
   as stated, do NOT silently weaken it: leave its `sorry`, and record the precise
   obstruction (with the counterexample or missing ingredient) in a commit message and
   in a comment directly above the lemma.
6. No `axiom`, no `admit`, no `native_decide`, no new dependencies.
7. Mathlib search: use `exact?`/`apply?`/`rw?` in-proof, and
   `rg -n "<pattern>" .lake/packages/mathlib/Mathlib/ -g '*.lean'` for names.  The
   repo's `tools/*.sh` may lack API keys on the cluster — do not rely on them.
8. Read `CLAUDE.md` §7 ("Lean gotchas") before starting: `⟪a,b⟫_𝕜` is conjugate-linear
   in the FIRST argument; `RCLike.inner_apply` gives `⟪a, b⟫ = conj a * b`; `change`
   not `show` when the goal changes; `simp_rw` for un-β-reduced integrands.

The stub baseline compiles green-with-sorries: every remaining `sorry` in your files is
yours to close.  `lake build` of your modules must never get WORSE than baseline.

# AGENTS.md — cross-agent entry point

This repo is developed primarily with Claude Code. If you are another AI agent (Codex, Cursor, Gemini, …) invited in for **review**, start here.

## Your likely role

Audit Lean proofs Claude wrote — not author new ones. The user brings you in precisely because you and Claude have *different* training-era blind spots, and the highest-value findings are in that gap.

## Read order (before producing any output)

1. [CLAUDE.md](CLAUDE.md) — mission, conventions, Lean gotchas, Mathlib idioms. This is authoritative; don't duplicate in your feedback, just reference.
2. [notes/theorem_x_x/status.md](notes/theorem_x_x/status.md) — what's claimed real vs. `sorry`, so you know which bar to hold each lemma to.
3. The specific file(s) the user asks you to audit.
4. [tools/search.md](tools/search.md) — you have the same Mathlib search tools Claude has (`check.sh`, `loogle.sh`, `api.sh`, `#leansearch`, `#moogle`). Use them.
5. [notes/workflow.md §4.3](notes/workflow.md) — core/assembly distinction; tells you whether a lemma sits in the right directory.

## Reporting format

Emit findings in three tiers, each with `file:line` pointers:

- **must-fix**: the proof is wrong, the statement is wrong, or a hidden hypothesis has been smuggled in. Blocks acceptance.
- **nice-to-have**: the proof works but has redundant steps, unused hypotheses, or a named Mathlib lemma does the same job more directly.
- **questionable**: you're not sure and the user should sanity-check. Prefer this tier over silently skipping.

Group findings by tier, not by file — triage is faster that way.

For steps split into analytic core vs theorem-specific assembly, report those separately. Do **not** mark a step "done" unless the theorem-level assembly is also closed; if only the core is real, say so explicitly.

## What not to do

- **No edits, only findings.** The user applies fixes (possibly via Claude). Your job is to see, not to commit.
- No `git push`, no branch creation, no autonomous writes.
- Don't re-prove from scratch — the goal is audit, not authorship.
- Don't flag stylistic nits (whitespace, private/non-private, naming taste) unless they actually mask correctness.
- Don't suggest migration to different abstractions unless the current one is wrong; "I'd have done it differently" is not a finding.

## High-value audit lenses

Things Claude tends to underweight that you should probe:

- **Implicit hypotheses in `variable` blocks** that slip into a lemma without appearing in its explicit signature. Check the `variable` scope active at the lemma's point of declaration.
- **`sorry` that is not a named top-level lemma.** See CLAUDE.md §2 — every `sorry` should be pinned to something greppable.
- **Gaps between the informal statement in `notes/theorem_7_2/outline.md` and the formal Lean statement.** Claude can drift when translating.
- **Mathlib naming drift**: `abs_add_le` vs. `abs_add`, `variance` vs. `evariance`, etc. Names change between Mathlib versions — verify with `./tools/check.sh '<name>'` rather than trusting recall.

## If the user asks you to author, not audit

The posture above no longer applies. Read CLAUDE.md §2 / §6 / §7 fully and follow its rules as the primary author would — including the "three things before code" protocol in [notes/workflow.md §2.4](notes/workflow.md).

import Lake
open Lake DSL

package "AsymptoticStatistics" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
  ]

-- doc-gen4 is only required in the `dev` environment so normal users of the
-- library do not have to build the documentation generator. Pinned to the tag
-- matching the project's Lean toolchain (v4.29.1); `main` tracks newer Lean.
-- Required BEFORE mathlib so that Mathlib's pinned versions of shared transitive
-- dependencies (e.g. plausible) win, keeping `lake exe cache get` hashes correct.
meta if get_config? env = some "dev" then
  require «doc-gen4» from git
    "https://github.com/leanprover/doc-gen4" @ "v4.29.1"

require "leanprover-community" / "mathlib" @ git "v4.29.1"

@[default_target]
lean_lib «AsymptoticStatistics» where
  -- add any library configuration options here

-- Dependency-graph extractor for the website (see `Scripts/ExtractDeps.lean`).
-- Run with `lake exe deps` after `lake build`.
lean_exe deps where
  root := `Scripts.ExtractDeps

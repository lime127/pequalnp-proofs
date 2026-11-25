# Verified Lean results by lime127

These are checked partial and derived results from the P vs NP project work. They are published as research artifacts on lime127's fork. They are not claims that P vs NP, or all four proposed conjectures, have been proved. Publishing them here does not imply acceptance or credit by pequalnp.com.

## Results

| File | What it proves | Scope and attribution |
| --- | --- | --- |
| [Mask4974Upper.lean](Mask4974Upper.lean) | `Lime127.Research.Mask4974.upper`: the 4-by-4 table encoded by mask 4974 has representation size at most 9. | An explicit nine-gate AND/OR circuit, checked on the 16 inputs selecting exactly one row and one column. Behavior on other inputs is not specified. This does not prove that eight gates are impossible. |
| [NoSmallCoverCounterexample.lean](NoSmallCoverCounterexample.lean) | `Lime127.Research.noSmallCoverCounterexample`: the counterexample requested by the saved L-meta-2400 statement cannot exist. | A derived application of the existing upstream theorem `PEqualNP.Outside.L_meta_217`, imported explicitly. It is not a new independent proof of that upstream lower bound. Its import was not allowed for the original task submission. |

The earlier reduction is already public in [PR #11349](https://github.com/open-goat/pequalnp-proofs/pull/11349), at commit `b0d1a37e68461c7a3093f62609aac4e31765270e`, file `lean/PEqualNP/Outside/R_meta_2071_587.lean`. It splits the original claim into two hypotheses; it does not prove those hypotheses. The full local CheckLemma verifier accepted the reduction. This is distinct from an official project verdict.

## Reproduce the checks

Base repository revision: `cc5bff61fdb650a4ecd82694aeffa0f790a01a60`.
Lean toolchain: `leanprover/lean4:v4.36.0`, as pinned in `lean/lean-toolchain`.
Use the repository's pinned Lake manifest and dependencies.

From a full checkout of this branch, with the pinned Lean toolchain installed:

```sh
cd lean
lake exe cache get
lake build PEqualNP.Defs PEqualNP.Outside.L_meta_217
lake env lean ../research/lime127/Mask4974Upper.lean
lake env lean ../research/lime127/NoSmallCoverCounterexample.lean
```

`verification.txt` records fresh local checks and the axioms reported by Lean. Neither proof uses `sorry`, a new axiom, or `native_decide`. Namespace changes distinguish these research artifacts from official task modules.

## Still unfinished

The eight-gate impossibility result for mask 4974 has computational UNSAT evidence and an external certificate replay, but no completed Lean proof. The certificate is larger than the project's submission limit. The other proposed conjectures are not proved. The uncompiled inline helper bundle and unfinished searches are not presented as verified Lean results here.

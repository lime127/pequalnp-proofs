# Verified Lean results by lime127

These are checked partial and derived results from the P vs NP project work. They are published as research artifacts on lime127's fork. They are not claims that P vs NP, or all four proposed conjectures, have been proved. Publishing them here does not imply acceptance or credit by pequalnp.com.

## Results

| File | What it proves | Scope and attribution |
| --- | --- | --- |
| [LineSingleBridge.lean](../../lean/PEqualNP/Research/LineSingleBridge.lean) | `PEqualNP.Research.LineSingleBridge`: the exact first child of reduction `R_meta_2071_587`. | A complete generic bridge from the project linear-parts evaluator to the specified derivative recurrence. Adapted from the generic trace argument in upstream `R_meta_2071_926`; no structural plane assumption is used. |
| [Mask4974Upper.lean](Mask4974Upper.lean) | `Lime127.Research.Mask4974.upper`: the 4-by-4 table encoded by mask 4974 has representation size at most 9. | An explicit nine-gate AND/OR circuit, checked on the 16 inputs selecting exactly one row and one column. Behavior on other inputs is not specified. This does not prove that eight gates are impossible. |
| [NoSmallCoverCounterexample.lean](NoSmallCoverCounterexample.lean) | `Lime127.Research.noSmallCoverCounterexample`: the counterexample requested by the saved L-meta-2400 statement cannot exist. | A derived application of the existing upstream theorem `PEqualNP.Outside.L_meta_217`, imported explicitly. It is not a new independent proof of that upstream lower bound. Its import was not allowed for the original task submission. |

The earlier reduction is already public in [PR #11349](https://github.com/open-goat/pequalnp-proofs/pull/11349), at commit `b0d1a37e68461c7a3093f62609aac4e31765270e`, file `lean/PEqualNP/Outside/R_meta_2071_587.lean`. It splits the original claim into two hypotheses; it does not prove those hypotheses. The full local CheckLemma verifier accepted the reduction. The official authoritative workflow also accepted it on 2026-11-25 at 04:04 UTC, but the PR remains unmerged as of the latest check. Acceptance of the reduction does not prove either child.

## Reproduce the checks

Base repository revision: `cc5bff61fdb650a4ecd82694aeffa0f790a01a60`.
Lean toolchain: `leanprover/lean4:v4.36.0`, as pinned in `lean/lean-toolchain`.
Use the repository's pinned Lake manifest and dependencies.

From a full checkout of this branch, with the pinned Lean toolchain installed:

```sh
cd lean
lake exe cache get
lake build PEqualNP.Defs PEqualNP.Outside.L_meta_217 PEqualNP.Research.LineSingleBridge
lake env lean ../research/lime127/Mask4974Upper.lean
lake env lean ../research/lime127/NoSmallCoverCounterexample.lean
```

`verification.txt` records fresh local checks and the axioms reported by Lean. None of these proofs uses `sorry`, a new axiom, or `native_decide`. Namespace changes distinguish these research artifacts from official task modules.

## Still unfinished

The eight-gate impossibility result for mask 4974 has computational UNSAT evidence and an external certificate replay, but no completed Lean proof. The certificate is larger than the project's submission limit. The other proposed conjectures are not proved. The uncompiled inline helper bundle and unfinished searches are not presented as verified Lean results here.
## First reduction child: complete proof

The exact child statement is preserved in [LineSingleBridge.statement.lean](LineSingleBridge.statement.lean). The proof uses only `PEqualNP.Defs`. It establishes agreement between the evaluator and an arbitrary derivative recurrence at every existing wire, then handles an output outside the wire range by showing its lineSingle value cannot be true. This proves CHILD 1 exactly; it does not assume CHILD 2. The unchanged project kernel verifier accepted the final source, rechecking 1,675 constants against the exact statement with only propext, Quot.sound, and Classical.choice. See [the local verification record](LineSingleBridge-verification.txt). This is not an official site verdict.

Attribution: the generic fold, wire-evaluation, and `lineSingle_eq_trace` arguments are adapted from [upstream R_meta_2071_926 at the pinned revision](https://github.com/open-goat/pequalnp-proofs/blob/cc5bff61fdb650a4ecd82694aeffa0f790a01a60/lean/PEqualNP/Outside/R_meta_2071_926.lean). The adaptation extracts those arguments into a standalone theorem, converts the original Fin-valued singleton inputs, and proves the missing output-bound case. The repository Apache-2.0 license applies. This is an extracted/derived proof, not a claim of a new circuit lower-bound discovery.

For the exact-statement kernel replay, after building the module and `checklemma`:

```sh
cd lean
lake build PEqualNP.Research.LineSingleBridge checklemma
lake env .lake/build/bin/checklemma PEqualNP.Research.LineSingleBridge ../research/lime127/LineSingleBridge.statement.lean check
```

On Windows the verifier executable is `checklemma.exe`.

## Remaining acceptance and mathematical obstacles

The public desk snapshot checked on 2026-11-25 listed three registered reductions of L-meta-2071: `_1`, `_319`, and `_926`. It did not list `_587` or either of its exact child statements. Our reduction PR remains open. Thus the first child's completed proof has no assigned official child-task ID to submit against at this time. The full allocation of reduction slots may explain this, but the project has not confirmed that reason.

CHILD 2 is not proved. It asserts single-read coverage of every incidence for a correct order-3 projective-plane circuit of at most 64 gates, even in the presence of nested and dirty AND gates. Existing results covering no nesting or all-clean AND gates do not establish this case. Finishing the evaluator bridge does not establish the structural gate-count bound. These unresolved facts prevent claiming that the original reduction is closed or that profile credit has been earned.

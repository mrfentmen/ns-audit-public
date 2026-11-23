# ns-audit

An independent, plain-language audit of [`openai/NavierStokesAndEuler`](https://github.com/openai/NavierStokesAndEuler) at commit `f9e8bc5` — a 641,332-line Lean 4 development that machine-checks a theorem about the 3D incompressible Navier–Stokes equations.

Everything here is commentary. No upstream code is vendored.

## The short version

The repo proves: for every viscosity ν > 0 there exists a smooth, compactly supported force and a zero initial velocity such that a smooth divergence-free solution exists on `ℝ³ × [0,1)` with bounded kinetic energy yet unbounded speed at `t = 1`, and **no** global finite-energy solution exists for that same force. That matches alternative **(C)** of the Clay statement, and is silent on the unforced alternatives (A) and (B).

The audit's two findings:

1. **The Non-Evaluated Constant Barrier.** A proof assistant checks arithmetic that reaches the *types*. Exponent indices and differentiability orders are types, so they are decided by unification — get one wrong and it will not compile. Multiplicative constants inside `∃ C, ∀ x, ‖Tx‖ ≤ C‖Sx‖` are terms, and are checked only for inhabitation. Every quantitative constant in the chain is introduced by an existential binder or by `Classical.choose`. The kernel verifies that *some* constant exists; it never verifies the size or the dimension. This is epistemic, not logical: the headline theorem mentions no constant, so no assignment can make it false — but no effective bound, no machine dimension check, and no "small enough for the next step" claim survives.
2. **Anisotropic Viscous Scaling under the generalized cone.** The repo's own pullback identities give `∂ₛ²` weight `q^{b-2}` but `∂𝓏²` weight `q^{b-2D(h)}` with `D(h) = ½ − h`. Since `2D(h) ∈ (0,1)` on the admissible range `0 < h < ½`, the Laplacian is a sum of two homogeneous pieces of degrees `b−1` and `b−2D(h)`, differing by exactly `2h`. No admissible member of the family is isotropic. The code is correct; it is the isotropic *reading* that is incompatible with it.

## What is in here

| File | What it is |
|---|---|
| `MANUSCRIPT.tex` | The audit paper. LuaLaTeX or XeLaTeX. |
| `MANUSCRIPT.pdf` | The typeset paper: 25 pages, LuaLaTeX, built by `typeset.yml` (E78). |
| `AUDIT_LOG.md` | The working log: entries E0–E87, every `path:line` citation behind the paper. |
| `PHASE2-FINDINGS.md` | Second-pass findings: the anisotropic weights, the three "free doors", the packets. |
| `CAVEMAN.md` | The whole thing rewritten in caveman. Every finding, plus §13–15: the equation symbol by symbol, why 3D is the hard case, and the four Clay doors A–D. |
| `CAVEMAN_1TO1.md` | The paper section for section in caveman: 8 sections, every subsection, appendix and bibliography. Nothing skipped. |
| `LAYMAN.md` | The paper in plain English: same structure, no symbol left unexplained. For a reader who is not a mathematician. |
| `BUZZWORDS.md` | Every invented label the paper uses (§A–G) and every real technical term it assumes you know (§H), each defined. |
| `cone_weights.svg` | The diagram: the generalized cone and the two viscous weights, with the `2h` gap. |
| `equation_terms.svg` | The four terms of the equation, one panel each: clock, advection, viscosity, pressure. |
| `clay_doors.svg` | The four Clay alternatives as a decision tree: arena × hand → A, B, C, D, with EVERY versus ONE and each door's status. |

## The three-sentence summary

The artifact is logically clean — no reachable `sorry`, no `axiom`, no `native_decide`, no `unsafe`, no `implemented_by`, and the force's global smoothness is *proved*, not assumed (trace in E65 and E66). But the kernel answers only "does this term inhabit this type", so constants and real exponents — which live in terms, not types — are never weighed or dimensioned. Separately, the repo's own derivative identities show the viscous term is two pieces with weights differing by `2h`, so no admissible member is isotropic, while the whole scale regime sits behind a single `Classical.choice`.

## What this audit did and did not establish

- **Findings are source-read.** Every finding comes from reading proof terms, binder order, and definitions. The build below did not machine-check the findings themselves.
- **Kernel acceptance was reproduced**, on Linux: `lake build NavierStokes` completed 9,580 jobs with exit 0 (817 modules, 20 min 17 s), and `#print axioms` on the four R3 theorems reports only `propext`, `Classical.choice`, `Quot.sound`. The pinned toolchain's `lake` aborts with `SIGTRAP` in `libmalloc` on current macOS (3/3), so the build first ran in an Ubuntu VM; it was then repeated from a pristine clone on a GitHub Actions runner (9,580 jobs, 28 min 35 s, E73).
- **Periodic alternative (D) was audited by reading** (E70): the corollary follows from the whole-space theorem by parabolic compression and periodization, its competitor class imposes no energy bound at all, and it is bridged to the comparator in both directions. Its axiom footprint, once inferred from the whole-space run (E70, E72), has since been **printed** on the same 817-module build: `navier_stokes_breakdown_periodic`, `periodic_corollary` and both comparator adapters depend only on `propext`, `Classical.choice`, `Quot.sound` — the exact set `ComparatorChallenges/NavierStokes.json` permits — with no `sorryAx` (E73). That closes the empirical item E70 left open. The external Comparator check has since **run and passed**: on run `45119134981` Comparator built the challenge and the solution inside the landrun sandbox, exported both against the same 32-name target list — which includes both `navier_stokes_breakdown_R3` and `navier_stokes_breakdown_periodic` — replayed the solution in a fresh builtin kernel, and printed `Lean default kernel accepts the solution` followed by `Your solution is okay!` (E75). The second kernel agreed: `nanoda kernel accepts the solution`, from a Rust implementation that shares none of Lean's kernel (E75 §7). So the solution proves the statement the challenge poses, and two kernels replayed it. Two earlier attempts had produced no verdict at all, and the reason was not the mathematics: a `systemd-run --pty` wrapper left the child blocked on an undrained PTY buffer, so 565 minutes across two runs yielded two lines of systemd chatter. With `--pipe` the same work takes 7.3 minutes (E74, E75).
- **The estimate chain is closed by reading** (E68, E69, E71): the source wave class that the stage estimates consume is proved for the initial state, rebuilt by every step, and the assembly that rebuilds it is a structure literal with no assumed field.
- **The encoded statement is checked against Fefferman's text clause by clause** (E76): every numbered condition of alternatives (C) and (D) — (1)–(11), including the errata's pressure-periodicity clause — maps to a named Lean field, and none is missing, weakened or strengthened. The two remaining conventions are named rather than hidden: `C^∞` on the closed half-space read as `ContDiffOn`, and multi-index bounds carried as iterated operator norms.
- **One alternate branch is unused** (E77): `WaveInputs` and the two endpoint definitions that supply it have no callers; the assembly goes through `actualStageEstimates` instead.
- **The Euler challenge was executed, and passes** (E79): the `Euler` library builds from a clean clone (10,603 jobs, 50 min 11 s), and Comparator accepts both `euler_breakdown_R3` and `exists_compact_smooth_euler_singularity` on two kernels — `Lean default kernel accepts the solution`, `nanoda kernel accepts the solution`, `Your solution is okay!` — with an axiom footprint of only `propext`, `Classical.choice`, `Quot.sound`, and no `sorryAx`. That checks the proofs against the statements, and E80 checks the statements: they are the two declarations `formalization.yaml:72–94` designates as the repository's Euler formalizations, both in `Euler/Solution.lean`, and the challenge's solution class is *proved* equivalent to the development's (`exists_sobolevSolution_iff`, both directions), with the rapid-decay and norm clauses bridged the same way. E81 then reads the Euler paper's Theorem 1.1 against the encoding: it is stronger than the paper in five respects and **weaker in two** — first, the challenge's `limsup velocityC1Norm = ⊤` adds the velocity supremum to the gradient's, while the paper asserts `limsup ‖∇u‖∞ = ∞` alone, and a sum can diverge while a summand does not; second, `Tstar` is defined over the development's Sobolev class, which is not proved to contain the paper's jointly smooth solution (E82). The development proves the paper's gradient-only statement (`maximalGradientNorm_limsup`, `EulerC1Limsup.lean:54`), and a runner has now printed its axiom footprint — `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx` (E84). But it is not in the challenge's target list, so it is not part of the statement Comparator accepted. Not one estimate inside the Euler development was read.
- **Did not re-run eight of the nine external checkers** the repository reports. The ninth, Comparator, now passes on both of the repository's challenges (E75, E79).
- The monotonicity argument behind finding 1 is a human argument about the scripts, not machine-checked.
- Two identities in §5 of the paper (the measure scaling and the critical weight `b* = −(3−2h)/4`) are the auditors' own derivation, labelled as such.

Kernel acceptance is now reproduced for the `NavierStokes` library, not merely reported. That settles the terms; it does not settle the statement. The theorem remains true **if** the kernel accepts it — and Clay's (C) is what the encoded statement says — neither of which the kernel tests.

## Reproducing

```bash
git clone https://github.com/openai/NavierStokesAndEuler.git
cd NavierStokesAndEuler && git checkout f9e8bc5
# then follow the repo's own build instructions
```

All citations are `path:line` pairs into that commit.

`.github/workflows/kernel-check.yml` does the build in CI (Actions → kernel-check → Run workflow): clone at `f9e8bc5`, `lake exe cache get`, `lake build NavierStokes`, then the axiom probe. It exists because this host cannot run the toolchain, and it does not run automatically. Run `44987195620` (2026-11-22) is the one the claims above rest on: green, 9,580 jobs, five footprints printed, artifact `kernel-check-logs`. The full `build.log`, not a tail, is uploaded with it.

## Scope

The audit examines one result in depth: the whole-space forced Navier–Stokes theorem behind `breakdownStatement`.

Alternative (D), the periodic corollary, is in scope for the statement and the architecture of its proof: E70 reads the compression, the periodization and the comparator bridge in both directions, and finds the excluded class *weaker* than (C)'s (it imposes no energy bound at all). The axiom print E70 and E72 left open has since been run, green, from a clean clone (E73); the external Comparator statement check has since been executed and **passed** on the builtin kernel (E75), and E76 now carries the statement-level comparison itself: every numbered condition of Fefferman's (C) and (D), plus the errata, matched to a named Lean field, none missing or weakened. What remains outside is not a judgement about the encoding but the two reading conventions E76 §3 names, and the periodic development's own machinery. The periodization lemmas have since been read rather than sampled (E83): `periodize` is a lattice `tsum` whose local finiteness, summability and differentiability are proved, locality under `r < 1/2` is proved, the post-one extension is discarded before summing, and the PDE transfers at the same viscosity. The proof of `classical_uniqueness_on_Icc` has since been read too (E85): the difference-energy balance is *derived* from the PDE by integration by parts on the cube, the gradient bound comes from compactness of the spacetime slab rather than from a hypothesis, and Gronwall with zero initial data closes it. The integration layer underneath is read too (E86): `cubeIntegral_partial_eq_zero` is an instantiation of Mathlib's box divergence theorem with periodicity supplying the face-matching hypothesis, integration by parts is a corollary of it, and differentiation under the integral is dominated convergence on a compact slab. That chain now runs from the solution definition to the energy identity without an assumed estimate in it.

The Euler development was outside this audit until E79. That entry now runs its Comparator challenge end to end: the library builds from a clean clone, both of its headline theorems pass on two kernels, and their axiom footprint is the three permitted axioms with no `sorryAx`. That is a statement-level and kernel-level result, and E80 ties the statement to the repository: the two declarations are the ones its own metadata designates, and the challenge's class is proved equivalent to the development's rather than assumed to match. E81 does the E76-shaped job for Euler against the paper's Theorem 1.1 and finds two soft clauses: the paper's gradient blowup is encoded as C¹-norm blowup (the same claim plus a velocity term, and therefore weaker), and the lifespan is taken over a Sobolev class that is not proved to contain the paper's smoothly evolving solution (E82 §4). Everything else in the encoding is exact or stronger. No line of the Euler proof was read, and no mathematical claim is made about it beyond that clause comparison.

Independent commentary, not affiliated with OpenAI. The upstream repository's own licence governs its code; the audit documents are the authors' own work.

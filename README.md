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
| `MANUSCRIPT.tex` | The audit paper, 1,555 lines. LuaLaTeX or XeLaTeX. |
| `AUDIT_LOG.md` | The working log: entries E0–E66, every `path:line` citation behind the paper. |
| `PHASE2-FINDINGS.md` | Second-pass findings: the anisotropic weights, the three "free doors", the packets. |
| `CAVEMAN.md` | The whole thing rewritten in caveman. Every finding, plus §13–15: the equation symbol by symbol, why 3D is the hard case, and the four Clay doors A–D. |
| `CAVEMAN_1TO1.md` | The paper section for section in caveman: 8 sections, 33 subsections, appendix and bibliography. Nothing skipped. |
| `BUZZWORDS.md` | Every invented label the paper uses (§A–G) and every real technical term it assumes you know (§H), each defined. |
| `cone_weights.svg` | The diagram: the generalized cone and the two viscous weights, with the `2h` gap. |
| `equation_terms.svg` | The four terms of the equation, one panel each: clock, advection, viscosity, pressure. |
| `clay_doors.svg` | The four Clay alternatives as a decision tree: arena × hand → A, B, C, D, with EVERY versus ONE and each door's status. |

## The three-sentence summary

The artifact is logically clean — no reachable `sorry`, no `axiom`, no `native_decide`, no `unsafe`, no `implemented_by`, and the force's global smoothness is *proved*, not assumed (trace in E65). But the kernel answers only "does this term inhabit this type", so constants and real exponents — which live in terms, not types — are never weighed or dimensioned. Separately, the repo's own derivative identities show the viscous term is two pieces with weights differing by `2h`, so no admissible member is isotropic, while the whole scale regime sits behind a single `Classical.choice`.

## What this audit did not do

- **Did not recompile.** No Lean toolchain was available. Every claim comes from reading proof terms, binder order, and definitions — not from re-elaborating.
- **Did not re-run the nine external checkers** the repository reports.
- The monotonicity argument behind finding 1 is a human argument about the scripts, not machine-checked.
- Two identities in §5 of the paper (the measure scaling and the critical weight `b* = −(3−2h)/4`) are the auditors' own derivation, labelled as such.

Truth here is conditional on kernel acceptance. The correct phrasing is "the theorem is true **if** the kernel accepts it", not "is true".

## Reproducing

```bash
git clone https://github.com/openai/NavierStokesAndEuler.git
cd NavierStokesAndEuler && git checkout f9e8bc5
# then follow the repo's own build instructions
```

All citations are `path:line` pairs into that commit.

## Scope

The audit examines one result: the whole-space forced Navier–Stokes theorem behind `breakdownStatement`. The repository's periodic Navier–Stokes and Euler developments are not audited here, and no claim is made about them.

Independent commentary, not affiliated with OpenAI. The upstream repository's own licence governs its code; the audit documents are the authors' own work.

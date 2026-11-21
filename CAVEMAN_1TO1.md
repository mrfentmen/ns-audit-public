# THE PAPER, ONE TO ONE, CAVEMAN

This file is the audit paper said again in caveman. Eight main sections and two appendices. Same subsections, same order, same appendix. Nothing skipped. Nothing invented. Where the paper says "we did not check this", this file says it too, because a caveman who hides the hole in his own cave is a caveman who gets eaten.

The other caveman file (`CAVEMAN.md`) is the tour: pictures, the equation, the four Clay doors. This file is the paper itself, walked end to end.

---

## START HERE — THE PAPER IN SIXTY SECONDS

One question holds this whole paper together: **when a computer says a proof is checked, what did it actually check?**

A proof assistant is a very literal clerk. It checks that each line follows from the lines above it. It does **not** check that the definitions match the real world, that a number is the right size, or that a unit is the right unit. It cannot, because it was never given those things to check.

The repository under audit proves a real thing: for every viscosity there is a smooth push, starting from rest, that makes the fluid speed run to infinity while the energy stays bounded, and for which no global finite-energy solution exists. That is a genuine theorem, and the clerk checked every step of it.

The paper then makes two observations, and neither one says the proof is wrong.

- **Observation one.** Every quantitative constant in the chain is introduced as "some number exists". The clerk confirms that a number exists. It never confirms that the number is small, or the right size for the next step, or dimensionally sane.
- **Observation two.** The viscosity term splits into two pieces that shrink at different rates: one with the radius, one with the height. The difference is a factor of `q^{2h}`. The code proves this itself, in four theorems. What the code cannot do is object if a reader treats the two pieces as one.

So the honest summary is: the artifact is logically clean, and "machine-checked" here means **structure-checked**, not **number-checked**.

On the Clay problem, this result sits in alternative **(C)** — the forced-breakdown door, where a hand from outside is allowed. It says nothing about the unforced doors (A) or (B), and it is not a claim on the prize.

---

## HOW TO READ THIS FILE

Three ways, depending on how much time you have.

- **Sixty seconds.** Read the section above, then §8.1 and §8.2. That is the whole argument.
- **One sitting.** §1 through §4, skipping the boxed code blocks. That is the two findings and why they are structural.
- **Looking something up.** Use the glossary below, then Appendix A for exact file and line.

Every `> **In human words.**` block is a plain-language restatement of the paragraph above it. They are the fastest way through a dense section.

---

## WORDS THAT LOOK SCARY

Nothing below is a new claim. This is a translation table for symbols and Lean names that appear in the text.

| Term | Plain meaning |
|---|---|
| `u`, `p`, `f`, `ν` | velocity, pressure, the push from outside, thickness of the fluid (viscosity) |
| `w` | the difference between two velocity fields, used when proving uniqueness |
| `τ` | time left before the bang: `τ = 1 − t` |
| `q` | the shrinking factor near the bang; it solves `q − z²q^{2h} = τ` |
| `D(h)` | how fast height shrinks compared with radius: `D = ½ − h` |
| `η`, `X` | height and radius measured in shrinking units, so the cone stays still |
| `b` | the power attached to a profile: bigger `b` means a faster-growing field |
| `b_*(h)` | the power that keeps the energy from changing with scale: `−(3−2h)/4` |
| `Δ_ax` | the viscous term written in cylinder coordinates |
| `Z_{h,b}` | the bookkeeping factor that appears when you differentiate in the vertical direction |
| `χ`, `∇χ_R` | a smooth fade-out function, and its gradient; it dies before the boundary |
| `CandidateProperties` | the twelve-item checklist the theorem has to satisfy |
| `GlobalFiniteEnergySolution` | a solution that exists for all time with finite energy |
| `noncomputable` | Lean cannot run it; the object is only known to exist, not calculated |
| `Classical.choice` | pick a witness out of an existence proof; there is no formula for it |
| an `∃`-bound constant | "some number exists" instead of a number |
| type index | a number baked into a type, so a wrong one fails to compile |
| unification | the step where Lean decides two types are the same |
| `native_decide` | a shortcut that trusts compiled code; not used here |
| `sorry` | Lean's "trust me" hole; none is reachable here |
| `ActualBounds` | the bundle of scale numbers the packets need |
| `constructionScales` | the single sealed choice that produces those numbers |
| `timeWidth` | how long one packet lasts in time |
| `horizonTime` | the time at which a packet window ends |
| `StageGuards` | the record that carries the proved halving from one stage to the next |

---

## 1. INTRODUCTION

### 1.1 The artifact

Big cave. Lean 4. **641,332 lines**, **2,659 files**. People say "28.6 million lines" — that is the whole Mathlib closure, not this cave. Do not repeat that number.

The cave is clean at the bottom: no `axiom`, no `native_decide`, no `unsafe`, no `partial def`, no `@[implemented_by]`, and no `sorry` you can reach from the proof roots. One module does carry a `sorry`, `ComparatorChallenges/NavierStokes.lean`, and it is unreachable: nothing under `NavierStokes/`, `Euler/`, the root `NavierStokes.lean` or `Euler.lean` imports it, and the module says so in its own header.

The repo says nine outside checkers accepted it. We did not run them. Say that out loud.

So the question is not "does it compile". The question is: **what does the compiled thing actually certify?**

### 1.2 What the artifact proves

The headline is small:

```
∀ ν > 0, ∃ u, ∃ p, ∃ f, ∃ K,
  CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalFiniteEnergySolution ν f)
```

`CandidateProperties` holds twelve fields. The ones that matter: velocity smooth, pressure smooth (both C^∞ on the pre-singular domain), speed unbounded (`limsup_{t↑1} ‖u(t)‖_∞ = ∞`), zero initial velocity, divergence free, force smooth, force support in `t > 0`, compact spatial support for `u` and `p`, and the equation itself:

```
∂_t u + (u·∇)u − νΔu + ∇p = f    on (0,1) × ℝ³
```

The version actually proved is stronger: `theorem_1_1_with_initial_rest` gives `u ≡ p ≡ 0` for `|t| ≤ 3/8`, and `theorem_1_1` is the same claim with no constant in it.

Said in human words: **for every ν > 0 there is a smooth compactly supported hand, a zero start, a flow that stays smooth and keeps finite energy on `[0,1)`, whose speed runs off to infinity as `t ↑ 1`, and for which no global finite-energy solution exists at all.**

### 1.3 Two halves, of very different cost

The statement is two claims wearing one coat. Split them or you will lie to yourself about the cost.

**Naming the hand is free.** Take any smooth divergence-free `u`, compactly supported in space, zero for `t ≤ 3/8`, blowing up at `t = 1`, finite energy. Put `p := 0`. Let `K` be the closure of the support. Define

```
f := ∂_t u + (u·∇)u − νΔu
```

Then `f` is smooth on the slab, supported in `K`, zero near `t = 0`; the equation holds identically; and **every** field of `CandidateProperties` except two holds. What does not follow: a smooth extension of `f` to all of `ℝ⁴`, and compact support stated for a function on `ℝ⁴`. `f` was only ever defined on a slab.

No fluid equation was solved. A field was picked and its leftover was named "hand". The repo does not hide this: `originalResidual A v p` is literally the residual of the constructed fields. And `force_nonzero_of_no_global_solution` records the honest lower bound:

```
CompactPositiveTimeSupport(f) ∧ ¬∃ global finite-energy solution(ν,f)
  ⟹ ∃ t > 0, ∃ x, f(t,x) ≠ 0
```

That is not a confession of a gap. It is the sharpest way to say the result is **forced**, not spontaneous.

**Smoothing the hand is not free.** The distance between that free proposition and the theorem is a second obligation, and it is the expensive one. Because the speed is unbounded, `∂_t u` is singular at `t = 1`; the residual is a pile of singular terms whose sum must cancel to all orders there. Making a field blow up is easy. Making its leftover not blow up is the whole construction.

The repo pays this in the force assembly, not through the identity: `of_localized_fields` takes `hf : ContDiff ℝ ∞ f` as a **hypothesis** and hands it straight to `force_smooth`.

**What is not free** (the paper's remark): two conjuncts carry cost. First `force_smooth` — a residual defined on the slab must be extended smoothly across the very time where its own `∂_t u` blows up. Second `¬ Nonempty (GlobalFiniteEnergySolution ν f)` — a real uniqueness theorem, `classical_uniqueness_on_Icc`. Its competitor class demands only smoothness, divergence-freeness, matching residuals, and uniform finite energy. No pressure norm. No decay of `p − q` at infinity. No support, growth, or derivative condition on the competitor. Pressure is killed by a Riesz pairing, and the Gronwall constant is uniform in the localization radius by binder order (`∃ D ≥ 0, ∀ R ≥ 1`).

So the ledger has three lines, not two: **naming = free. smoothing = the construction. comparison = the mathematics.**

> **In human words.** Three jobs, three bills. **Naming** the hand is free: pick a flow that already blows up, compute what is left over, and call that the force. Nobody solved anything. **Smoothing** the hand is the construction: the flow's own time derivative explodes at the bang, so the leftover is a pile of exploding terms and the construction has to make them cancel to every order. **Comparison** is the mathematics: proving that no other global solution exists for that same push. The repository pays all three, but only the third is the kind of thing a referee would call a theorem.

### 1.4 Two structural findings

Finding one, the **Non-Evaluated Constant Barrier**: the analytic chain is quantitatively empty at the level of constants, and the rock cannot see that — not by accident, but for a reason that lives in the type theory.

Finding two, **Anisotropic Viscous Scaling**: the repo's own pullback identities show the Laplacian is a sum of two homogeneous pieces in the similarity weight. Radial piece has degree `1`; axial piece has degree `2D(h) = 1 − 2h`, which sits in `(0,1)`. So no admissible member of the family is isotropically self-similar.

Both are one principle: **the rock audits arithmetic that got reflected into types, and says nothing about arithmetic that did not.** Constants inside `∃` binders and real exponents inside definitions are not reflected.

### 1.5 Relation to the macroscopic caveats

People talk about two things: the zero starting datum, and the hand. Both are real. Both are statement-level. Neither is this paper's subject. We take them as given and ask a different question: given that statement, what does the proof **certify**?

The answer is not "everything the compiler checked". This matters because "machine-checked" gets read as "numerically and dimensionally reliable", and §3 shows that reading is false here for a structural reason — one that will come back in any big formalization of a quantitative PDE estimate.

### 1.6 Method and reproducibility

We read proof terms and binder sequences. We did not re-elaborate them. For every claim the log records: the declaring file and line, the binder order where it matters, the statement in normal notation, and a dimension check.

Where a review task named a file or declaration that does not exist at `f9e8bc5`, the log records the missing premise and points at the module that really carries the content. It does not invent a lemma. Of thirty-five tasks in the final review matrix, nineteen were answered from declarations that exist under the names given; sixteen needed premise correction (E46, E47).

---

## 2. PRELIMINARIES: NOTATION AND THE TWO SPACES

Letters: `u` velocity, `p` pressure, `f` hand, `ν > 0` kinematic viscosity, `ω = ∇ × u` vorticity, `w := u − v` difference of two fields. `τ := 1 − t` is time left before the bang. `r = |x'|` cylindrical radius, `s := r²/2`, `z := x₃` axial. `𝕋³` the unit torus. `innerCube(r) := {x ∈ ℝ³ : |x_i| < 1 − r for all i}`; at `r = 1/4` that is `(−3/4, 3/4)³`.

Two facts about the whole-space/torus seam. Both were targets of an earlier hypothesis that the audit killed.

**One: whole space comes first.** The torus is periodized **from** it by a lattice sum of the cut whole-space pressure,

```
p_{𝕋³}(t,x) = Σ_{k ∈ ℤ³} χ(x+k) p(t,x+k)
```

and the local finiteness of that sum is proved, not assumed.

**Two: the two residuals agree exactly.** On the inner cube it is a jet identity, not a decay estimate:

```
∂^α periodicResidual A p (t,x) = ∂^α cutResidual A p (t,x)   on innerCube(1/4)
```

(`PeriodicResidualLimits.lean:138`), obtained from a germ equality. Support radius is at most `1/4`, the cube has margin `1/2`, so the lattice sum has no overlap and no spectral truncation is involved.

Why it matters here, narrowly: the pressure in the comparison is fixed only up to a constant — the Riesz symbol acts on the data, and the constant dies against `∇·w = 0`. So **no pressure norm is ever assumed.** That is a strength, and it is why the comparison survives the statement-design objections. It is also why the quantitative content must be examined separately: with pressure gone, what remains is a chain of inequalities, and that chain is where §3 bites.

### 2.1 Alternative (D) and the pressure-periodicity clause

The repo also formalizes a periodic corollary — alternative **(D)**, not (C). Its candidate **and competitor** carry a clause with no whole-space twin:

```
pressure_periodic : UnitSpatialPeriodsOn (Ico 0 1) p
```

Read against a statement that makes only the velocity periodic, that clause would shrink the competitor class — and shrinking the competitors is exactly how a breakdown claim can be made to look easier than it is. **The objection does not land here.** The official problem description carries an erratum saying plainly that in the periodic case equation (8) requires both velocity and pressure to be periodic. The repo's clause is the published hypothesis, not an addition to it.

The clause is dead weight for this paper, which is about (C) on `ℝ³` and never invokes pressure periodicity; whole-space comparison kills pressure by Riesz pairing instead. One limitation said in the same breath: **we did not read that erratum at first hand.** The attribution rests on the repo's own reference and on secondary descriptions. Correctly attributed, not independently verified.

---

## 3. THE NON-EVALUATED CONSTANT BARRIER

### 3.1 Three exhibits

**Exhibit one — a Sobolev constant inherited from Mathlib.**

```
def sobolevConstant : ℝ :=
  (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ)
```

used for `‖f‖_{L⁶(ℝ³)} ≤ sobolevConstant · ‖∇f‖_{L²(ℝ³)}`. It is `noncomputable`: it is whatever Mathlib's proof happened to produce. Its child `weightedSobolevConstant := 4 * sobolevConstant + 1` is just as blind.

**Exhibit two — a witness pulled out of an existence proof.** `LocalizedFluxEstimates.lean:176` proves `∃ C > 0, ∀ x, ‖D² baseWeight(x)‖ ≤ C` by compact support plus continuity, with `C = max(1, C₀)`. Line 184 then *names* it:

```
def weightSecondDerivativeConstant : ℝ :=
  Classical.choose exists_weight_second_derivative_bound
```

and lines 186 and 190 record only that it is positive and that it bounds. The term is definitionally opaque: not reducible, no computable content, no equation beyond the inequality it was chosen to satisfy.

**Exhibit three — a pressure functional bounded by an existential.** `PressureFunctionals.lean:169` gives `∃ C ≥ 0` bounding `|averagedPressureDifferenceValue W₀ W₁ G k ψ|` by `C · √(fourierHNormSq 3 ψ)`, and line 279 restates it for the functional the flux estimate actually eats. The witness is assembled from an explicit expression in the data,

```
M = 3√(l2Sq W₀) + √(l2Sq W₁) + Σ_i ∫‖G_ki‖ + Σ_{i,j} ∫‖G_ij‖
```

times an operator-norm constant `B` from `exists_uniform_test_bound`. So the **dependence** on the data is explicit. The **size** is not. This is the friendliest of the three, and it still does not evaluate.

### 3.2 Why the kernel cannot see it: indices versus terms

**Indices are checked.** A family like `Lp ℂ p` or `ContDiff ℝ n` is a *type family*. A term of type `Lp ℂ 6` is not a term of type `Lp ℂ 4`; the elaborator must solve `6 =? 4` and fails. So any exponent reflected into an index is checked by unification, and changing it by a nonzero amount is a type error. The kernel is a complete decision procedure — **relative to the declared type family.** It decides whether a term inhabits the type it was handed, not whether that type is the physics you meant. A development that consistently encodes a wrong exponent elaborates exactly as smoothly as a correct one. The guarantee is internal consistency with the spec, not correspondence between spec and problem.

**Terms are only inhabited.** The proposition

```
∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Tx‖ ≤ C‖Sx‖        (★)
```

is checked by verifying that the witness inhabits it. There is no second, independent specification of `C` to compare against; the proposition **is** the specification. And once `C` comes out of `Classical.choose`, it is not merely unknown but *inaccessible*: not reducible, not computable, not inspectable by `norm_num` or `decide`, with no defining equation.

**Consequence.** An exponent error that reaches an index becomes a compile failure. A constant error does not: `(★)` stays true when `C` becomes `10⁶C`, and every use in the repo is monotone in `C` (each occurrence is `≤ C · norm` with `C` in positive position), so the inflated witness inhabits the same statements. The artifact cannot tell a correct constant from a bloated one. That monotonicity observation is a human argument about the scripts, not a machine-checked fact — which is why dimensions had to be checked by hand (E10.7).

### 3.3 Epistemic, not logical

Do not oversell this. The barrier creates no unsoundness and does not threaten the theorem's truth.

**The barrier cannot falsify the headline.** The type of `theorem_1_1` contains no numerical constant: `∀ν>0, ∃u ∃p ∃f ∃K, CandidateProperties ν u p f K ∧ ¬Nonempty(…)`. So no assignment of values to auxiliary constants can change the truth value of what was proved. Immediate from the shape: no constant sits in the binders or the body except through `CandidateProperties`, whose fields are qualitative — smoothness, support, divergence-freeness, an identity, an unboundedness claim, and a negated existential.

What it does kill:

| Claim | Status |
|---|---|
| The proof yields an explicit bound | **No** — every constant is `∃`-bound or `choose`n |
| The bound is dimensionally consistent | **Not machine-checked** — dimensions are a semantic layer the type theory does not have |
| The constant is small enough for the next step | **No** — no step ever instantiates a constant by a numeral |
| The exponent bookkeeping is correct | **Yes**, where the exponent reaches a type index or a reducible definition |
| The theorem itself holds | **Yes**, subject to kernel acceptance |

### 3.4 The contrast case: exponents that *are* checked

It would be wrong to say the formalization checks nothing quantitative. The exponent ledger does real work, and it works precisely because its objects are reducible definitions, not existential witnesses.

`ExponentLedger.lean` fixes the residual-order budget. Its header says openly that it checks the arithmetic of those assignments *conditional on the estimates being valid*, and that it does not define the analytic classes, build a correction, or prove a PDE estimate. Inside that fence the results are exact. The correction gain is a nested minimum,

```
particularGain(σ,κ) = min( min(min(½−3κ, ½−κ), ½+σ−κ), 2/5 )
```

and `particular_gain_eq` proves it equals `2/5` for `σ ≥ 1/5`, `κ ≤ 10⁻⁵`, by `linarith` on exact rationals. The signed gain is `2/5 − κ` under the same hypotheses, so the binding gain is `2/5 − κ`, and the first listed entry `½ − 4κ` is slack by `1/10 − 3κ`.

That is the sharpest possible contrast. The gain is a **definition** of a real number built from rationals; equality with a numeral is decidable by linear arithmetic, and the kernel checks it. The Sobolev constant is a **witness** of an existential; no numeral exists, and the kernel checks only that some witness exists.

Two more things the ledger says. First, `κ` is **never defined** in the repo: every theorem is stated for `κ ≤ 1/100000`, and `manuscript_kappa_admissible` only checks the numeral `10⁻⁵` against that bound. The artifact verifies a **range**, not the manuscript's choice; `smaller_kappa_admissible` records that `10⁻⁶` works too. Second, the tightest numerical margin is the `17/100` bar-residual bound, whose exact threshold is `κ < 1/200` (`old_difference_bar_margin_iff`) — three orders of magnitude above the value used. So the ledger is not tight, and its correctness is consistency, not optimality.

### 3.5 Consequence for the "fully verified" reading

The natural reading of "machine-checked" is that the paper's quantitative content got checked. On this artifact that reading fails, and it fails structurally: not because some constant is wrong, but because the assistant has **no mechanism** by which a constant could be right in a checkable sense.

At the quantitative level the formalization is a certificate that the exponent algebra and the implication structure are **consistent**. That is real and not small — it is what catches an off-by-one in a derivative count, which is the usual way this literature breaks. It is not a certificate of numerical or dimensional correctness.

---

> **In human words.** A recipe says "add some flour". The clerk checks that flour exists in the kitchen. It never checks the amount, and it cannot tell you whether the cake will work. That is fine if the recipe only promises "there is a cake". It is not fine if a reader takes "machine-checked" to mean "the amounts are right". The paper's claim is exactly this distinction, no stronger.

## 4. ANISOTROPIC VISCOUS SCALING UNDER THE GENERALIZED CONE

### 4.1 The coordinates

`a = 2h ∈ (0,1)`, `τ = 1 − t > 0`. The quantity `q = q(τ,z)` is the unique positive solution of

```
q − z² q^{2h} = τ
```

(`forwardScalar`, `coordinateQ_spec`). Inner coordinates:

```
η := z / q^{D(h)},    X := s / q,    D(h) := ½ − h
```

matching `coordinateEta` and `coordinateX`, with `D` at `CoordinateAlgebra.lean:19`. Eliminate `η` using `z = q^D η`: then `q(1 − η²) = q − z² q^{2h} = τ`, i.e.

```
τ = q · d(η),    d(η) = 1 − η²
```

and since `a = 2h`, we get `(q^D)² q^{2h} = q^{2D+2h} = q`. So the defining equation is exactly `q · d(η) = τ`.

The geometry lives in the inner coordinates. The level set `η = ±1`, i.e.

```
|z| = q^{D(h)}
```

is the boundary of the **generalized cone**. For `h ∈ (0, ½)` we have `D(h) ∈ (0, ½)`, so this is a paraboloid-like surface `|z| ∼ τ^D` whose opening depends on `h`. The classical parabolic case is the *other* endpoint, `h = 0`: there `D(0) = ½` and `η = z/√q` is the ordinary heat variable. The admissible range excludes that endpoint; at `h = ½`, `D = 0` and the axial scale stops contracting at all.

The scaling group is

```
(τ, z, s, q) ↦ (Qτ, Q^{D(h)} z, Q s, Q q)
```

which leaves `η` and `X` fixed. That this group acts by **proved** homogeneity, not postulation, is `forwardScalar_scale`, `coordinateQ_scale_h`, `coordinateEta_scale_h`, `coordinateX_scale_h`. The last three derive the scaling from the defining equation and uniqueness of its positive branch — not from an assumed ansatz.

### 4.2 The pullback and its four exact derivative identities

The profile pullback: for `h ∈ (0,½)`, `b ∈ ℝ`, inner profile `f`,

```
(Φ_{h,b} f)(t,s,z) := q^b · f(X, η)
```

The physical partials are genuine Fréchet derivatives along the coordinate directions, not formal symbols.

**Exact weight transport.** For `f` in `C²` near `(X,η)`:

```
∂_s (Φ_{h,b} f)  = Φ_{h,b−1} (∂_X f)
∂_z (Φ_{h,b} f)  = Φ_{h,b−D(h)} (Z_{h,b} f)
∂_s² (Φ_{h,b} f) = Φ_{h,b−2} (∂_X² f)
∂_z² (Φ_{h,b} f) = Φ_{h,b−2D(h)} (Z_{h,b−D(h)} Z_{h,b} f)
```

where

```
Z_{h,b} f = ( 2η b f + d(η) ∂_η f − 2ηX ∂_X f ) / L(h,η),    L(h,η) = 1 − 2hη²
```

The proof: the first-order identities are `partialS_pullback` and `partialZ_pullback`; the second-order ones are `partialS_partialS_pullback` and `partialZ_partialZ_pullback`. Each is proved by differentiating the pullback along the coordinate with chain and product rules, then identifying the result as the pullback of the stated inner expression. The chain coefficients are the explicit rational functions `qTime, etaTime, xTime, qAxial, etaAxial, xAxial`; the identifications are `time_chain_coefficient` and `axial_chain_coefficient`. The second-order cases need a *local* `C²` hypothesis, because they differentiate a first-order identity on a neighbourhood — which is why they are stated with `ContDiffAt` and not pointwise differentiability.

The asymmetry is the point: `∂_s` moves the weight by exactly `−1`, `∂_z` moves it by `−D(h)`. The first comes from `X = s/q`; the second from `η = z/q^D`, and the cone's opening exponent is what appears.

### 4.3 The Laplacian is a sum of two homogeneous weights

In axisymmetric variables `(s,z)`:

```
Δ_ax = 2s ∂_s² + 2 ∂_s + ∂_z²
```

The factor `2` is the Jacobian of `s = r²/2`; below, only the weights matter. One care: `s = qX` in front of `∂_s²` is **not** constant in the inner variables, so it travels with the derivative and eats one power of `q`.

**Two weights, not one.**

```
Δ_ax (Φ_{h,b} f) = Φ_{h,b−1} (2X ∂_X² f + 2 ∂_X f)
                 + Φ_{h,b−2D(h)} (Z_{h,b−D(h)} Z_{h,b} f)
```

Proof in one breath: `∂_s²` gives `q^{b−2} ∂_X²f`; multiplying by `2s = 2qX` gives `2q^{b−1} X ∂_X²f`; `2∂_s` gives `2q^{b−1} ∂_X f`; the axial term is the `∂_z²` identity as stated; add the three pieces of `Δ_ax` and collect the two radial ones.

The radial group closes on a **single** weight, `b − 1`: the second radial derivative loses two powers, and the Jacobian factor `s = qX` gives one back. The axial group does not. Its degree is

```
b − 2D(h) = b − (1 − 2h)
```

and the two degrees differ by

```
(b − 2D(h)) − (b − 1) = 1 − 2D(h) = 2h ∈ (0,1)
```

Neither degree is what an isotropic Laplacian would carry in `q`, which is `b − 1`. That is the radial degree itself; the axial one matches only at `h = 0`. For `q ∈ (0,1)` the axial coefficient is the *smaller* of the two by `q^{2h}`, so the axial term is the more damped, and the radial term is the more singular near the apex. Which one dominates any given expression also depends on the inner factors `Z Z f` — the weight alone does not decide it. A bound that treats `νΔ` as one homogeneous object of degree `b − 1` **mis-assigns the axial piece**.

**Corollary — no admissible member is isotropic.** For `h ∈ (0,½)`, `2D(h) = 1 − 2h ∈ (0,1)`, so the axial degree differs from `b − 1` for every admissible `h`. The coincidence `2D = 1` happens exactly at `h = 0`, and `2D = 2` at `h = −½` — both outside the range of every declaration in `SimilarityProfile.lean`, which all carry `0 < h` and `h < ½`.

**What this does and does not say.** It is not a claim that the construction fails to be self-similar. It is a statement about the **operator**: on this family the viscous term is a sum of three homogeneous pieces with distinct degrees, and the axial degree depends on `h`. Any estimate written as "`νΔ` acts with weight `q^{b−2}`" is, on this family, an assertion about the radial part alone. Whether the accompanying manuscript makes that assertion is a question about the manuscript's text. What can be certified is that the code's own identities forbid the isotropic reading for every `h` the code uses.

> **In human words.** Shrink the fluid towards the bang. The cone squeezes height by `q^D` and radius by `q`. The viscous term has two parts: one measures how the flow changes sideways, one how it changes vertically. They do not squeeze at the same rate — they differ by `q^{2h}`. Treating them as one number is like measuring a stretched photograph with a single ruler: the ruler is not wrong, it is just measuring only one direction.

### 4.4 The container absorbs the mismatch

The anisotropy is not a defect of the coordinates. It is the cone's geometry doing its job. The inner domain is `|η| < 1`, with `X` in a bounded interval because the profile is compactly supported. So `dz` scales like `q^{D(h)}`, `ds` like `q`, and the physical measure element is

```
dz ds = q^{1 + D(h)} · (L(h,η)/d(η)) · dX dη
```

because `z = q^D η` with `q d(η) = τ` gives `dz = q^D (L/d) dη` at fixed `τ`, while `ds = q dX`. Hence

```
‖Φ_{h,b} f‖²_{L²(dz ds)} = q^{2b + 1 + D(h)} ∫_{|η|<1} (L/d) |f(X,η)|² dX dη
```

so the weight that makes the *scaling* of the norm cancel is

```
b_*(h) = −(1 + D(h))/2 = −(3 − 2h)/4
```

At `b = b_*` the pullback is scale-invariant, but **not an isometry**: the inner integral still carries the weight `L/d`. On a profile supported in `|η| ≤ 1 − ε` that weight sits between two positive constants, since `L ≥ 1 − 2h` and `d ≥ 2ε − ε²`. Without that gap from the cone boundary, the equivalence fails as `|η| → 1`.

As `h → ½` this gives `−½`; as `h → 0`, `−¾`. The critical weight moves with the cone's opening. Viscous losses sit at `b_* − 1` (radial) and `b_* − 2D(h)` (axial), so the axial term is the more damped and the radial the more singular.

**These equations are ours, not the repo's.** The measure, `L²` and `b_*` lines are not stated anywhere upstream; they follow immediately from the inner coordinates, the scaling group and the pullback definition, and we label them as derived. They are included to make the geometric reading explicit: the cone is a container whose axial opening decides both which derivative loses least and which weight is `L²`-critical. An exponent ledger that assigns a single viscous exponent is, in this geometry, assigning wrong bookkeeping to one of the three terms.

### 4.5 Why the exponent ledger cannot see this

Same reason the constants are invisible, and it is precise. The weight `b` is a **real-number argument** of a definition. It sits in `q^b` through `Real.rpow`, whose type is `ℝ → ℝ → ℝ` no matter what `b` is. Changing `b` to `b − 2h` changes no type, creates no unification problem, and cannot be detected by the kernel.

Likewise `D(h)` is a definition, and `2D(h) = 1 − 2h` is proved by `ring`. But **no declaration asserts `2D(h) ≠ 2`**, because that is a statement about geometry, not about the algebra the file set out to check.

So the ledger's arithmetic is exact where it operates — on rationals, by `linarith` and `ring` — and silent where the geometry walks in. The anisotropy is visible in the code, in four theorems with explicit weights. What is missing is any declaration that would **fail** if someone treated those weights as equal. That absence is structural: to make `b` an index you would have to reflect it into a type, and the repo does not.

---

## 5. THREE INTERFACE AUDITS

Sections 3 and 4 live inside the chain. A separate pass walked the three **seams** where a construction like this usually pays a visible bill: the edge of space at infinity (where a pressure-velocity pairing gets integrated by parts), the time seam at `t = 3/8` (where the field switches on), and the divergence defect you get from cutting a divergence-free field.

In all three the same thing happened: **what disappears is a separate boundary, matching, or corrector estimate — not because the term is small, but because each one is replaced by an identity.** Each seam is closed by a germ equality, a case split, or a curl. That is why none of them adds a constant, an exponent, or a hypothesis to the ledger. They are not free, though: 5.3 records where the cutoff commutator is actually paid.

> **In human words.** Three bills that never arrive. At infinity the pressure term would need a boundary integral; the proof never writes one, because the test function fades out before it reaches the boundary. At the switch-on time `t = 3/8` the join would need matching derivatives; both sides are identically zero there, so there is nothing to match. At the cut, divergence would need a repair field; the construction cuts the potential and takes a curl, so the repair is already inside the velocity. Each seam is closed by an identity, not by an estimate.



### 5.1 Pressure non-locality and the spatial decay boundary

Pressure is the non-local solution of `Δp = ∂_i∂_j(u_i u_j)`. So any argument that integrates `∇p` against a field must do one of two things: assume decay at infinity (`lim_{R→∞} ∫_{∂B_R} p (w·n) = 0`), or restrict the competitor class to compactly supported fields. The audit asked which one the repo does.

**Neither.** `classical_uniqueness_on_Icc` has no boundary term to evaluate at all. Its hypotheses are: smoothness of `u, v, p, q` on the slab `[0,T]`; compact spatial support of the **reference** `u` only; divergence-freeness of both fields; equality of the two residuals; equality of the data; and a uniform finite-energy bound on the competitor `v`. There is no support, decay, growth, or derivative hypothesis on `v`, and no bound, decay, or growth hypothesis on `q`.

Two mechanisms make the surface term vanish before it is written. First, pressure never appears alone — it is paired with `∇χ_R`, and `χ_R` is compactly supported for every finite `R`, so no integral over `∂B_R` is ever formed. Second, the Riesz identity `actual_flux_eq_canonicalCutoffFlux` rewrites that pairing as the canonical Riesz functional of `u ⊗ v`, after which `exists_uniform_actual_pressure_flux_bound` bounds it by a constant fixed **before** `R` is quantified.

Every remaining `R`-dependence is explicit and dies:

```
C₀/R²,   (C₁/R)B^{3/2},   C₂[ (B^{1/2}+1)(A/R + 1/R²) + R^{−7/4}B^{3/4} ]
```

and `eq_of_pressure_flux_bound` drives `‖w(t)‖₂² → 0` by dominated convergence.

So the boundary term is neither assumed away nor dodged by a qualitative support predicate on the competitor: **it is never formed.** Decay at infinity is replaced by two weaker and checkable inputs — finite energy of the competitor, compact support of the reference — and the limit `R → ∞` is taken on a bound, not on an integral identity. That is stronger than the review task expected, and it is why no decay lemma exists to find: `WholeSpaceUniqueness.lean` has no such statement because the proof never needs one.

### 5.2 Temporal interface regularity at the initial rest margin

Second seam: `t = 3/8`, where the field goes from identically zero to active. The audit asked whether smoothness there is carried by one global `ContDiff` statement or by a piecewise conditional handing smoothness to sub-intervals, and whether the force time derivatives get evaluated at `t = 3/8`.

**Neither.** There is no `if-then-else`, and no derivative is evaluated at a point. The seam is a scalar multiplier in time alone: `activatedVelocity u := λ(t)u`, `activatedPressure p := λ(t)p`, and `PositiveTimeForce.force f := θ(t)f`. Smoothness is inherited because `C^∞` is closed under multiplication and composition — `activatedVelocity_smooth` and `force_contDiff` are one-line applications of `ContDiffOn.smul` and `ContDiff.smul`.

The two branches agree because the field itself vanishes on the early slab. `activatedVelocity_zero_early` and `activatedPressure_zero_early` give `u = p = 0` for `|t| ≤ 3/8`; `localized_residual_zero_early` gives a vanishing residual there; and the equation across the seam is closed by a two-branch case split on `t < 3/8` — early side both residual and force are zero, late side `PositiveTimeForce.force_eq` applies on `[3/8, 1]`.

Two corrections to the premise of the task. The declaration it named, `R3/CandidateBreakdown.lean`, contains **no** smoothness proof of `f` at all: its four theorems are the uniqueness transfer, the force-nonzero lower bound, and an `L²` bound. Force smoothness lives elsewhere — `compactForce_smooth` (a smooth spatial outer cutoff times `f`) followed by `PositiveTimeForce.force_contDiff`. And the force time support is not asserted near the seam but bounded away from it: `force_tsupport_subset` gives `tsupp f ⊆ [1/16, 21/16] × K`, which is what supplies the `CompactPositiveTimeSupport` field.

So no jet of `f` is matched at `t = 3/8` by computation. The seam is regular because both sides are eventually equal to the zero germ, and `C^∞` is closed under that identification.

### 5.3 Divergence-free cutoff corrections in the torus interface

Cutting a divergence-free field makes a defect: `∇·(χu) = u·∇χ ≠ 0`. The standard repair is a corrector field, found by solving a divergence equation and subtracting a gradient. The audit asked three things: does such a corrector exist, do its spatial derivatives eat powers of `q` missing from the exponent ledger, and is its residual added to `f` or majorized by an existential constant.

**There is no corrector, and none is needed.** The construction cuts the **potential**, not the velocity:

```
cutPotential A := χ A,     cutVelocity A := ∇ × (χ A)
```

and a curl is divergence-free identically (`spatialDivergence_spatialCurl_on`). The periodized velocity is the curl of the periodized potential, `periodicVelocity A := ∇ × (periodicPotential A)`, with `periodicVelocity_divergence_free` giving `∇·u = 0` exactly. The quantity `∇·(χu)`, the one a corrector would be for, never appears.

The price is paid somewhere else, and it is visible. The cutoff gradient is not removed — it is **kept inside the velocity**, by the product rule

```
∇ × (χ A) = χ (∇ × A) + ∇χ × A
```

The second term is exactly the commutator `[∇, χ]` that a corrector would have cancelled. Here it is part of the field, which is why the cut velocity is exactly divergence-free while being only germ-equal to `χ (∇×A)`: on the plateau, where `χ ≡ 1`, the commutator vanishes, and `periodicVelocity_eventuallyEq` upgrades the plateau identity to equality of all jets. Off the plateau the commutator is carried by `∇χ × A`, supported in the annulus `supportCylinder \ plateau`, and it enters the residual as an exact term of the equation.

Both ledger questions therefore have empty answers, and that is the finding: the exponent ledger has no corrector entries because there is no corrector, so no powers of `q` can be missing from it; and no corrector residual is absorbed into `f`, because there is no corrector residual to absorb. The force stays the exact residual of the fields actually used, and the equation holds by case split, not by estimate.

---

## 6. PACKET TIME-WIDTH COMPRESSION: DERIVED, WITH ONE CONDITIONAL LINK

Sections 3 and 4 are about the statement and about the homogeneity class of the operator. Neither says how the existence half gets built. Section 1.3 takes a field, names its residual, and stops; where the field came from is the assembly.

This section and the next close that gap in the repo's own terms, on the **Euler side** (`Euler/`), where the packet family is built and where the top-level singular datum is defined (E53).

### 6.1 The object is a packet, not a pulse

Search for the vocabulary of oscillatory pulses and you get nothing: a recursive search of `Euler/` and `NavierStokes/` for `pulse` and `oscillat` is empty, and no filename in either tree contains either word. The construction is named **packet**.

The subtree is big enough that the name matters: `Euler/` holds **1,839** files against **816** in `NavierStokes/`, and **110** of them are `Euler/Packet*.lean` mentioning compact support or a support inclusion. A scan for "pulse" reports the absence of a **name**, not the absence of a mechanism — and that is the difference between a negative audit result and a false one.

What is proved here is a construction, not a continuation: the packet time windows halve, and the datum they define is the limit. Nothing in this section claims smooth continuation of an evolving solution through `t = 1`. The smoothness proved is that of the limiting initial datum (E57).

### 6.2 The halving is a theorem about one geometric sequence

The thing that shrinks is `timeWidth`:

```
timeWidth J X n = 3 · scaleSequence J X (n+1) · scaleSequence J X n / sqrt(previousShear J X n)
```

where `scaleSequence` is geometric, `scaleSequence J X 0 = X` and `scaleSequence J X (n+1) = ((J+n):ℝ)² · scaleSequence J X n`, and `previousShear` is exponential in `scaleSequence` at exponent `7`.

The numerator is a product of consecutive terms. The denominator is super-exponential. You do not need asymptotics to see the ratio fall.

`actualWidths_contract` concludes

```
timeWidth J X (n+1) ≤ timeWidth J X n / 2
```

from `3 ≤ J`, `8 ≤ X`, an `ActualBounds` witness, and `δ ≤ 1/2`. The route is `actualTimeRatio_le`, which bounds the width ratio by `sourceTimeRatio` — one component of the `ActualBounds` series — after which `SmallSeries.term_le` gives ratio `≤ δ ≤ 1/2`, and `div_le_iff_0` turns that into halving. A finite series total, then arithmetic. No limit, no compactness, no asymptotic expansion.

> **In human words.** The packets are a stack of time windows that shrink. Each window is at most half the one before it, and that is proved by adding up a finite series — not by taking a limit. A finite sum is something a clerk can actually add. This is why the compression is a theorem rather than a hope.

### 6.3 One link is a hypothesis, and the join is made elsewhere

`horizonTime_antitone` carries

```
(hw : ∀ n, timeWidth J X (n+1) ≤ timeWidth J X n / 2)
```

as a **binder**, and that file does not import the guards file. Read alone, the nesting theorem is conditional; citing it as an unconditional compression result overstates by one import.

The join is made through the guard structure: `StageGuards.next_width` is a structure field, `stage_guards` fills it with `actualWidths_contract`, and `exists_guarded_sequence` produces `J`, `X₀`, `δ` uniformly. The compression closes through `StageGuards`, not through `PacketNestedHorizons.lean` alone. Section 7 shows where that field is consumed.

The arithmetic the nesting eats is `nested_horizon_of_width_ratio`: from `Δ ≤ 2W/3` and `W_next ≤ W/2` it yields `t + Δ + 2W_next ≤ t + 2W`, with `Δ` bounded by `stepLength_bounds`. Those constants give a **strict** drop the library does not state: since `2/3 + 1 − 2 = −1/3`,

```
horizonTime (n+1) ≤ horizonTime n − timeWidth n / 3
```

The library records only `≤`, which is all the nesting argument needs.

### 6.4 Grade is the derivative order

Whether "time-supports compress as the derivative index rises" is true of **this** construction depends on whether grade `n` is the jet order or just a stage counter. It is the jet order, in the operative sense.

`velocityJet` is assembled from `slicedJet` applied to `(a i).high`, `(a i).mean` and `(a (i−1)).corrector`; `knownJets O p a` is `history p` of that jet family, so grade `p` is exactly the order-`p` jet being cancelled; `profiles_step` for `p ≥ 2` depends only on the strict prefix, which is the well-founded recursion; and `tail_grade_bound` carries `N+1 ≤ n`, i.e. tail grades indexed beyond the required order `N`.

The literal theorem is still about consecutive **grades** `n` and `n+1`. `timeWidth` has no separate derivative-order parameter; the two indices coincide by construction, not by definition. A reader who takes the sentence as a statement about `∂^k` for arbitrary `k` is reading one step further than the code goes.

### 6.5 Three things the compression is not

1. **Not a dimensional law.** Grading and shrinking both come from the same `scaleSequence`; the ratio is controlled by a summable cost series, not by differentiating a scaling ansatz and reading off exponents. So it is not evidence for or against the isotropy question of §4.
2. **Not the spatial support.** The spatial radius is `supportScale`, exponential at exponent `7/2`; `scale_support` and `high_scaled_support` dilate a fixed ball by `ℓ`. Time width and spatial radius are different objects with different exponents, `7` and `7/2`; a claim about one is not a claim about the other.
3. **Not collapse to a point.** `activationTime` is strictly increasing while `horizonTime` is antitone, so intervals nest from both ends — but `common_positive_interval` proves `baseHorizon J X / 12 < horizonTime J X n`, so the intersection has positive length. Nesting keeps one common interval available; it does not squeeze it shut.

---

## 7. THE `Classical.choice` THAT SELECTS THE SCALE REGIME

The compression theorems of §6 are polymorphic in a scale record `S : Scales c B` and consume its `ActualBounds` field. That raises a question the local proofs cannot answer: does such a record actually reach the top-level theorem, or is the field merely asserted somewhere next to it?

The answer: the chain closes through a **single opaque selection** of the scale regime (E54). The lifespan is a second `choose`, downstream of that selection (`PacketFiniteLifespan.lean:54`), not a competing root.

### 7.1 The five links

1. **Existence.** `exists_scales`:

```
theorem exists_scales (c B : ℝ) (hc : 0 ≤ c) : Nonempty (Scales c B)
```

Its proof takes `exists_base_power`, then `exists_common_guards`, then assembles the record with `actual := hdata.1`. An `ActualBounds` witness is **produced**, for some `J, D, X, δ`, from nothing but `0 ≤ c`.

2. **Selection.** `constructionScales`:

```
noncomputable def constructionScales : ConstructionScales :=
  Classical.choice (exists_scales (requiredExponent : ℝ)
    (commonThreshold gradientConstant hessianConstant) (Nat.cast_nonneg _))
```

3. **Packets.** `packets n = stages constructionScales le_rfl le_rfl n`. The two reflexivity arguments discharge the `stages` hypotheses `requiredExponent ≤ q` and `commonThreshold ≤ B`, so neither is carried downstream.

4. **Datum and lifespan.** `initialDatum = Stage.initialDataLimit packets`; `lifespan = initialDatum_finite_lifespan.choose`, with `lifespan_le_base` bounding its duration by `baseHorizon constructionScales.J constructionScales.X`.

5. **Top level.** `initialDatum_singularity` and `exists_compact_smooth_euler_singularity`. `Euler.lean` is one line, `import Euler.EulerSingularity`, so that file is the root.

> **In human words.** One sealed envelope. All the numbers that set the scale — `J`, `D`, `X`, `δ` — are pulled out of a single envelope that is opened exactly once, and every packet inherits them. So the proof is logically closed: nothing is assumed. But nobody can read the numbers off the envelope. This is the same blindness as the constants, one level up: there it hid single numbers, here it hides the entire scale regime.

### 7.2 Where the compression is spent

Each `Stage` carries `source_stage : StageGuards …`, obtained from `Scales.stage`, which passes `S.actual` into `stage_guards_at` → `stage_guards` → `actualWidths_contract`. That is the only place `next_width` is proved.

`PacketStageRestriction.nextHorizon_lt` consumes it to place the next horizon strictly below the parent terminal time; without the halving that inequality does not close. The rest of the containment comes from `Stage.horizon_eq` (which reads `parent.T = time + 2 · timeWidth n`), `Stage.horizon_le` (`parent.T ≤ baseHorizon`), and `Scales.time_small` (`baseHorizon ≤ 1`). Together they keep every packet inside `[0,1]`.

### 7.3 Instrumental, not constitutive

The exact statement of `initialDatum_singularity` settles what the choice is **for**. It asserts smoothness at order `∞`, compact support, non-vanishing, vanishing divergence at every point, positive duration bounded by `1`, the equivalence "smooth solution at `T` ⟺ `0 < T < lifespan.duration`", a `C¹` limsup equal to `⊤`, and a maximal-vorticity integral equal to `⊤`.

Nothing in that list mentions `timeWidth`, `ActualBounds`, or any scale parameter. The halving is used **instrumentally**, to build the `packets` sequence whose limit the datum is; it is not a conjunct of the conclusion. So the chain closes in the construction and not in the statement — which is exactly why a reader who opens only `EulerSingularity.lean` cannot see it, and why the trace is worth writing down.

### 7.4 Logical closure, numerical opacity

Because `constructionScales` is a `Classical.choice`, the parameters `J, D, X, δ` have no computable content, and every downstream quantity — `timeWidth`, `scaleSequence`, `baseHorizon`, every frequency — is defined from that opaque witness.

The halving theorem is nevertheless **about the actual object**: every lemma is polymorphic in `S : Scales c B` and uses only fields, so nothing is assumed of a hypothetical record. What is lost is recoverability, not correctness: no explicit bound on the first width, on `J`, or on `baseHorizon` follows from the statement.

This is the barrier of §3 at a coarser grain. There the opacity sits behind individual constants; here it covers the whole scale regime — chosen once at the root, inherited by every packet. The difference is that this opacity is **structural rather than incidental**: the choice **is** the construction, and no rewriting of the proof would expose the witness without also exposing which witness was chosen.

Two side checks. First, the record's `delta_small` (`δ ≤ 1/16`) and `delta_geometry` (`10⁶ · geometryConstant · δ ≤ 1`) are stronger than the `δ ≤ 1/2` that `actualWidths_contract` needs, so the halving has slack. Second, `ActualBounds` has further producers, at `PacketSourceScaleActual.lean:230` and `PacketSourceScaleFromCosts.lean:70`; both are theorems, and no path enters `ActualBounds` as an axiom or a bare hypothesis.

Both questions this trace originally left open are now closed. The import path is four hops — `EulerSingularity` → `EulerC1Limsup` → `EulerC1Breakdown` → `EulerFiniteLifespan` → `PacketFiniteLifespan` — and `PacketFiniteLifespan` has exactly one direct importer inside the root reachable set, so the final edge is forced (E55). The chosen `D` does not constrain the derivative order: it enters `previousFrequency` only at index zero, as `X^D`, and every later term is free of `D`. Its one degrading effect is the index-zero instance of `neighborError`, which carries `X^{cD}` and is absorbed by enlarging `X`; there is no upper bound on `D` anywhere in `ActualBounds`, so no ceiling on the order follows (E56, corrected in E59 §3). The width argument never reads it.

---

## 8. CONCLUSION

### 8.1 The verdict

The logical integrity of the repo is robust. No axioms, no `native_decide`, no `unsafe`, no `partial`, no `implemented_by`, no reachable `sorry`; the exponent ledger is exact rational arithmetic; and the comparison theorem supplying the nonexistence conjunct is a genuine uniqueness result with nearly empty hypotheses — no pressure norm, no decay of `p − q` at infinity, no support, growth, or derivative condition on the competitor, Gronwall constant uniform in the localization radius by binder order, closure by an interior-derivative argument using `E(0) = 0` at a single point. That is not a proof padded into shape.

But the success is an achievement of **statement design**, not of fluid physics. The two findings mark what the artifact certifies:

1. **The Non-Evaluated Constant Barrier.** Every quantitative constant is `∃`-bound or `choose`n, so the kernel verifies existence and never size or dimension (§3). The headline theorem is constant-free, so it is not threatened; but no effective bound is extracted, and no machine check of dimensional consistency is possible.
2. **Anisotropic viscous scaling.** The Laplacian on the generalized cone is a sum of two homogeneous pieces, degrees `b − 1` (radial) and `b − 2D(h)` (axial), `2D(h) = 1 − 2h ∈ (0,1)`, differing by `2h`. Neither degree is the isotropic weight `b − 1` except at `h = 0`; no admissible member is isotropic; the axial term is the more damped (§4). The container `|z| < q^{D(h)}` absorbs the mismatch, through the measure factor `q^{1+D(h)}` and the `h`-dependent critical weight `b_*(h) = −(3−2h)/4`.

Both are one principle: the kernel audits arithmetic reflected into types and is silent about arithmetic that is not. A reader who takes "machine-checked" to mean "numerically and dimensionally reliable" is misreading the artifact — not because it is defective, but because that is not what type checking is.

A third observation is of another kind. The three seams of §5 need no separate boundary, matching, or corrector estimate: the pressure pairing has no boundary term at infinity because the test is compactly supported and the limit is taken on a vanishing bound; the time seam is a smooth scalar multiplier closed by a vanishing germ rather than a jet match; and the divergence defect of cutting is avoided by curling the cut potential, which keeps the commutator `∇χ × A` inside the velocity instead of correcting it away. None of the three appears as a constant, an exponent, or a hypothesis. **The seams of this construction are exact identities, and exactness is why the constant barrier never has to be crossed there.**

The construction side has its own ledger, traced in §6 and §7. Packet time widths halve by theorem, not hypothesis — `actualWidths_contract` derives `timeWidth (n+1) ≤ timeWidth n / 2` from a finite series total — with one conditional link, `horizonTime_antitone`, joined not inside its own file but through the `StageGuards.next_width` field. And the whole scale regime `J, D, X, δ` enters through a single `Classical.choice` at `PacketInfiniteConstruction.lean:68`, from which the packet family, the limiting datum, and its lifespan are all built. That root is why the final theorem can be constant-free in its statement while opaque in its construction: the compression is spent to build the object, and the object definition is the only place the witness is ever named.

> **In human words.** In one breath: the proof is honest and the clerk is honest. The gap is in what a clerk can be asked to do. It can check structure — that this line follows from that one, and that every case is covered. It cannot check size or shape: whether a constant is small enough, or whether an operator is the same in every direction. That is not a bug in Lean. It is a boundary of the job.

### 8.2 What the theorem says, in one sentence

A smooth compactly supported force can drive a fluid from rest to unbounded speed with no global finite-energy solution.

That is the data and the conclusion of alternative **(C)** of the Clay statement: zero is an admissible initial datum, and a smooth compactly supported force is stronger than Clay's rapid-decay requirement. **If the proof is correct, it resolves (C).** It does not establish the unforced alternatives (A) or (B), and the repo's own `force_nonzero_of_no_global_solution` is the formal witness that the result cannot be restated with `f ≡ 0` — which is exactly why it bears on (C) and not on (A). Whether the proof is correct, and how CMI evaluates it, are separate questions this audit does not decide.

### 8.3 Scope and limitations

We did not recompile. There is no Lean toolchain on the audit host, so every claim is by inspection of proof terms, binder sequences, and definitions — not by re-elaboration.

Independent kernel evidence exists for the artifact as a whole (nine external checkers are reported), but such evidence verifies **terms**, not **statements**; the statement-level caveats — zero datum, force-as-residual, similarity in `ν` — are exactly what kernel acceptance cannot test.

The derived identities of §4.4 (measure, `L²`, `b_*`) are ours, not the repo's, and are labelled as such. One log entry (E36, on `SchwartzCompactApproximation.continuous_zero_of_compactSupport`) is provisional: call site and approximation estimates verified, exact binder not opened. And the monotonicity claim of §3.2 — that every use of a constant is monotone in it — is a meta-argument about the scripts, not machine-checked.

### 8.4 Implications beyond this repository

Large formalizations of quantitative PDE estimates are becoming feasible, and this artifact previews their characteristic failure mode.

The kernel will faithfully audit the combinatorial and exponent-theoretic skeleton — where human error is most common and most damaging. It will **not** audit the two things a numerical analyst cares most about: the size of constants, and the homogeneity class of the operator.

If such developments are to support claims of the form "the constant is explicit" or "the estimate is dimensionally correct", those claims need to be reflected into the types — as explicit numerals, as rational bounds, or as homogeneity statements proved about the pullback. Otherwise no amount of compilation bears on them.

---

## APPENDIX A. ARTIFACT INDEX

All paths relative to commit `f9e8bc5`. Every row of the paper index, in the same order.

| Path | Declaration | Where it is used |
|---|---|---|
| `R3/ProblemStatement.lean` | `breakdownStatement` | §1.2 |
| `R3/ProblemStatement.lean` | `CandidateProperties` | §1.2 |
| `R3/Theorem.lean` | `theorem_1_1_with_initial_rest` | §1.2 |
| `R3/Theorem.lean` | `theorem_1_1` | §1.3, §3.3 |
| `R3/CandidateBreakdown.lean` | `force_nonzero_of_no_global_solution` | §1.3, §5.2 |
| `R3/WholeSpaceUniqueness.lean` | `classical_uniqueness_on_Icc` | §1.3, §5.1 |
| `R3/WeightedSobolev.lean` | `sobolevConstant`, `lpNorm_six_le`, `weightedSobolevConstant` | §3.1 |
| `R3/LocalizedFluxEstimates.lean` | `exists_weight_second_derivative_bound`, `weightSecondDerivativeConstant` | §3.1 |
| `R3/PressureFunctionals.lean` | `averagedPressureDifferenceValue_bound`, `averagedPressureDifference_bound` | §3.1 |
| `ExponentLedger.lean` | `particularGain`, `particular_gain_eq`, `manuscript_kappa_admissible` | §3.4 |
| `CoordinateAlgebra.lean` | `D`, `d`, `L`; `timeCoeff`, `axialCoeff` | §4.1, §4.2 |
| `SimilarityCoordinates.lean` | `coordinateQ`, `coordinateEta`, `coordinateX` | §4.1 |
| `SimilarityHomogeneity.lean` | `coordinateQ_scale_h` and the three coordinate scalings | §4.1 |
| `SimilarityProfile.lean` | `pullback`, `partialS_pullback`, `partialZ_pullback` | §4.2 |
| `SimilarityProfile.lean` | `partialS_partialS_pullback`, `partialZ_partialZ_pullback` | §4.2 |
| `PeriodicLocalization.lean` | `innerCube` | §2 |
| `PeriodicResidualLimits.lean` | `periodicResidual_jets_eq_cut` | §2 |
| `R3/ComparisonRateBound.lean` | `exists_uniform_rate_bound` | §1.3, §5.1 |
| `SpatialLocalization.lean` | `cutPotential`, `cutVelocity`, `periodicVelocity` | §5.3 |
| `SpatialLocalization.lean` | `spatialDivergence_spatialCurl_on`, `periodicVelocity_eventuallyEq` | §5.3 |
| `TimeLocalization.lean` | `activatedVelocity`, `activatedPressure` | §5.2 |
| `R3/PositiveTimeForce.lean` | `force`, `force_eq`, `force_contDiff` | §5.2 |
| `R3CompactCandidate.lean` | `compactForce_smooth` | §5.2 |

---

## APPENDIX B. NON-CLAIMS

So nobody misquotes the cave. This paper does **not** claim, and its evidence does **not** support, any of these:

1. That the repo is unsound, hides an axiom, or proves something false. The verifications point the other way.
2. That Lean or Mathlib is to blame for the statement-design choices. The same theorem written in prose would meet the same objections, and the kernel did exactly what it was told.
3. That the comparison theorem is weak or circular. It is, in our view, the strongest part of the development, and its hypotheses are close to minimal.
4. That the anisotropy of §4 is a bug in the code. The identities are correct; the finding is that an isotropic reading of the viscous term is incompatible with them.
5. That the whole repo is 641,332 lines of comparison argument. That is the whole tree; the comparison chain is a small fraction, and we do not pin the total on any single module.

---

## WHERE TO LOOK (the paper bibliography, in caveman)

- **The repo itself**: OpenAI, `NavierStokesAndEuler`, commit `f9e8bc5`.
- **This audit**: A. El Sayad and John, the audit log, entries E0–E67.
- **Lean 4**: de Moura and Ullrich, CADE-28, 2021.
- **Mathlib**: the Mathlib community, CPP 2020.
- **Leray 1934**: the original weak-solution construction for viscous flow in all of space.
- **Hopf 1951**: the initial-value problem for the hydrodynamic equations.
- **Kato 1984**: strong `L^p` solutions, and applications to weak ones.
- **Beale–Kato–Majda 1984**: how smooth 3D Euler solutions break down.
- **Caffarelli–Kohn–Nirenberg 1982**: partial regularity of suitable weak solutions.
- **Fefferman 2006**: the official Clay problem statement.

---

## COVERAGE MAP — PROOF THIS IS 1:1

Every unit of the paper, and where it is handled here.

| Paper unit | Subsections | Here |
|---|---|---|
| §1 Introduction | 6 | §1, all six |
| §2 Preliminaries: notation and the two spaces | 1 | §2, both facts plus 2.1 |
| §3 The Non-Evaluated Constant Barrier | 5 | §3, all five |
| §4 Anisotropic Viscous Scaling | 5 | §4, all five |
| §5 Three interface audits | 3 | §5, all three |
| §6 Packet time-width compression | 5 | §6, all five |
| §7 The `Classical.choice` that selects the scale regime | 4 | §7, all four |
| §8 Conclusion | 4 | §8, all four |
| Appendix A Artifact index | — | Appendix A, every row |
| Appendix B Non-claims | — | Appendix B, all five |
| Bibliography | 10 entries | Where to look, all ten |

**33 of 33 subsections. 8 of 8 body sections. 2 of 2 appendix sections. 10 of 10 bibliography entries.**

Nothing in the paper is skipped here. What is *added* is only caveman phrasing, plus the arithmetic in §6.3 that the paper states in words (`horizonTime (n+1) ≤ horizonTime n − timeWidth n / 3`), which is a restatement of constants already in the text, not a new claim.

**Reading aids.** The START HERE block, the reading paths, the glossary and the `In human words` boxes are aids for human readers. They add no claims. The 33 subsections above are unchanged, and every one of them still corresponds to exactly one subsection of the paper.

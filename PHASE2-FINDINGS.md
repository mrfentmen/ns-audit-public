# Phase II forensic payload — `openai/NavierStokesAndEuler` @ `f9e8bc5`

Seven tasks (A.1–A.3, B.1–B.2, C.1–C.2). Verdicts: **3 answered as posed, 3 with a false
premise, 1 vacuous by dependency.** No declaration was guessed; every line number below was
read at this commit.

---

## 0. Schema map (with corrections to the expected paths)

| Task | Expected path | Actual location of the mechanism |
|---|---|---|
| A.1 Riesz / boundary | `R3/WholeSpaceUniqueness.lean` | **correct**, plus `R3/PressureFlux.lean:576`, `R3/WholeSpaceComparisonClosure.lean:32`, `R3/ComparisonRateBound.lean:127`, `R3PressureFourier.lean` (symbol) |
| A.2 lattice sum | `PeriodicLocalization.lean`, `PeriodicResidualLimits.lean` | **correct**, but the *fields* are cut in `SpatialLocalization.lean:165–218`; `PeriodicResidualLimits.lean:138` is the jet upgrade |
| B.1 temporal margin | `R3/Theorem.lean` | **wrong**: `Theorem.lean:26` only *calls* the candidate. Mechanics in `TimeLocalization.lean:27–31` + `R3/PositiveTimeForce.lean:21–63` + `R3/ActualCandidate.lean` |
| B.2 residual smoothness | `R3/CandidateBreakdown.lean` | **wrong**: that file proves no smoothness of `f`. `R3CompactCandidate.lean:90` + `R3/PositiveTimeForce.lean:49` |
| A.3 weights | `R3/WeightedSobolev.lean` | **correct**; `R3/PressureFunctionals.lean:169,279` |
| C.1/C.2 corrector | `PeriodicResidualLimits.lean` | **wrong**: no corrector exists anywhere. Divergence-freeness from `SpatialLocalization.lean:165–172,258` |

---

## 1. GROUP A — pressure non-locality and spatial decay

### A.1 — there is no boundary term to make vanish

**Location.** `NavierStokes/R3/WholeSpaceUniqueness.lean:30`,
`classical_uniqueness_on_Icc`.

**Binder sequence & type signature** (verbatim):

```lean
theorem classical_uniqueness_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x)
```

Binder order: implicit `{T}` → `(hT : 0 < T)` → implicit `{u v p q K}` → the ten explicit
hypotheses → conclusion `∀ t ∈ Icc 0 T, ∀ x`. **There is no `∃` in the statement**, so no
existential can be hiding a remainder.

**Algebraic analysis.** The question asked whether the infinity term vanishes through a
checked algebraic decay constraint (e.g. `1/|x|^3`) or through a qualitative boundary
predicate concealing remainders in a noncomputable existential.

Neither. `p − q` occurs only against `∇χ_R`:

  ∫_{ℝ³} (p − q) ∇χ_R · w

and `χ_R` is compactly supported for every finite `R`, so **no integral over ∂B_R is ever
written**. There is no integrand at infinity to estimate, hence no decay constraint, hence
no `1/|x|^3` lemma to find. What replaces decay is:

- `hsupp`: compact spatial support of the **reference** `u` only;
- `hev`: `UniformFiniteEnergy` of the competitor `v` — the sole quantitative input on `v`.

The reference's own finite energy is *derived*, not assumed:
`CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab hu hK hsupp`.

The `R → ∞` limit is taken on a **bound**, not on an integral identity.
`R3/ComparisonRateBound.lean:127`:

```lean
theorem exists_uniform_rate_bound {C0 C1 C2 S M : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∃ D ≥ 0, ∀ R ≥ 1, ∀ A ≥ 0, ∀ B ≥ 0, B ≤ S * (A + M / R) →
      ∀ E E' G : ℝ,
        (1 / 2 : ℝ) * E' + A ^ 2 ≤ G * E + C0 / R ^ 2 +
          C1 / R * B ^ (3 / 2 : ℝ) +
          C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
            R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) →
        E' ≤ 2 * G * E + D / R
```

Binder order is the decisive detail: `∃ D ≥ 0` is **closed before** `∀ R ≥ 1`. `D` cannot
depend on `R`. Every remaining `R`-dependence is explicit and decays: `C0/R²` (degree −2),
`C1 R⁻¹ B^{3/2}` (degree −1), `C2[…+R^{-7/4}B^{3/4}]` (degrees −1 and −7/4). The conclusion
`E' ≤ 2GE + D/R` tends to `E' ≤ 2GE`, and
`WholeSpaceComparisonClosure.eq_of_pressure_flux_bound` (`:32`) then drives `‖w(t)‖₂² → 0`
by dominated convergence. Pressure is annihilated up to a constant by `∇·w = 0`.

**Verdict.** No vulnerability. The dichotomy in the task is false: the term is never formed.
A decay lemma would be dead code, which is why none exists.

---

### A.2 — germ equality, not a gradient identity

**Location.** `NavierStokes/SpatialLocalization.lean:210–218, 258–282`;
`NavierStokes/PeriodicResidualLimits.lean:138`.

**Binder sequence & type signature** (verbatim):

```lean
theorem periodicPressure_eventuallyEq_cut (p : PressureField) {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicPressure p =ᶠ[𝓝 z] cutPressure p
```

```lean
theorem periodic_residual_eventuallyEq_cut (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    (fun w => navierStokesResidual (periodicVelocity A) (periodicPressure p) w.1 w.2)
      =ᶠ[𝓝 z] (fun w => navierStokesResidual (cutVelocity A) (cutPressure p) w.1 w.2)
```

```lean
theorem periodicResidual_jets_eq_cut (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) (n : ℕ) :
    iteratedFDeriv ℝ n (periodicResidual A p) z =
      iteratedFDeriv ℝ n (cutResidual A p) z
```

`innerCube r := {x | ∀ i : Fin 3, |x i| < 1 - r}` (`PeriodicLocalization.lean:213`), so
`innerCube (1/4) = (−3/4, 3/4)³`.

**Algebraic analysis.** The task asked for the proof that `∇p_{𝕋³}` matches the cut
physical gradient on the inner cube, and whether `[∇, χ]` is actively bounded or hidden in a
germ identity.

The premise is again false in the repository's favour. The code **never asserts**
`∇(Σ_k χ p(·+k)) = Σ_k χ ∇p(·+k)`, which is false as soon as `∇χ ≠ 0`. It proves the
stronger statement that the two *functions* agree on a neighbourhood of each point of
`innerCube(1/4)`. Equal functions on a neighbourhood have equal iterated derivatives, which
is exactly what `iteratedFDeriv_eventuallyEq … .self_of_nhds` extracts. So gradient
agreement is a *corollary*, not a hypothesis, and `[∇, χ]` requires no bound anywhere.

Where `[∇, χ]` would actually matter, it vanishes identically: on
`plateau := {x | radialSquare x < 1/32 ∧ |x 2| < 1/8}` (`:134`) one has `χ ≡ 1`, hence
`∇χ = 0`, and `periodicVelocity_eventuallyEq` (`:318`) upgrades the identity to the *uncut*
field `periodicVelocity A =ᶠ spatialCurl A`. No non-local leakage: the lattice sum is
locally finite (`periodicPotential_locally_finite`, `:219`) and each translate is supported
in a cube of radius `1/4`, strictly inside the `3/4` margin, so no two translates overlap
on the cube.

**Verdict.** No vulnerability. "Relies entirely on a localized germ identity" is accurate
but is a strength, not an evasion: the germ identity is stronger than the derivative
identity it is used to obtain.

---

### A.3 — no decay weights exist (premise false)

**Location.** `NavierStokes/R3/WeightedSobolev.lean:25, 42, 210` (read in full);
`R3/PressureFunctionals.lean:169, 279`.

**Binder sequence & type signature** (verbatim):

```lean
theorem lpNorm_six_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : Space → E} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    comparisonLpNorm 6 f ≤ sobolevConstant * comparisonLpNorm 2 (fderiv ℝ f)
```

```lean
theorem weighted_sobolev {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ 1 w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L) :
    comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ≤ weightedSobolevConstant *
      (Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) + L * comparisonLpNorm 2 w)
```

Note the binder order: the cutoff derivative bound `L` is an **input**, not an output; the
constant `weightedSobolevConstant := 4 * sobolevConstant + 1` is fixed (`:210`).

**Algebraic analysis.** Dimension check. `[S] = 1`: the Sobolev constant is dimensionless,
since `‖f‖₆` and `‖∇f‖₂` both carry `L^{3/2}T^{-1}`. For the weighted estimate each of the
three terms carries `L^{3/2}T^{-1}`:
`‖w‖₆` by the same homogeneity; `√(∫φ⁸|∇w|²)` as `(T^{-2}·L³)^{1/2}`; and `L‖w‖₂` because
`L` bounds `‖∇φ‖` and hence has dimension `L^{-1}`, so `L^{-1}·L^{5/2}T^{-1}`. The constant
`weightedSobolevConstant = 4S + 1` is dimensionless. Consistent, with no hidden length scale.

The substantive point: **there is no `1/|x|^3` and no Riesz kernel in this file.** The
weights are `χ⁴` (velocity) and `χ⁸` (dissipation) — both *localising*, not decaying. The
file header states the estimate is local and needs only `L²` of the unweighted velocity. So
the comparison the task asks for cannot be made: there is no decay order to compare against.
Nothing is hidden in an existential either; `sobolevConstant` carries magnitude, not order,
and the E26 barrier therefore bites only on magnitude.

**Verdict.** Premise corrected. No hidden remainder; no decay bookkeeping to audit.

---

## 2. GROUP B — temporal interface at `t = 3/8`

### B.1 — a scalar multiplier, not a branch

**Location.** `NavierStokes/TimeLocalization.lean:27–31`; the composition lemma at `:33`.

**Binder sequence & type signature** (verbatim):

```lean
def activatedVelocity (u : VelocityField) : VelocityField :=
  fun z => timeSwitch z.1 • u z

theorem activatedVelocity_smooth (u : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) :
    ContDiffOn ℝ ∞ (activatedVelocity u) preSingularDomain
```

**Algebraic analysis.** The task offered two options: an explicit `ContDiff ℝ ⊤` indicator
across the interface, or an `if-then-else` that side-steps jet matching.

The answer is the *first* — `ContDiffOn ℝ ∞`, with `∞ = ⊤` — and there is no branch. The
multiplier is scalar and depends on `t` alone, so smoothness is inherited by closure of
`C^∞` under multiplication: `(timeSwitch_contDiff.comp contDiff_fst).contDiffOn.smul hu`.
The two sides agree not because the multiplier is constant but because the **field vanishes
on the early slab**: `activatedVelocity_zero_early` and `activatedPressure_zero_early` give
`u = p = 0` for `|t| ≤ 3/8`, whence `localized_residual_zero_early` gives a vanishing
residual there. The equation is then closed by `by_cases hearly : t < 3/8` in
`R3/ActualCandidate.lean`: early side uses the vanishing residual and `force_eq_zero`; late
side uses `PositiveTimeForce.force_eq ⟨le_of_not_gt hearly, ht.2.le⟩`.

Consequently full jet matching at the boundary point holds trivially — every jet of the
zero germ is zero on both sides — without any jet ever being computed.

**Verdict.** No vulnerability. No conditional; no side-stepped match.

---

### B.2 — the named file proves no smoothness of `f` (premise false)

**Location.** `NavierStokes/R3/CandidateBreakdown.lean` (4 declarations, none about
smoothness); actual location `NavierStokes/R3CompactCandidate.lean:88–92` and
`NavierStokes/R3/PositiveTimeForce.lean:46–63`.

**Binder sequence & type signature** (verbatim):

```lean
theorem compactForce_smooth {f : VelocityField} (hf : ContDiffOn ℝ ∞ f futureDomain) :
    ContDiffOn ℝ ∞ (compactForce f) futureDomain
```

```lean
theorem force_contDiff {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (force f)
```

```lean
theorem force_tsupport_subset {f : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hf : ∀ t x, x ∉ K → f (t, x) = 0) :
    tsupport (force f) ⊆ Icc (1 / 16 : ℝ) (21 / 16) ×ˢ K
```

**Algebraic analysis.** No `∂_t^k f` is evaluated anywhere at `t = 3/8`, and no `norm_num`
appears at the interface. Both smoothness proofs are one-liners of the form "smooth cutoff
composed with a projection, multiplied by a smooth field":

- `(outerCutoff_smooth.comp contDiff_snd).contDiffOn.smul hf`
- `(timeCutoff_contDiff.comp contDiff_fst).smul hf`

The time support is **bounded away from the junction** rather than asserted at it:
`tsupport ⊆ [1/16, 21/16] × K`, which is what discharges `CompactPositiveTimeSupport`
(needs `tsupport ⊆ {t > 0}`, satisfied since `1/16 > 0`).

`CandidateBreakdown.lean`'s actual four declarations are
`CandidateProperties.not_global_agreement`, `no_global_solution_one`,
`force_nonzero_of_no_global_solution` (`:53`), `uniform_l2_sq_bound`.

**Verdict.** Premise corrected. Smoothness is inherited from algebraic closure of `C^∞`, and
the interface is never a distinguished point in any proof.

---

## 3. GROUP C — divergence-free cutoff corrections

### C.1 — no corrector, because nothing diverges

**Location.** `NavierStokes/SpatialLocalization.lean:165–172` (cut), `:258–262` (divergence).

**Binder sequence & type signature** (verbatim):

```lean
noncomputable def cutPotential (A : VelocityField) : VelocityField :=
  fun z => spatialCutoff z.2 • A z

noncomputable def cutVelocity (A : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (cutPotential A)
```

```lean
theorem periodicVelocity_divergence_free {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) {t : ℝ}
    (ht : t ∈ times) (x : Space) : spatialDivergence (periodicVelocity A) t x = 0
```

**Algebraic analysis.** The task presupposes a corrector field resolving
`∇·(χu) ≠ 0`. No such field exists, because the cut is applied to the **potential**, not the
velocity:

  u_cut = ∇×(χA) = χ ∇×A + ∇χ×A.

The left-hand side is a curl, so `∇·u_cut = 0` identically
(`SpatialCurl.spatialDivergence_spatialCurl_on`). The defect `∇·(χu)` is never formed, so
there is nothing to correct.

The commutator is not removed; it is **retained inside the velocity** as the second term
`∇χ×A`, supported in `supportCylinder ∖ plateau`
(`supportCylinder := {x | radialSquare x ≤ 1/16 ∧ |x 2| ≤ 1/4}`, `:72`;
`plateau` at `:134`). This is why the cut velocity is exactly divergence-free while being
only germ-equal to `χ ∇×A`.

**Exponent tracking.** The corrector's spatial derivatives would carry similarity powers of
`q` only if the corrector were a similarity-space object. It is not: `χ` is a fixed physical
cutoff, and `∇χ×A` is a *spatial-support* term, bounded by `‖∇χ‖ ‖A‖`. It therefore
consumes no power of `q`, and nothing in `ExponentLedger.lean` can be missing it. The two
bookkeepings — similarity weight `q^b` and physical support `χ` — are independent
decompositions and do not interact through a single exponent.

**Verdict.** Premise corrected. No corrector, no missing exponent, no conflict with the
ledger.

---

### C.2 — vacuous by dependency

**Location.** None: the object does not exist (C.1).

**Binder sequence & type signature.** N/A.

**Algebraic analysis.** With no corrector there is no corrector residual. It is therefore
neither added to `f` nor majorised by an existential constant: the disjunction in the task
has no true branch because the subject is absent. The force remains the exact residual of the
fields actually used (established in log E10.6, correcting E9.4), and `navier_stokes` holds by
case split, not by estimate.

**Verdict.** N/A. No vulnerability; the question dissolves.

---

## 4. Manuscript Markdown patch

The three LaTeX subsections are already written into `ns-audit/MANUSCRIPT.tex` (§5,
labels `sec:riesz-decay`, `sec:temporal-bump`, `sec:divergence-corrector`). The blocks below
are the paste-ready Markdown form of the same findings, for the log or co-author notes.

### § `sec:riesz-decay`

```markdown
#### Pressure non-locality: no boundary term is formed

`classical_uniqueness_on_Icc` (`R3/WholeSpaceUniqueness.lean:30`) has **no surface integral
to make vanish**. Pressure appears only against `∇χ_R`, and `χ_R` is compactly supported for
every finite `R`, so `∫_{∂B_R}` is never written. No decay hypothesis
(`lim ∫_{∂B_R} p (w·n) = 0`) and no support predicate on the competitor: the reference `u`
has compact support (`hK`, `hsupp`), the competitor `v` has only `UniformFiniteEnergy`.
The reference's finite energy is *derived* (`uniformFiniteEnergy_of_compact_slab`).

The `R → ∞` limit is taken on a bound. `exists_uniform_rate_bound`
(`R3/ComparisonRateBound.lean:127`) closes **`∃ D ≥ 0` before `∀ R ≥ 1`**, so `D` cannot
depend on `R`; the remaining explicit terms are `C₀/R²`, `C₁R⁻¹B^{3/2}` and
`C₂[(B^{1/2}+1)(A/R+R⁻²) + R^{-7/4}B^{3/4}]`, all vanishing. The conclusion
`E' ≤ 2GE + D/R` gives `E' ≤ 2GE` in the limit, and `eq_of_pressure_flux_bound` closes by
dominated convergence. Pressure is annihilated up to a constant by `∇·w = 0`.
```

### § `sec:temporal-bump`

```markdown
#### Temporal margin: a scalar multiplier, no branch, no jet

No `if-then-else`, no interval delegation, no derivative evaluated at `t = 3/8`.
The junction is `timeSwitch(t) • u` (`TimeLocalization.lean:27`), and smoothness is
`ContDiffOn ℝ ∞` inherited by closure of `C^∞` under multiplication:
`(timeSwitch_contDiff.comp contDiff_fst).contDiffOn.smul hu`.

The two sides agree because the *field* vanishes early, not because the multiplier is
constant: `activatedVelocity_zero_early` / `activatedPressure_zero_early` give `u=p=0` for
`|t| ≤ 3/8`, hence `localized_residual_zero_early`, and the equation closes by
`by_cases t < 3/8`.

`CandidateBreakdown.lean` contains **no** smoothness proof of `f`. Force smoothness is
`compactForce_smooth` (`R3CompactCandidate.lean:90`) followed by `force_contDiff`
(`R3/PositiveTimeForce.lean:49`), both one-line `smul` closures. Time support is bounded
away from the junction, not asserted at it: `tsupport ⊆ [1/16, 21/16] × K`
(`force_tsupport_subset`).
```

### § `sec:divergence-corrector`

```markdown
#### Torus interface: no corrector exists

The cut is applied to the potential, not the velocity:
`cutVelocity A := ∇×(χ A)` (`SpatialLocalization.lean:171`), so
`∇·(χu) ≠ 0` never arises and no corrector is introduced — confirmed by
`periodicVelocity_divergence_free` (`:258`) through
`spatialDivergence_spatialCurl_on`.

The commutator is not cancelled, it is *carried*:
`∇×(χA) = χ ∇×A + ∇χ×A`. The second term is `[∇,χ]` itself, supported in
`supportCylinder ∖ plateau` and retained inside the field. That is why the cut velocity is
exactly divergence-free while being only germ-equal to `χ ∇×A`.

Consequences: `ExponentLedger.lean` has no corrector entries to be missing, since the
commutator is a spatial-support term (`‖∇χ‖‖A‖`), not a similarity-weight term — it consumes
no power of `q`. And no corrector residual is added to `f` or hidden in an existential,
because there is none.
```

---

## 5. Verification status

- All line numbers read at `f9e8bc5`; none inferred.
- No `elan`/`lean`/`lake` on this host: **not re-elaborated**. Claims are from proof terms and
  binder order.
- `AUDIT_LOG.md` E48 records the same seven findings (appended, E0–E47 untouched).
- `MANUSCRIPT.tex` 1,217 lines; structural check passes (environments, refs, labels, braces,
  `$` parity). Not compiled: no TeX engine.

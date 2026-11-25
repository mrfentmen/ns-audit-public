# PROOF STEPS — the paper's argument, one inference at a time

**Status: first complete pass over the sixteen steps that carry Theorem 1.1 and every row the
ledger already calls partial.** Reading only. Nothing in this file was compiled, and no Lean
proof was re-run. The companion answers a narrower question than `CROSSWALK.md`:

> `CROSSWALK.md` asks whether a declaration exists whose **statement** is the paper's.
> This file asks whether the paper's **inference** from one statement to the next is valid,
> and which declaration consumes it.

It is possible to answer yes to the first and no to the second. That is why the two files are
separate.

> **Current verdict: no mathematical defect has been established.** The sixteen steps split
> 8 `exact`, 2 `composition`, 5 `partial`, 1 `inexpressible`, 0 `defect`. The partials are
> category 2 — missing declarations, compositions or syntax — not false inferences. The
> defect ledger at the end names what would change that.

## Verdict key

| Verdict | Meaning |
|---|---|
| `exact` | A declaration states the paper's claim, clause for clause. The proof of that declaration was not recompiled. |
| `composition` | The step is valid only when two or more declarations are composed. The composition is named; it is not one theorem. |
| `partial` | At least one clause of the paper's claim has no declaration. The missing clause is named. |
| `inexpressible` | The clause is a fact about the proof's syntax, and the development has no object-language proposition for it. |
| `unread` | Not audited. |
| `defect` | A stated inference is false on its own terms. **None has been established.** |

The distinction that matters throughout:

1. **A code fact** — a declaration with this statement exists (`cross_product_zero`, `theorem_1_1`).
2. **A formalization limit** — the paper proves the clause, but the tree does not state it
   (the map `f_m ↦ (t_m, π_m)`, the support of the limit tensors).
3. **A mathematical error** — a false estimate, a wrong exponent, or an invalid inference in
   the paper. The audit has not established one.

A `partial` row is category 2 unless its named clause is itself false. None of the five
partials is in that position.

## The chain, as the paper states it

```
Theorem 1.1  (ns.txt:29)
  ├─ Proposition 10.1  localization of the local field        (ns.txt:5955)
  │    └─ Proposition 9.9  summed local field                 (ns.txt:5794)
  │         ├─ Proposition 9.3  one correction cycle          (ns.txt:5272)
  │         │    ├─ Lemma 9.7  one common domain               (ns.txt:5669)
  │         │    ├─ Lemma 9.8  stage-independent jet losses    (ns.txt:5734)
  │         │    ├─ Lemma 6.1  disjoint lifted slots           (ns.txt:3392)
  │         │    ├─ Lemma 6.2  common-torus representation     (ns.txt:3462)
  │         │    ├─ Proposition 7.2  driven amplitude          (ns.txt:3992)
  │         │    ├─ Corollary 7.3  one threshold for all maps  (ns.txt:4114)
  │         │    └─ Proposition 7.6  linearized amplitude map   (ns.txt:4317)
  │         └─ Proposition 5.3  base residual rate             (ns.txt:2874)
  ├─ Lemma 10.2  derivative limits of the force               (ns.txt:5997)
  ├─ Lemma 10.3  compact smooth force extension                (ns.txt:6071)
  ├─ Lemma 10.4  uniform energy and finite dissipation         (ns.txt:6115)
  └─ Lemma 10.5  whole-space comparison                        (ns.txt:6143)
```

The arrows are the paper's. They are not all Lean dependencies: the tree sometimes builds a
consumer that takes the producer as a hypothesis, and sometimes states the producer and the
consumer in one structure. The “Lean consumer” line in each step says which.

---

## Step 1 — Theorem 1.1

**Paper.** `Theorem 1.1` (`ns.txt:29`): for every `ν > 0` there are `f ∈ C_c^∞(ℝ³ × (0,∞); ℝ³)`,
a compact `K`, and smooth `u, p` on `ℝ³ × [0,1)` with

```
∂_t u + (u·∇)u − νΔu + ∇p = f,   div u = 0,   u(·,0) = 0,
supp u(·,t) ∪ supp p(·,t) ⊂ K   (0 ≤ t < 1),
sup_{0≤t<1} ‖u(t)‖_{L²} < ∞,   limsup_{t↑1} ‖u(t)‖_{L∞} = ∞.
```

Consequently no smooth global solution with the same force and zero datum has uniformly
bounded kinetic energy.

**In plain terms.** One force, one compact box, one flow that exists up to time one, never
leaves the box, keeps finite energy, and whose speed becomes arbitrarily large as time
approaches one. Because the energy stays finite, the failure is not an energy blow-up; the
solution simply cannot be continued smoothly past time one.

**Hypotheses.** None beyond `ν > 0`. The force, box and fields are conclusions, not inputs.

**What the paper does.** It constructs the fields in §§4–9, localizes them in §10.1, extends
the force through time one in §10.2, proves the energy bound in §10.3, and excludes a global
finite-energy competitor by the comparison argument of Lemma 10.5. The periodic sentence at
the end is Corollary 10.6, not a sixth clause of the theorem.

**Lean.** `R3/ProblemStatement.lean:150` defines `breakdownStatement` with the five clauses;
`R3/Theorem.lean:46` proves it as `theorem_1_1`. The five clauses map field for field:

| Paper clause | Lean field |
|---|---|
| `f` smooth, compactly supported in `t > 0` | `CandidateProperties.force_smooth`, `force_support` |
| `K` compact | `support_compact` |
| `u, p` smooth on `[0,1)` | `velocity_smooth`, `pressure_smooth` |
| PDE, divergence, zero datum | `navier_stokes`, `divergence_free`, `zero_initial_velocity` |
| supports in `K` for `0 ≤ t < 1` | `velocity_support`, `pressure_support` |
| finite `L²` sup | `energy_bounded` |
| `limsup` of `L∞` is `∞` | `speed_unbounded` |
| no global finite-energy solution | `¬ Nonempty (GlobalFiniteEnergySolution ν f)` |

**Two closure notes, not gaps.** The paper writes the PDE at `t = 0`; the Lean field imposes it
only on `0 < t < 1`. The residual is continuous on the closed half-domain because `u, p` are
`C^∞` there and `f` is smooth, so the `t > 0` identity extends to `t = 0` by continuity. The
paper writes `limsup ‖u(t)‖_{L∞} = ∞`; the Lean field is pointwise unbounded in every left
neighbourhood. For a continuous slice supported in compact `K`, `‖u(t)‖_{L∞}` is its spatial
supremum, so the two are equivalent.

**Does the inference follow?** `exact` at statement level. The theorem is not asserted by a
structure or an axiom: `theorem_1_1` is a proof term. Its proof was not recompiled here.
The periodic corollary is separately placed as Corollary 10.6.

---

## Step 2 — Proposition 10.1, localization

**Paper.** `Proposition 10.1` (`ns.txt:5955`): there are compact `K`, smooth `u, p` on
`ℝ³ × [0,1)`, supported in `K`, with `div u = 0`, `u = p = 0` for sufficiently small
`t ≥ 0`, agreeing with `u_loc, p_loc` near the origin for times close to one.

**In plain terms.** Cut the local field off in space and time. The spatial cutoff is applied
**before** the curl, so the cut velocity is still divergence-free; the price is the extra
`∇c × A` term, which stays inside `u` rather than disappearing.

**Hypotheses.** The local field of §9 and the fixed local domain `Ω* = {τ > 0, q < q*}`.

**What the paper does.** Picks `τ₀, z₀` with `q ≤ q*/2` on the cutoff support, chooses
`c = χ_x(x)χ_t(t)`, sets `u = curl(cA) + cB e_θ`, `p = c p_loc`, and extends by zero. Then
`div u = div curl(cA) + r^{-1}∂_θ(cB) = 0`.

**Lean.** `PaperLocalization.lean` proves `local_theorem_with_compact_candidate`, which
returns the local `Properties`, the compact `CandidateProperties`, the no-global-solution
clause, the short-time vanishing, and the agreement on a neighborhood of the origin — all for
the same fields. The short-time clause is stronger than the paper's: `|t| ≤ 3/8`.

**Does the inference follow?** `exact`, and stronger on the short-time clause. The
divergence-free cutoff identity is the paper's `div curl = 0` step, not an added hypothesis.
No `∇c × A` correction field is hidden: it is part of the defined `u`.

---

## Step 3 — Lemma 10.2, force derivative limits

**Paper.** `Lemma 10.2` (`ns.txt:5997`): for every spatial multi-index `α` and `j ≥ 0`,
`∂_x^α ∂_t^j f` converges uniformly on `ℝ³` as `t ↑ 1`; there are
`F_j ∈ C_c^∞(ℝ³; ℝ³)`, supported in `K`, with

```
lim_{t↑1} ∂_x^α ∂_t^j f(x,t) = ∂_x^α F_j(x),   ∂_x^α F_j(0) = 0.
```

**In plain terms.** Every derivative of the force has a limit at the terminal time, the limits
fit together as spatial derivatives of smooth compactly supported functions, and every one
vanishes at the origin.

**Hypotheses.** The localized force of (10.5), the flat residual (3.4), and the endpoint
bounds of Theorem 3.1(ii).

**What the paper does.** Away from the origin, Theorem 3.1(ii) bounds every derivative
uniformly, so each derivative is uniformly Cauchy. Near the origin, (3.4) gives
`|∂^α∂^j f| ≤ C(τ + |z|^{1/D})^N`; a small ball plus a finite cover gives uniform convergence
and vanishing at the origin. The fundamental theorem of calculus identifies the limits and
gives (10.10).

**Lean.** `JointResidualLimits` constructs the locally uniform joint limits; `LocalResidualFlatness`
supplies the flat residual tower; `SpacetimeEndpoint.boundary_tensors_contDiff` derives
smoothness of the boundary coefficient functions. E66 traces `hlim` through
`StageEstimates → exists_schedule_all_jetRates → VanishingJointJets → boundaryLimits_locallyUniform`.
The derivative limits are constructed, not assumed.

**Does the inference follow?** `partial`. The convergence and compatibility clauses have
declarations. The support clause — `F_j ∈ C_c^∞(ℝ³; ℝ³)` with support in `K` — has no single
declaration for the limit tensors (E150). This is category 2: the paper proves it (the limits
vanish off `K` because every `f(·,t)` does), but the tree does not state it as one theorem.
It is not evidence that the paper's step is false.

---

## Step 4 — Lemma 10.3, smooth compact force extension

**Paper.** `Lemma 10.3` (`ns.txt:6071`): the force in (10.5) extends to
`f ∈ C_c^∞(ℝ³ × (0,∞); ℝ³)`, with support in `K × [0,2]`.

**In plain terms.** The force is known only before time one. Glue a smooth continuation on the
other side, using the derivative limits as Taylor coefficients, with cutoff widths shrinking
fast enough that every derivative series converges. The result is compactly supported in time.

**Hypotheses.** Lemma 10.2's `F_j`, and the zero force near `t = 0`.

**What the paper does.** Sets
`f(x,1+σ) = Σ_j χ₀(b_jσ) σ^j/j! F_j(x)`, chooses `b_j` increasing so that the `j`-th block is
at most `2^{-j}` in every derivative up to `⌊j/2⌋`, and checks that at `σ = 0` the `m`-th
derivative is exactly `F_m`. Each block is supported in `K` and vanishes for `σ ≥ 1`.

**Lean.** `SpacetimeGluing.smoothExtension_contDiff` constructs a global smooth extension from
the actual one-sided normal jets; `SpatialBorelExtension.rightExtension_contDiff` is the
Taylor–Borel realization; `rightExtension_time_jets` proves that the `k`-th time jet at the
join is `F_k`. E137 placed the row.

**Does the inference follow?** `exact` at statement level. The construction is the paper's
shrinking-cutoff series, and its derivative matching is a theorem, not an assumption.

---

## Step 5 — Lemma 10.4, energy and dissipation

**Paper.** `Lemma 10.4` (`ns.txt:6115`): with `F(t) = ∫_0^t ‖f(s)‖² ds`, `F(1) < ∞` and

```
‖u(t)‖₂² + 2∫_0^t ‖∇u(s)‖₂² ds ≤ F(t)²   (0 ≤ t < 1).
```

**In plain terms.** Testing the equation against `u` gives an energy identity; the force term
can add or remove energy, but Cauchy–Schwarz and Gronwall still give a finite bound. The total
dissipation up to time one is finite.

**Hypotheses.** The localized fields are smooth and compactly supported on each `[0,T]`,
`T < 1`.

**What the paper does.** Derives
`½ d/dt ‖u‖₂² + ‖∇u‖₂² = ⟨f,u⟩`, divides by `(‖u‖₂² + δ²)^{1/2}`, integrates from zero data,
lets `δ ↓ 0`, and integrates the identity again. Monotone convergence gives the `t ↑ 1`
dissipation bound from the `t < 1` bounds alone.

**Lean.** `R3/IntegratedDissipation.lean:279` proves `candidate_energy_estimates`, which
returns the interval integrability of `f`, the integrability of the dissipation, the sharp
inequality on every `T ∈ [0,1)`, and the total bound.

**Does the inference follow?** `exact`. The force term is `⟨f,u⟩`, not a positive term; the
Lean statement keeps it inside `F(t)²` and does not assert that the force only adds energy.

---

## Step 6 — Lemma 10.5, whole-space comparison

**Paper.** `Lemma 10.5` (`ns.txt:6143`): fix `T < 1`. If `v, P` is a smooth solution on
`ℝ³ × [0,T]` with the force of Lemma 10.3, zero initial velocity, and
`v ∈ L∞([0,T]; L²(ℝ³))`, then `v = u` on that interval.

**In plain terms.** A competitor with the same force and datum cannot differ from the
constructed field before time one. The proof localizes the difference on expanding balls,
recovers the pressure gradient from the equation, and uses a weighted energy estimate plus
Gronwall. No spatial growth condition on the competitor's pressure is assumed.

**Hypotheses.** Smoothness, the same force, zero datum, and a uniform `L²` bound. No support or
decay of the competitor.

**What the paper does.** Sets `w = v − u`, `π = P − p`, derives
`∂_t w + (v·∇)w + (w·∇)u = Δw − ∇π`, reconstructs `∇π` by Riesz transforms, and closes the
weighted estimate on balls with constants independent of the radius.

**Lean.** `R3/WholeSpaceComparisonClosure.eq_of_pressure_flux_bound` is the final PDE energy
calculation; its pressure-flux hypothesis is discharged by the pressure reconstruction modules
in `R3/WholeSpaceUniqueness`. `R3/CandidateBreakdown.CandidateProperties.no_global_solution_one`
turns agreement-before-one into the absence of a global competitor.

**Does the inference follow?** `composition`. The statement is exact; the proof is a
composition. The pressure flux is not an extra competitor hypothesis: the closure theorem says
in its own docstring that the flux hypothesis is discharged by the reconstruction modules. The
composition is the step; no single theorem named “Lemma 10.5” is needed.

---

## Step 7 — Proposition 9.9, the summed local field

**Paper.** `Proposition 9.9` (`ns.txt:5794`): there are smooth `(u_loc, p_loc)` on `Ω*`,
obtained by summing the finite corrections, with `div u_loc = 0` and all conclusions of
Theorem 3.1 holding.

**In plain terms.** Sum the finite-stage corrections with cutoffs shrinking in `q`. The sum
converges to a smooth divergence-free field whose residual is flat to every order, whose
endpoint jets exist, and whose exterior is the exact heat flow.

**Hypotheses.** Lemmas 9.7 and 9.8, the summation lemma Lemma 5.4, and the finite-stage
estimates.

**What the paper does.** Applies Lemma 5.4 with `F(u,p) = R(u,p)` and `q* = q_big`, verifies
its hypotheses on the finite states, and checks Theorem 3.1(i)–(iv) for the sum.

**Lean.** `LocalPaperTheorem.local_theorem` returns `Properties h q* Xa Xext C A D u p` with
no finite-stage or schedule hypothesis. `Properties` carries smoothness, the curl
decomposition, divergence-freeness, endpoint extensions, uniform jets on scale strips, the
flat residual tower, the exact heat exterior, and the angular growth — all for the same fields.

**Does the inference follow?** `exact`, and stronger: the Lean `Properties` requires
smoothness on all `t < 1` and uniform jets on compact sets avoiding the singular point, where
the paper states the local positive-scale domain.

---

## Step 8 — Proposition 9.3, one correction cycle

**Paper.** `Proposition 9.3` (`ns.txt:5272`): fix `j`. For a finite sequence of pulse inverses,
curl constructions, signed amplitude maps, and mean maps, with pressure reconstructed by
(8.12) and products taken with the full velocity, there is a decomposition
`R(u[j],p[j]) = G[j] + F[j]` with (i) supported sources in `W_α`, (ii) a flat remainder
`|F[j]|_m ≤ C q^N`, and (iii) the exact mean equations (9.6).

**In plain terms.** One correction step splits the residual into a part that is a finite sum of
supported waves and a part that is flat to every order, while preserving the exact mean
balance. The exponents come from the wave and mean maps, not from a new estimate.

**Hypotheses.** The finite construction, the pressure reconstruction (8.12), and the exponents
furnished by Propositions 9.1, 7.2, 6.6, 7.6, §8, and Lemma 9.2.

**What the paper does.** Proves (i) by collecting the supported coefficients, then tracks the
additive errors through the construction to prove (ii), and checks (iii) by substituting the
complete velocity into the mean equations.

**Lean.** `ActualStageEstimates.RunData.result` produces a
`CorrectionAnalyticStep.StepResult` for each stage from the actual invariant and step data;
`ActualCyclePreservation` supplies the invariant and the fixed parameters;
`ActualStageEstimates.RunData.rank_class` supplies the class update. E149 placed the row.

**Does the inference follow?** `composition`. The statement is exact; the proof is a
composition. The tree proves the step for each `j` from the actual data; it does not package
the whole finite induction as one theorem. That is a packaging difference, not a missing
estimate.

---

## Step 9 — Lemma 9.7, one common domain

**Paper.** `Lemma 9.7` (`ns.txt:5669`): there is `q_big > 0`, independent of the correction
stage and derivative order, such that every finite partial sum is well defined on
`0 < q < q_big`. For every fixed stage and output amplitude derivative, the construction and
estimate require finitely many input amplitude derivatives.

**In plain terms.** All finite stages live on one `q`-domain, and no stage needs infinitely
many derivatives of its input. The constants may depend on the stage; the domain and the
finite-derivative count may not.

**Hypotheses.** The fixed background, a positive lower bound for `|n_Φ|`, the primary
covariance, and the fixed supports of the mean-correction profiles.

**What the paper does.** Chooses `q_big ≤ q*` once. Every later amplitude problem is linear
with fixed coefficients; the same threshold works for every harmonic because the propagator is
the fundamental one times a damping factor of modulus at most one. The derivative count is a
finite DAG: each vertex asks for finitely many derivatives of its inputs, and the graph is
finite at each fixed stage.

**Lean.** `ActualCandidateConstruction.qbig` has neither a stage nor a derivative-order
argument; `GermEndpointInputs` carries one `qbig` across `∀ j`. The finite-derivative clause is
not stated: the tree has no syntax representation of the derivation DAG for a proposition to
quantify over. E159 records this; E165 corrects E159's wording (Lean does quantify over proof
terms; what is missing is the syntactic representation, not proof quantification).

**Does the inference follow?** `inexpressible` for the third clause, `exact` for the first two.
The paper's argument is valid; the Lean development cannot state the clause because it is
about the proof's syntax. This is category 2, not a defect.

---

## Step 10 — Lemma 9.8, stage-independent jet losses

**Paper.** `Lemma 9.8` (`ns.txt:5734`): for every Cartesian space–time derivative order `m`,

```
|Z_j|_m + |Δu_j|_m ≤ C_{j,m} q^{g_j − ℓ_m} (1 + |log q|) P_{j,m},   g_j = h j/10 → ∞,
|(u[j],p[j])|_m ≤ C_{j,m} q^{−K_m} (1 + |log q|) P_{j,m},
|R(u[j],p[j])|_m ≤ C_{j,m} q^{hσ_j − K_m} (1 + |log q|) P_{j,m} + E_{j,m},
```

with `ℓ_m` and `K_m` independent of `j`, and `E_{j,m} ≤ C q^N` for every `N`.

**In plain terms.** Differentiating the physical fields costs a fixed power of `q` at each
derivative order. The loss does not grow with the correction stage; the stage only changes the
constant and the gain `g_j`.

**Hypotheses.** The chart derivative costs (9.19), the phase bounds, and the finite harmonic
range at a fixed stage.

**What the paper does.** Computes the radial, axial, time, and frame derivative costs, bounds
the phase exponential, and sums the finite Leibniz terms. The exponent loss is the sum of the
fixed costs; the stage enters only through `g_j` and the constants.

**Lean.** `BaseResidual.physicalLoss h m = 2*A h + (m+1)*(1+3h/2)` is the paper's printed
`ℓ_m`; `ExponentLedger.gain h j = h*j/10` is `g_j`; no definition between `physicalLoss` and
`paperJetLoss` accepts a stage index. E134 placed the row.

**Does the inference follow?** `exact`, and stronger: the tree absorbs the flat error `E_{j,m}`
instead of displaying it separately.

---

## Step 11 — Lemma 6.1, disjoint lifted slots

**Paper.** `Lemma 6.1` (`ns.txt:3392`): for the labels `Γ` and slow supports `K_γ` of (6.8)–
(6.9), there are centers `c_γ` and a radius `r₀ > 0`, common to all labels and independent of
the band, such that the enlarged rectangles are injectively parametrized and

```
γ ≠ γ′,  K_γ ∩ K_γ′ ≠ ∅  ⇒  R^{abs,+}_γ ∩ R^{abs,+}_γ′ = ∅.
```

**In plain terms.** Two labels whose slow supports meet get lifted rectangles that do not
overlap. That is what makes the product of two label-supported fields vanish: if both were
nonzero at a point, the point would lie in both rectangles, contradicting the separation.

**Hypotheses.** The dyadic supports, the band indices differing by at most four, and the
covering indices differing by at most `Δ_max`.

**What the paper does.** Bounds the interaction graph, greedily colors it with finitely many
colors, chooses rational centers avoiding the finitely many forbidden differences
`c_μ = J^Δ_g c_ν`, and chooses one rectangle size small enough that the separation survives
the fixed enlargement.

**Lean.** `PartitionedCovariance.SlotSystem` has `radius`, `injective`, and `disjoint` as
fields; `exists_slotSystem` constructs them. `masks_force_adjacency` turns two nonzero masks at
a common point into `SlotColoring.Adj`; `SlotSystem.disjoint` turns `Adj` into disjoint lifted
supports; `SlotSystem.cross_product_zero` (`PartitionedCovariance.lean:323`) composes them and
proves the product of two label-supported fields is zero.

**The correction.** E163's first prose argued: a point of `K_γ ∩ K_γ′` exists, so both masks
are nonzero there. That is false for a closed support: a smooth cutoff can vanish on the
boundary of its support. E166 replaced the step with a `tsupport` route via
`physicalSlowMask_tsupport_subset_physicalBox` and `lineMask_tsupport`. That route is not
needed and does not repair the implication. The valid argument starts from a **nonzero
product**: if `f(Y)g(Y) ≠ 0`, then both masks are nonzero at the underlying point, so
`masks_force_adjacency` applies, and `disjoint` contradicts membership in both lifted
supports. `cross_product_zero` is exactly that argument, already a declaration.

**Does the inference follow?** `exact` at the model level, not provisional. The paper's (6.13)
is the `disjoint` field; the product-zero use is `cross_product_zero`. The only modelling
identification is the paper's `F_γ` versus the tree's `covered` field, which E163 already
named. E168 records the correction to E163/E166.

---

## Step 12 — Lemma 6.2, the common-torus representation

**Paper.** `Lemma 6.2` (`ns.txt:3462`): for `U, i₀, H` as in (6.17), each change `H ↦ Y_i` has
uniformly bounded derivative factors, and `R^H_γ` consists of `14^{Δ_ℓ} ≤ 14^{Δ_max}`
disjoint lifts of `R_γ`. Haar averages on the absolute, common, and band tori agree whenever
the function is a pullback. Radial integration at fixed `(z,t)`, torus translation, averaging,
and directional Fourier inversion on zero-mean functions preserve common-torus descent and
introduce no new dyadic band.

**In plain terms.** Moving a field from its band torus to a common torus costs a bounded
derivative factor and a finite number of copies, and the operations used later do not create a
new band.

**Hypotheses.** `U` chosen so its band indices differ by at most four; `Δ_ℓ = i(ℓ) − i₀`.

**What the paper does.** Compares the covering maps, counts the quotient
`#(ℤ²/J^Δ_g ℤ²) = |det J_g|^Δ = 14^Δ`, checks the Haar identity on Fourier characters, and
argues that radial integration fixes `(z,t)` and leaves the band cutoffs unchanged.

**Lean.** `TorusCoverDegree.card_liftedRectangles` counts the `14^{Δ_ℓ}` lifts;
`TorusAverages.squareAverage_covering_iterate` is the three-torus Haar identity;
`CommonCoverClass.bandGeometry_argumentCost_le` bounds the derivative factors. The fourth
sentence bundles four operations; the tree proves three separately, and the radial-integration
half plus “no new dyadic band” have no single declaration. E164 records this.

**Does the inference follow?** `partial`. The first three clauses are exact; the fourth is a
conjunction with no declaration and no named predicate for common-torus descent. This is
category 2: the paper's argument is explicit, the tree's assembly is implicit. It is not a
false step.

---

## Step 13 — Proposition 7.2, the driven amplitude

**Paper.** `Proposition 7.2` (`ns.txt:3992`): fix `α`, finitely many harmonics, and a label at
level `i` on a common torus `H`. For each harmonic let `f_m` be a `C³` coefficient descending
to `H`, with the stated support and bounds. On `0 < q < q*` there is a unique amplitude `t_m`
with `n_Φ · t_m = 0`, zero initial data, and a pressure coefficient `π_m` such that (7.5)
holds:

```
t'_m = A_Φ t_m − m² d t_m − proj_{n_Φ^⊥} Φ f_m,   t_m(0) = 0,
π_m = (i k_m n_Φ · K t_m − n'_Φ · t_m + n_Φ · f_m) / |n_Φ|².
```

The bounds (7.14)–(7.15) hold, and one-sided slow derivatives pass to the solution.

**In plain terms.** Solve the linear pulse equation driven by one harmonic source, get the
pressure back from the same equation, and keep the same envelope and support.

**Hypotheses.** The moving frame, the source support, the finite harmonic set, and the
threshold `q*` from Lemma 7.1.

**What the paper does.** Bounds the forward propagator by `P(v)/P(w)`, writes Duhamel, checks
the support and descent, and recovers the pressure from the normal component of the equation.

**Lean.** `PulseAmplitude` and `LinearWaveResidual` prove the bounds on the output fields
(7.14) and the jet tower. The **map** `f_m ↦ (t_m, π_m)` is not a declaration, and the
pressure formula (7.13) is proved by subtracting the target, not by constructing `π_m` from
the right-hand side. E158 records this.

**Does the inference follow?** `partial`. The existence and uniqueness of `t_m` and the bounds
are declared; the operator and the explicit pressure reconstruction are not. Category 2.

---

## Step 14 — Corollary 7.3, one threshold for all finite maps

**Paper.** `Corollary 7.3` (`ns.txt:4114`): the solution operators `f_m ↦ (t_m, π_m)` are
defined at every finite correction stage on the same domain `0 < q < q*`. Increasing the
finite harmonic set or the derivative order changes constants and polynomial degrees but does
not require shrinking the domain.

**In plain terms.** The threshold is uniform in the harmonic set and the stage. Higher
harmonics only add damping and larger constants.

**Hypotheses.** Lemma 7.1's single finite choice and (7.18).

**What the paper does.** Checks that every higher harmonic is at least as damped in value as
the first, and that extra factors of `m` and coefficient derivatives only enlarge constants.

**Lean.** `CorrectionStep` proves the uniformity three times over (E154). No declaration is
the operator `f_m ↦ (t_m, π_m)`, so the corollary's subject is missing even though its
conclusion is proved for the outputs.

**Does the inference follow?** `partial`. The uniformity is exact; the operator is not
declared. Category 2.

---

## Step 15 — Proposition 7.6, the linearized amplitude map

**Paper.** `Proposition 7.6` (`ns.txt:4317`): for every `α` and every real two-vector
`Σ ∈ M_α` independent of the angular and auxiliary variables, (7.31) defines a linear
operation `L_Σ`. Its harmonic coefficients satisfy the local derivative and envelope bounds of
`W_{α−1/2}`, with smooth zero extension at the shell edges, and

```
η^β L_Σ ∈ W_{α−1/2},   B(W₀, L_Σ) = Σ,   C(η^β L_Σ) ∈ M_{2α−1}.
```

**In plain terms.** Given a stress `Σ`, build the two scalar coefficients `δa_σ` that produce
it under the bilinear covariance, and keep the wave-class bounds. The denominator `a_σ` is
fixed at every stage.

**Hypotheses.** The differentiated inverse bounds of Proposition 7.5, and `Σ ∈ M_α` with no
sign or relative-size restriction.

**What the paper does.** Applies Leibniz to `d_Σ = H^{-1}(Σ/ε)`, cancels the numerator weights
against `ζ^{-1/2}`, and proves the exact bilinear identity `B(W₀, L_Σ) = Σ`.

**Lean.** `SmoothCovariance` and `SignedCovariance` prove the class and the quadratic
remainder; the **map** `Σ ↦ L_Σ` is not declared, and the identity `B(W₀, L_Σ) = Σ` is proved
by subtracting the target rather than constructing `L_Σ` from `δa`. E162 records this as the
same field-versus-map pattern as Step 13.

**Does the inference follow?** `partial`. The bounds and the identity are declared for the
output; the linear operation is not. Category 2.

---

## Step 16 — Proposition 5.3, the base residual rate

**Paper.** `Proposition 5.3` (`ns.txt:2874`): fix the leading profiles of Theorem 4.6. There is
a sequence of positive-order profiles built by Lemmas 5.1 and 5.2. Every finite velocity sum
`u[N]` is divergence-free. On every fixed compact profile range, for each `N, m ≥ 0` and
`0 < q ≤ 1`,

```
|F_slow(U[N])|_m ≤ C_{N,m} q^{2h(N+1) − K_m},   K_m independent of N.
```

**In plain terms.** Truncating the base expansion at order `N` leaves a residual whose decay
in `q` improves linearly with `N`, and the derivative loss `K_m` does not grow with `N`.

**Hypotheses.** The leading profiles, the inner solutions of Lemma 5.1, the extensions and
moment corrections of Lemma 5.2, and the finalized lower orders.

**What the paper does.** Constructs the sequence, uses (5.2) for exact incompressibility,
differentiates the stress primitives, and shows that every uncancelled product or shifted
viscous term has exponent increment at least `2h(N+1)`. The derivative loss is computed from
(5.26).

**Lean.** `BaseResidual.truncationResidual_rate` prints `2Nh − 2 − M`; the paper's
`2h(N+1) − K_m` is the same at `K_m = m + 2 + 2h`, so the loss is linear in `m` and does not
grow with `N`. `SlowExpansionResidual.divergence_slowVelocity_eq_zero` states the divergence
clause for the actual Euclidean divergence of the finite sum, and
`divergence_slowVelocity` proves that divergence equals the finite coefficient series. E95 and
E97 placed both clauses.

**Does the inference follow?** `exact`. Both the exponent and the divergence clause are
declarations; the exponent is derived from the omitted monomials, not assumed.

---

## The seven partials, in one table

| Result | Exact clauses | Unmatched clause | Category |
|---|---|---|---|
| Lemma 5.1 | solve, uniqueness, zero-axis, smoothness, holomorphy | cone-margin interval; one theorem for all positive orders | missing composition / packaging |
| Lemma 10.2 | convergence, compatibility, vanishing at the origin | `F_j ∈ C_c^∞`, supported in `K` | missing declaration |
| Lemma 6.2 | derivative factors, `14^{Δ}` lifts, Haar averages | radial integration at fixed `(z,t)`; no new band | missing declaration / no predicate |
| Proposition 7.2 | existence/uniqueness of `t_m`; bounds (7.14)–(7.15) | the map `f_m ↦ (t_m, π_m)`; explicit `π_m` | missing operator |
| Corollary 7.3 | uniformity in harmonics and stage | the operator the corollary is about | missing operator |
| Proposition 7.6 | class bounds; `C(η^β L_Σ) ∈ M_{2α−1}` | the map `Σ ↦ L_Σ`; constructive `B(W₀,L_Σ)=Σ` | missing operator |

One row is `partial-inexpressible`: Lemma 9.7's finite-derivative count, because it is a fact
about the derivation, not about the fields.

## The defect ledger

What would count as a mathematical defect, and what the audit actually has:

| Candidate defect | Status | Why |
|---|---|---|
| Existential constants hide an unusable bound | **not a defect** | The headline theorem mentions no constant. The kernel checks inhabitation, not size. This is an epistemic limitation of the formalization, not a false paper step. |
| The anisotropic weights make the operator nonhomogeneous | **not a defect** | E63 retracted the order-by-order impossibility claim. Different weights are compatible with a term-by-term construction; the paper does exactly that. |
| A closed support intersection is treated as a nonzero mask | **audit prose error, not a paper error** | E163's first explanation was invalid; `cross_product_zero` uses the correct nonzero-product argument. E168 records it. |
| Proposition 7.5's floor is weaker than the paper's | **formalization weaker, not false** | The tree proves `c√S·ζ` where the paper prints `c√(Sζ)`; the consumer needs only `ζ^{-1/2}`. It is weaker-but-sufficient, not a contradiction. |
| The driven amplitude and linearized map are not declared | **formalization gap, not a false inference** | The paper defines both maps explicitly; the tree proves bounds on their outputs and the identity by subtraction. Category 2. |
| Lemma 9.7's derivative count is unstated | **inexpressible, not false** | The paper's DAG argument is valid; Lean has no syntax representation for it. Category 2. |
| Lemma 10.2's limit tensors lack a support statement | **missing declaration, not false** | The paper's limits vanish off `K`; the tree states the convergence and compatibility but not the support bundle. Category 2. |
| Lemma 5.1's cone-margin interval is not in the solve theorem | **missing composition, not false** | `exists_positive_order_solution` takes `R` and proves the solve; the paper's interval is chosen from Theorem 4.6. The per-order family is per-`n`, not one quantified theorem. Category 2. |

**Bottom line.** No row in this companion is a `defect`. The audit establishes code facts and
formalization limits; it does not establish that the paper's proof is wrong. To move a row to
`defect`, one would need a stated inequality that is false on its own terms, a consumer that
uses a bound the producer does not supply, or a Lean hypothesis the paper does not grant. None
of the sixteen steps has produced one.

## Reproduction status

| Check | Evidence | Status |
|---|---|---|
| `lake build NavierStokes` at `f9e8bc5` | E73, run `44987195620` | green, 9,580 jobs |
| Axiom print, R3 and periodic | E72, E73 | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| Comparator, R3 and periodic | E75 | pass on the default and nanoda kernels |
| Euler Comparator | E79 | pass on both kernels |
| This companion's structure and citations | `tools/step_check.py` | green, 16 steps |
| The audit's prose readings | — | not machine-checkable; statement-level |
| A fresh kernel run for this revision | — | not performed; no Lean file changed |

No new kernel run was made for this pass. Re-running `kernel-check.yml` would rebuild the same
pinned upstream tree; it cannot check the audit's prose. The existing E73/E75 evidence is the
kernel evidence, and it is stated as such rather than as a check of this file.

## What is not in this file

- **The proofs of the Lean declarations were not recompiled.** `exact` means the statement
  matches; it does not mean the kernel was re-run for this pass. The build evidence is E73
  and E75, at the pinned commit.
- **The paper's §4 leading-order construction and the rest of §5 are not walked here.** Lemma 5.1 is recorded as partial in the table above (E169); Theorem 4.6,
  Proposition 4.2 and the §5 lemmas are upstream inputs to Step 16; their statements are in
  `CROSSWALK.md`, and the §4–§5 rows are classified in `NEXT.md` (E170).
- **No result is unplaced now.** E170 classifies the remaining 26 supporting rows as
  partial-unread, each with its declared fragment and missing bundle named. This companion
  covers the sixteen rows that carry Theorem 1.1 and every partial; the queue is closed.
- **No claim about the whole upstream repository.** This is the whole-space forced
  Navier–Stokes theorem; the periodic corollary and the Euler development are separate.

## Citation convention

`ns.txt:NNNN` is a line in `.setup/paper/ns.txt`. `NavierStokes/Foo.lean:NNN` is a line in the
pinned upstream commit `f9e8bc5`. A declaration named without a line is cited by its theorem
name; `tools/step_check.py` validates the structure and, when the sources are present, the
line references.

<!-- proof-steps: steps=16 exact=8 composition=2 partial=5 inexpressible=1 defect=0 -->

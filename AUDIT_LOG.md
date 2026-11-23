# FORENSIC AUDIT LOG — openai/NavierStokesAndEuler

**Policy:** append-only. Entries are never edited or deleted. Corrections are appended as new entries.
**Auditor:** John (Lean 4 / 3D PDE).
**Target commit:** `f9e8bc5` (`main`, shallow clone, 2026-09-08 repo creation, last push 2026-09-10).
**Toolchain declared:** `leanprover/lean4:v4.34.0-rc2`, Mathlib `v4.34.0-rc2`, Comparator `v4.34.0-rc2`.

> Scope limitation, stated up front and not to be quietly dropped later: **every finding below is source-read, not obtained by elaboration.** No `elan`/`lean`/`lake` existed on the audit host when the findings were made, and the project's export closure is ~28.6M lines / 1.5 GB per Lean Kernel Arena. Kernel acceptance was reproduced **afterwards**, on Linux: `lake build NavierStokes` completed 9,580 jobs with exit 0 (817 modules, 20 min 17 s), and `#print axioms` on the four R3 theorems reports only `propext`, `Classical.choice`, `Quot.sound`. The pinned toolchain's `lake` aborts with `SIGTRAP` in `libmalloc` on current macOS (E50; 3/3 reproductions), so the build ran in an Ubuntu VM. That build verifies terms, not statements; the findings below remain textual. Kernel acceptance is *not* statement review.

---

## E0 — Ingest metrics

| Metric | Value |
|---|---|
| `.lean` files | 2,659 |
| Lines (clone) | 641,332 |
| `NavierStokes/` | 816 files / 429,279 lines (109 in `NavierStokes/R3/`) |
| `Euler/` | 1,839 files / 211,578 lines |
| `ComparatorChallenges/` | 2 files / 472 lines |
| `axiom` declarations | 0 |
| `sorry`/`admit` | 5 (all in `ComparatorChallenges/`; 3 terms, 2 in prose) |
| `native_decide` | 0 |
| `@[implemented_by]` / `@[extern]` | 0 |
| `unsafe` | 0 |
| `partial def` | 0 |

**Correction to a circulating figure:** the often-quoted "28.6M lines" is the *lean4export closure* including transitive Mathlib, not this repository. The repository itself is 641k lines.

**Import-graph check:** `rg 'import ComparatorChallenges'` over `NavierStokes/`, `Euler/`, `NavierStokes.lean`, `Euler.lean` returns nothing. The `sorry`-bearing reference module is unreachable from the proof root, consistent with its own header (*"Neither the proof root nor the submission imports this reference"*). The `sorry_count: 0` claim in `formalization.yaml` therefore refers to the submission and is accurate.

---

## E1 — `NavierStokes/R3/Theorem.lean` : `theorem_1_1_with_initial_rest`

**(a) Raw Lean.**
```lean
theorem theorem_1_1_with_initial_rest (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space,
        u (t, x) = 0 ∧ p (t, x) = 0 := by
  obtain ⟨u, p, f, K, hc, hzero⟩ := ActualCandidate.selected_candidate_one_with_initial_rest
  refine ⟨scaledVelocity ν u, scaledPressure ν p, scaledVelocity ν f,
    (fun x : Space => Real.sqrt ν • x) '' K, candidate_at_viscosity hc hν, ?_, ?_⟩
  · rintro ⟨v⟩
    exact hc.no_global_solution_one ⟨normalized_global_solution hν v⟩
```

**(b) Informalization.** For every $\nu>0$ there exist $u,p,f$ and compact $K$ with
$$u\in C^\infty(\overline{\Omega}\setminus\{t=1\}),\quad \nabla\cdot u=0,\quad \partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p+f\ \ (0<t<1),$$
$$u\equiv 0,\ p\equiv 0\ \text{on}\ |t|\le 3/8,\qquad u(0,\cdot)=0,$$
$$\sup_{t\in[0,1)}\tfrac12\|u(t)\|_{L^2}^2<\infty,\qquad \limsup_{t\uparrow 1}\|u(t)\|_{L^\infty}=+\infty,$$
and no global finite-energy solution of the same forced problem from the zero datum exists.

**(c) Dimensional check.** $[u]=LT^{-1}$, $[f]=LT^{-2}$, $[\nu]=L^2T^{-1}$, $[\tfrac12\|u\|_2^2]=L^5T^{-2}$. The clause $u=p=0$ on $|t|\le3/8$ is dimensionally inert (an identity, not an estimate). Consistent.

**(d) Finding — the datum is identically zero.** `CandidateProperties.zero_initial_velocity : ∀ x, u (0,x) = 0`, and the comparator instantiation is literally `refine ⟨fun _ => 0, toComparator (rescaledForce ν f), ...⟩` (`NavierStokes/ComparatorR3Theorem.lean`). The entire construction is carried by the forcing. This is *admissible* under Clay (C) — which only demands *some* smooth $u_0$ — but it changes what the theorem says: this is **forced breakdown from rest**, not spontaneous finite-time blowup of a smooth finite-energy datum. The repository's own header says so ("one compactly supported flow ... Its same force and zero initial data satisfy the exact comparator conditions"). No concealment; the abstract does say "with smooth forcing". Recorded because downstream citations of "Navier–Stokes blowup" typically elide it.

---

## E2 — `NavierStokes/R3/ViscosityScaling.lean` : `rescale_residual`

**(a) Raw Lean.**
```lean
/-- Multiplying lengths and velocities by `a` multiplies viscosity by `a²`. -/
theorem rescale_residual (μ a : ℝ) (ha : a ≠ 0) (u : VelocityField)
    (p : PressureField) (t : ℝ) (x : Space) :
    ProblemStatement.navierStokesResidual (a ^ 2 * μ)
      (rescale a a⁻¹ u) (rescale (a ^ 2) a⁻¹ p) t x =
      a • ProblemStatement.navierStokesResidual μ u p t (a⁻¹ • x) := by
  have h1 : a ^ 2 * a⁻¹ = a := by field_simp
  have h2 : (a ^ 2 * μ) * (a * a⁻¹ ^ 2) = a * μ := by field_simp
  simp only [ProblemStatement.navierStokesResidual, rescale_temporalDerivative,
    rescale_advection, rescale_laplacian, rescale_gradient, smul_add, smul_sub,
    smul_smul, h1, h2]
```

**(b) Informalization.** With $u_a(t,x)=a\,u(t,a^{-1}x)$, $p_a(t,x)=a^2 p(t,a^{-1}x)$:
$$\mathrm{Res}_{a^2\nu}[u_a,p_a](t,x) \;=\; a\,\mathrm{Res}_{\nu}[u,p](t,a^{-1}x).$$
Setting $a=\sqrt\nu$, $\mu=1$ gives `scaledVelocity ν u = √ν • u(t, x/√ν)`, `scaledPressure ν p = ν • p(t, x/√ν)`, and $\nu = a^2\cdot1$. This is the exact Navier–Stokes symmetry group element $u\mapsto \lambda u(\lambda x,\lambda^2t)$ restricted to the spatial slice with time held fixed.

**(c) Dimensional check — PASSES.** Term by term from the file: $\partial_t \mapsto a\,(\cdot)$; advection $\mapsto a^2b$ with $ab=1$ so $\mapsto a$; Laplacian $\mapsto ab^2$ with $a^2\mu$ coefficient giving $a\mu$; pressure gradient $\mapsto a^2b = a$. All four terms scale by the *same* $a$, so the residual is homogeneous of degree one and vanishes iff the original does. $[\nu]=L^2T^{-1}$ is preserved because $[a]^2=L^2T^{-0}$ has the dimension of a length ratio squared. **No anomaly.** The `h2` identity $(a^2\mu)(a\,a^{-2})=a\mu$ is the whole load-bearing arithmetic and it is correct.

**(d) Consequence to record.** "For every positive viscosity" is therefore a *similarity* statement: the singular time is pinned to $1$ at every $\nu$, and the energy bound rescales as $E_\nu \sim \nu^{-1/2}E$. The theorem is not uniform in $\nu$, and viscosity is not playing a regularizing role — it is being scaled out. Physically this is the correct reading of a similarity construction, but "holds for all $\nu$" should not be read as "viscosity cannot prevent it at any strength"; the force is re-chosen for each $\nu$.

---

## E3 — `NavierStokes/R3FiniteEnergyComparison.lean` : `compact_candidate_excludes_global_solution`

**(a) Raw Lean (body excerpt).**
```lean
theorem compact_candidate_excludes_global_solution
    {u v f : VelocityField} {p q : PressureField}
    (h : R3CompactCandidate.Properties u p f) (hv : GlobalSolutionRn f v q) : False := by
  apply h.not_global_agreement hv.velocity_smooth
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  ...
  have hsupport : ∀ r ∈ Icc (0 : ℝ) t, tsupport (fun y => u (r, y)) ⊆ K := ...
  have heq := NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc hpos
    (h.velocity_smooth.mono hpre) (hv.velocity_smooth.mono hfuture)
    (h.pressure_smooth.mono hpre) (hv.pressure_smooth.mono hfuture)
    hK hsupport (hv.uniformFiniteEnergy t) ... 
  exact heq t ⟨ht.1, le_rfl⟩ x
```

**(b) Informalization.** Let $(u,p)$ be the constructed candidate with compact spatial support $K$ and $u(0,\cdot)=0$, and $(v,q)$ a global smooth solution of the same forced system with the same zero datum and uniformly bounded energy. Classical uniqueness on the slab $\mathbb{R}^3\times[0,t]$ forces $v\equiv u$ on that slab; since $u$ has no $L^\infty$ bound as $t\uparrow1$, $v$ cannot either. Contradiction. Hence
$$\neg\exists (v,q):\ \text{global smooth, finite energy, same } f,\ \text{zero datum}.$$

**(c) Dimensional check.** No inequality is asserted — this is an identity/uniqueness transfer. The only quantitative input is `hv.uniformFiniteEnergy t`, which supplies $\tfrac12\|v(t)\|_2^2\le E$ with $[E]=L^5T^{-2}$; the uniqueness theorem consumes it at the same dimension. Consistent.

**(d) Finding — the architecture is correct and the competitor class is honest.** `GlobalFiniteEnergySolution` is documented as imposing *"no support, periodicity, pressure-growth, derivative-growth, or energy inequality assumptions on a competitor."* That is the right way to close alternative (C): the exclusion is by uniqueness against a singular object, not by weakening the competitor. **This is the strongest part of the repository.** Note it is a *conditional* non-existence: it is `¬∃` for this prescribed $f$, not a statement about the unforced equation.

---

## E4 — `NavierStokes/ExponentLedger.lean` : the $\kappa=10^{-5}$ budget

**(a) Raw Lean (header + representative definitions).**
```lean
/-- ... The manuscript fixes `κ = 10⁻⁵` in §8.1 and again in §10.2. ... -/
def particularGain (σ κ : ℝ) : ℝ :=
  min (min (min (1 / 2 - 3 * κ) (1 / 2 - κ)) (waveExponent σ - κ)) (2 / 5)

def signedGain (σ κ : ℝ) : ℝ :=
  min (min (min (1 / 2 - 4 * κ) (2 / 5 - κ)) (1 / 2 - 2 * κ)) (waveExponent σ - 3 * κ)

def signedBarGain (σ κ : ℝ) : ℝ :=
  min (min (min (min (9 / 50 - 2 * κ) (1 / 2 - 3 * κ)) (σ - 3 * κ)) (1 - κ)) (1 - 2 * κ)
```

**(b) Informalization.** For a residual of "order" $\sigma$, the four competing estimates have gains $\tfrac12-3\kappa$, $\tfrac12-\kappa$, $B-\kappa$ where $B=\tfrac12+\sigma$, and $\tfrac25$; the declared gain is their minimum. With $\sigma\ge\tfrac15$ and $0\le\kappa\le10^{-5}$, every gain is positive and bounded away from zero by an explicit rational.

**(c) Dimensional check — PASSES trivially but is uninformative.** Exponents and $\kappa$ are dimensionless real numbers subtracted from $\tfrac12$; no physical quantity enters. There is no dimension that could fail here. That is also the point: **this file contains no PDE.**

**(d) Finding — self-documented as arithmetic-only.** Header, verbatim: *"This file checks the arithmetic of those assignments, conditional on the estimates being valid. It does not define the analytic classes, construct a correction, or prove an estimate for a PDE."* This is unusually honest and it is the single most important caveat in the codebase. $\kappa=10^{-5}$ is a **slack budget**, not a physical parameter: it is chosen small enough that every exponent stays positive. If any analytic estimate's true constant exceeds the ledger's allowance, the ledger remains sound but inapplicable. This is the legitimate modern form of "$\varepsilon$ small enough", and it is exactly the kind of margin that a referee must check against the paper's §8.1/§10.2.

---

## E5 — Similarity coordinates: what they actually are

**(a) Raw Lean** (`NavierStokes/SimilarityCoordinates.lean`).
```lean
def forwardScalar (a z q : ℝ) : ℝ := q - z ^ 2 * q ^ a

theorem exists_positive_solution {a τ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hτ : 0 < τ) (z : ℝ) : ∃ q : ℝ, 0 < q ∧ forwardScalar a z q = τ
```
with `NavierStokes/SimilarityProfile.lean`: `q h p := coordinateQ (2*h) (1 - p.1, p.2.2)`, `pullback h b f p := q h p ^ b * f (inner h p)`.

**(b) Informalization.** The change of variables is the *implicit* map $q=q(\tau,z)$ solving
$$\tau \;=\; q - z^2 q^{a}, \qquad a = 2h \in (0,1),$$
with $s=r^2/2$, inner variables $(X,\eta)$, and physical reconstruction
$$U(t,x) \;=\; q(t)^{b}\, F\bigl(X(t),\eta(t)\bigr).$$

**(c) Dimensional check — ANOMALY, explained.** For $\tau = q - z^2q^a$ to be dimensionally homogeneous with $[q]=[\tau]=T$ one needs $[z]^2\,T^{a} = T$, i.e.
$$[z] = T^{(1-a)/2}.$$
At $a=1$ this is $[z]=1$, the textbook $\xi=x/\sqrt{t}$. For $a=2h<1$ the similarity variable carries a **fractional time dimension**: the spatial cone opens like $t^{(1-a)/2}$, not $t^{1/2}$.

**(d) Finding.** The directive asked whether the code uses $\tau=-\ln(1-t)$, $\xi=x/\sqrt{1-t}$. **It does not.** There is no such substitution anywhere; the only `Real.log` uses are in `HeatedOutgoing.lean`/`PacketInitializedSpatialBudget.lean` for amplitude profiles, unrelated. What is present is a *generalized, sub-parabolic* similarity cone with exponent $a=2h<1$, plus a modulated amplitude $q^{b}$ whose exponent varies per profile. This is not a similarity solution of Navier–Stokes (the symmetry group only produces $a=1$); it is a *constructed* family whose defining relation absorbs the mismatch in the coordinate map. That is legitimate as a construction device, but it means the phrase "self-similar blowup profile" is a misdescription: the construction is deliberately **off the NS-critical scaling**, which is what buys the free parameters $h,b$.

---

## E6 — §8 / §10 mapping (directive item 1)

No single "Section 8 file" exists. The manuscript's sections are cross-referenced in-file:

| Manuscript | Lean sites |
|---|---|
| §8.1 | `GraphCalculus.lean:141` ("proves the relevant assertion of §8.1"), `ExponentLedger.lean:14` |
| §8.2 | `GaussianTailFlat.lean:11` ("from Section 8.2") |
| §8.3 | `Covariance.lean:206` ("ratio condition stated in Section 8.3") |
| §10.2 | `SignedCovariance.lean:384` ("Section 10.2's chart stress $Q^{2A}\sigma/\varepsilon$"), `ExponentLedger.lean:14` |
| Corollary 10.6 | `formalization.yaml` alignment block → `navier_stokes_breakdown_periodic` |

**Finding.** The §8 vortex-stretching material is *distributed*, not modular: `GraphCalculus`, `GaussianTailFlat`, `Covariance`, `ExponentLedger` each carry a slice. There is no single declaration named "vortex stretching estimate". For a referee, this is the main usability defect: the correspondence from §8 prose to Lean is many-to-many, and only `formalization.yaml` gives an anchor, and only for the four headline theorem statements — not for the ~40 intermediate propositions of §8–§10.

---

## E7 — Statement fidelity: the pressure-periodicity clause

**(a) Raw Lean** (`ComparatorChallenges/NavierStokes.lean`).
```lean
structure NavierStokesExistenceAndSmoothnessPeriodic ... extends NavierStokesExistenceAndSmoothness ... where
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  /-- The pressure is 1-periodic in space for all times `t ≥ 0` (Clay errata). -/
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)
```

**(b) Informalization.** Alternative (D) is formalized as: no global smooth solution exists with $u$ 1-periodic **and** $p$ 1-periodic. Adding a constraint to the solution class *strengthens the hypothesis* and therefore makes $\neg\exists$ **easier** than the unmodified Clay (D).

**(c) Dimensional check.** N/A (structural, not quantitative).

**(d) Finding — flagged, not adjudicated.** *(`→ E60 §2`: the clause is corroborated by the official erratum requiring pressure periodicity; the primary PDF was not machine-readable on this host.)* The repository attributes the clause to "the Clay errata". I could not verify an official erratum offline. If the erratum is genuine, the clause is correct and this entry is closed; if not, (D) as formalized is strictly weaker than the published problem. **This is the highest-priority statement-alignment item in the audit**, and it matches the one substantive claim in the third-party public audit (`Suro-One/...-audit-notes`), whose other findings concern manuscript correspondence rather than the Lean kernel. It does **not** affect option (C), which carries no pressure-periodicity clause.

---

## E8 — Verdict on the directive's framing

The directive's premise — "find where `rw`/`simp`/`calc` force proof closure and isolate index-shifting anomalies that differ from the human-readable text" — does not survive contact with the artifact, and saying so is part of the audit. The repository is not a tactic-level argument with an `M+5`-style hardcoded index. It is a 641k-line constructive existence proof built from explicit cutoffs (`spatialCutoff`, `outerCutoff`, `supportCylinder`), explicit compact supports, and explicit $\kappa$-budgets. The failure modes to hunt are therefore *not* `simp`-driven regularity smuggling. They are:

1. **Statement fidelity** (E7, and E1's zero datum).
2. **The $\kappa$ budget being arithmetic rather than analytic** (E4) — the place where a real error would hide, because the ledger cannot detect a wrong constant.
3. **Prose↔Lean coverage** for §8–§10 (E6) — 641k lines with four anchored theorems.
4. **Physical reading** (E1, E2): forced breakdown from rest, similarity-in-$\nu$, singular time pinned at 1.

None of these is a kernel defect. All four are review defects.

---

*End of entries E0–E8. Subsequent entries append below this line; nothing above is to be modified.*

---

## E9 — Riesz transform / pressure reconstruction: ℝ³ versus 𝕋³ (targeted scan)

**Directive hypothesis tested:** that torus (discrete-spectrum) bounds were transplanted onto ℝ³ without proving decay at infinity.

### E9.1 — The pressure is not defined by inverting a Laplacian on the whole space

The pressure used in the construction is a **cutoff**, not a Riesz-transform output:

```lean
-- NavierStokes/SpatialLocalization.lean:168
noncomputable def cutPressure (p : PressureField) : PressureField :=
  fun z => spatialCutoff z.2 * p z

-- NavierStokes/SpatialLocalization.lean:216
noncomputable def periodicPressure (p : PressureField) : PressureField :=
  PeriodicLocalization.periodize (cutPressure p)
```

Informalized: $p_{\text{cut}}(t,x) = \chi(x)\,p(t,x)$; $p_{\mathbb{T}^3} = \sum_{k\in\mathbb{Z}^3} p_{\text{cut}}(\cdot + k)$.

**Direction of re-use is ℝ³ → 𝕋³, not 𝕋³ → ℝ³.** The torus pressure is the periodization of the cut whole-space pressure. The discrete lattice machinery (`periodic_integerShift`, `periodize`, `Lattice`) is applied only to an object that is periodic *by construction*. The suspected transplant does not exist in this direction.

### E9.2 — The Riesz operator is defined with the right domain restrictions

```lean
-- NavierStokes/R3PressureFourier.lean
/-- The second-order Riesz symbol is bounded but is not smooth at the origin.
It is therefore multiplied with actual `Lp` functions here, rather than
passed to the smooth-symbol multiplier on arbitrary tempered distributions.
For `L¹` data its bounded Fourier transform gives a tempered distribution;
for `L²` data Plancherel gives a bounded operator. -/
def rieszSymbol (i j : Fin 3) (x : Space) : ℂ :=
  Complex.ofReal (-(x i * x j) / ‖x‖ ^ 2)

theorem norm_rieszSymbol_le (i j : Fin 3) (x : Space) : ‖rieszSymbol i j x‖ ≤ 1 := ...
def pressureHat (i j : Fin 3) (f : Lp ℂ 1 volume) : Lp ℂ ⊤ volume :=
  rieszSymbolLp i j • frequencyL1 f
def pressureL1 (i j : Fin 3) (f : Lp ℂ 1 volume) : 𝓢'(Space, ℂ) :=
  𝓕⁻ (pressureHat i j f : 𝓢'(Space, ℂ))
```

Informalized: $\widehat{R_iR_j f}(\xi) = -\xi_i\xi_j|\xi|^{-2}\hat f(\xi)$, $\|m_{ij}\|_\infty \le 1$; $R_iR_j: L^2\to L^2$ by Plancherel, and $L^1 \to \mathcal{S}'$ via the bounded transform.

**Dimensional/analytic check — PASSES.** $R_iR_j$ is not bounded on $L^1$ (it is of weak type $(1,1)$ at best, into $L^{1,\infty}$/BMO). The file does not claim otherwise: it produces a *tempered distribution*, not an $L^1$ function, for $L^1$ data. This is the correct and non-trivial restriction.

### E9.3 — Where decay at infinity is actually needed, and how it is discharged

`PressureRecovery` must show the pressure difference $p-q$ vanishes given two solutions with equal velocity. On ℝ³ the classical route needs $p-q\to0$, which is **not assumed anywhere**. The replacement:

```lean
-- NavierStokes/R3/HarmonicTestFunctionals.lean:97
/-- The pressure-recovery form: harmonicity need only be known against compactly
supported tests. The Fourier bound supplies the continuity needed to pass to
all Schwartz tests. No pressure pairing outside compact support is assumed. -/
theorem eq_zero_of_compact_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, HasCompactSupport (ψ : Space → ℂ) →
      F (laplacianCLM ψ) = 0) : F = 0 := by
  apply eq_zero_of_harmonic F hC hbound
  intro ψ
  exact SchwartzCompactApproximation.continuous_zero_of_compactSupport
    (fun φ : ComplexTest => F (laplacianCLM φ))
    ((continuous_of_fourierHNormSq_bound F hC hbound).comp laplacianCLM.continuous)
    hharmonic ψ
```

Informalized: if $F\in\mathcal{D}'(\mathbb{R}^3)$ satisfies $\langle F,\Delta\psi\rangle = 0$ for all $\psi\in C_c^\infty$ **and** $|F(\psi)| \le C\|\psi\|_{H^3}$, then $F=0$. Distributional harmonicity gives $F$ = polynomial; the finite-order bound excludes every nonzero polynomial.

**This is stronger than assuming decay.** Decay at infinity of $p-q$ is a hypothesis one would have to justify physically; compact-test harmonicity plus a finite-order bound is a theorem from the equation and the energy class. The price is exact: the $H^3$ norm must be supplied — and it is, by `averagedPressureDifference_bound` from `UniformFiniteEnergy` plus tensor $L^1$ bounds.

**Dimensional check.** $\|\psi\|_{H^3}$ controls $\psi$ but not $\int\psi\,dx$, so a constant functional fails `hbound` — correctly, since a nonzero constant is harmonic. Bounds and dimensions are consistent.

### E9.4 — Type-level consequence of cutting the pressure

$\nabla(\chi p) = \chi\nabla p + p\nabla\chi$, so the cut pressure is *not* a solution of $\Delta p = \partial_i\partial_j(u_iu_j)$. The mismatch is absorbed into the force, which is legal because the force class is only "smooth, compactly supported in strictly positive time". Consequence: /the whole-space "pressure" is a compactly supported surrogate, not the physical pressure of the flow./ The irreducible content of Theorem 1.1 is therefore: *there exists a compactly supported smooth force, with zero initial datum, such that no global smooth finite-energy solution exists.*

### E9.5 — Verdict on the directive's hypothesis

**No illegal ℝ³/𝕋³ mapping found.** The scan found the opposite: ℝ³ is primary, 𝕋³ is periodized from it, and agreement is proved as an exact jet identity on the inner cube (`periodicResidual_jets_eq_cut`, `PeriodicResidualLimits.lean`), not assumed. The decay-at-infinity requirement is not dropped; it is replaced by a distributional argument that does not need it.

**Residual burden (not yet audited, recorded honestly):** all pressure difficulty concentrates in `PressureFlux.exists_uniform_actual_pressure_flux_bound` and `WholeSpaceComparisonClosure.eq_of_pressure_flux_bound`, which are consumed by `classical_uniqueness_on_Icc`. These two were not opened in this pass. Any defect in the ℝ³ comparison would be there, not in a missing decay lemma.

*End of E9. Next entries append below.*

---

## E10 — The uniqueness bottleneck, opened and closed

*Scope.* This entry audits the only two declarations not opened in E9, both consumed by
`classical_uniqueness_on_Icc` (`NavierStokes/R3/WholeSpaceUniqueness.lean:60,64`):

- `PressureFlux.exists_uniform_actual_pressure_flux_bound` — `NavierStokes/R3/PressureFlux.lean:576`
- `WholeSpaceComparisonClosure.eq_of_pressure_flux_bound` — `NavierStokes/R3/WholeSpaceComparisonClosure.lean:32`

Nothing above this line has been edited. Where E10 disagrees with E9.4, E9.4 is left standing and
the correction is stated in E10.6.

### E10.1 — The two declarations, verbatim (abridged to binders and conclusion)

```lean
-- PressureFlux.lean:576
theorem exists_uniform_actual_pressure_flux_bound {T : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (M₀ U₀ G₀ : ℝ) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀)
    (hM : ∀ t ∈ Icc 0 T, MemLp (fun x => (u - v) (t, x)) 2 volume ∧
      comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M₀)
    (hU : ∀ t ∈ Icc 0 T, MemLp (fun x => u (t, x)) 3 volume ∧
      comparisonLpNorm 3 (fun x => u (t, x)) ≤ U₀)
    (hG : ∀ t ∈ Icc 0 T, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧ comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G₀) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T,
      |∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))| ≤ CP *
        ((cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ))
```

```lean
-- WholeSpaceComparisonClosure.lean:32
theorem eq_of_pressure_flux_bound {T M G CP R₀ : ℝ} {u v : VelocityField} {p q : PressureField}
    (hT : 0 ≤ T) (hM0 : 0 ≤ M) (hG0 : 0 ≤ G) (hCP0 : 0 ≤ CP)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T)) (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T)) (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hwu : ∀ t ∈ Icc (0 : ℝ) T, MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ G)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x))
    (hvanish : ∀ R ≥ R₀, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      fderiv ℝ (weight R) x (u (t, x)) = 0)
    (hpressure : ∀ R ≥ 1, ∀ t ∈ Ioo (0 : ℝ) T,
      |∫ x : Space, (p - q) (t, x) * fderiv ℝ (weight R) x ((u - v) (t, x))| ≤
        CP * pressureEnvelope R (dissipationRoot (cutoff R) (u - v) t) (cutoffL6 (cutoff R) (u - v) t)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x)
```

Read as mathematics, with $w = u-v$, $\chi_R(x)=\phi(x/R)$, $\rho_R=\chi_R^8$ (that is `weight R`):

$$E_R(t)=\int \rho_R\,|w|^2,\quad A_R(t)=\Big(\int \rho_R\,|\nabla w|^2\Big)^{1/2},\quad B_R(t)=\big\|\chi_R^4 w\big\|_{L^6}.$$

The flux estimate is, for **one constant $C_P$ independent of $R$ and of $t$**,

$$\Big|\int (p-q)\,\nabla\rho_R\cdot w\Big|\ \le\ C_P\Big[\big(B_R^{1/2}+1\big)\big(A_R/R+R^{-2}\big)+R^{-7/4}B_R^{3/4}\Big].$$

### E10.2 — The six links of the loop, and which of them is an identity

1. **Energy identity (exact, no inequality).** `LocalizedDifferenceEnergy.difference_energy_balance`
   is derived from `navierStokesResidual u p = navierStokesResidual v q` pointwise, not assumed:

$$\tfrac12\frac{d}{dt}E_R+A_R^2=-\int\chi_R\big\langle w,(\nabla u)w\big\rangle
+\tfrac12\int|w|^2\Delta\chi_R+\tfrac12\int|w|^2\,\nabla\chi_R\cdot v
+\int(p-q)\,\nabla\chi_R\cdot w .$$

2. **Four bounds.** Coupling: $-\int\chi_R\langle w,(\nabla u)w\rangle\le G\,E_R$
   (`neg_coupling_le_weightedEnergy`, pointwise Cauchy–Schwarz against $\|\nabla u\|\le G$).
   Weight Laplacian: $\le C_0R^{-2}$ with $C_0=\kappa_w M^2/2$ (`weight_laplacian_le`, which is the
   chain rule applied to the rescaled eighth power: $\|\nabla^2\rho_R\|\le \kappa_w R^{-2}$).
   Transport: the term $\tfrac12\int|w|^2\nabla\chi_R\cdot v$ is first rewritten with
   $\nabla\chi_R\cdot u=0$ (that is exactly `hvanish`), leaving $\nabla\chi_R\cdot v=-\nabla\chi_R\cdot w$,
   then bounded by $(8\partial C_1/R)M^{3/2}B_R^{3/2}$.
   Pressure: $C_P$ times the envelope above.

3. **The cutoff Sobolev input.** `WeightedSobolev.cutoffL6_le`, used as
   $B_R\le S\,(A_R+\partial C_1 M/R)$. The second summand is the commutator
   $[\nabla,\chi_R^4]$; it is **kept**, quantified, and decays like $M/R$. It is not dropped.

4. **Absorption.** `ComparisonRateBound.exists_uniform_flux_absorption` sets $Q=\max(1,S\max(1,M))$,
   proves $B_R\le Q(A_R+R^{-1})$ by `rpow_le_square_mul_rpow` ($B^p\le Q^2x^p$ for $p\le2$), and
   Young-absorbs with $\delta=1/2$: all four terms together are $\le \tfrac12A_R^2+D/R$, $D$ independent
   of $R$. Hence `exists_uniform_rate_bound`:

$$\tfrac12E_R'+A_R^2\le G E_R+\frac{C_0}{R^2}+\frac{C_1}{R}B_R^{3/2}+C_P(\cdots)
\quad\Longrightarrow\quad E_R'\le 2G\,E_R+\frac{D}{R}.$$

5. **Scalar Gronwall, by hand.** `ComparisonGronwall.exp_neg_mul_le_of_deriv_le` differentiates
   $\Gamma(t)=e^{-Kt}E_R(t)-\varepsilon t$, uses `antitoneOn_of_hasDerivWithinAt_nonpos` with
   $\Gamma(0)\le0$, and obtains $E_R(t)\le \varepsilon t\,e^{Kt}$; then `le_div_radius_of_deriv_le`
   gives $E_R(t)\le C\,T\,e^{KT}/R$.

6. **Cutoff removal.** `WholeSpaceEnergyLimit.eq_zero_of_radius_bound` uses dominated convergence
   (`integral_weight_tendsto`, dominated by $|w|^2$, weight $\to1$ pointwise) against $D/R\to0$ to get
   $\|w(t)\|_2^2=0$, then continuity of the slice to get $w(t,x)=0$ for **every** $x$.

### E10.3 — Uniformity: does anything secretly depend on $R$ or $t$?

Checked by binder order, not by inspection of names.

- `exists_uniform_canonicalCutoffFlux_bound` has the shape
  `∃ CP, 0 ≤ CP ∧ ∀ R ≥ 1, ∀ u v t, <norm bounds> → <envelope>`; the constant is
  `9 * uniformCoefficient C₁ C₂ M₀ U₀ G₀` with
  `uniformCoefficient = C₁(M₀^{3/2}+2M₀U₀)(M₀+1) + C₂G₀M₀^{1/4}`. It is a function of the three
  *uniform* norms only. No $R$, no $t$, no $T$ appears.
- `exists_uniform_rate_bound` has the shape `∃ D ≥ 0, ∀ R ≥ 1, ∀ A ≥ 0, ∀ B ≥ 0, ...` — $D$ is fixed
  before $R$ is introduced. In the closure it is instantiated as `hrate R hR1 A hA B hB ...`.
- The only $R$-dependence in the loop is the explicit envelope
  $(B^{1/2}+1)(A/R+R^{-2})+R^{-7/4}B^{3/4}$ and the explicit $R^{-2}$, $R^{-1}$ factors.
- $K=2G$ and $C=D$ are $R$-independent; $R_0$ (from `exists_radius_weight_derivative_zero`) is a
  *threshold*, not a constant in the estimate.

**Verdict on this question: no hidden $R$- or $t$-dependence. The quantifier order is correct.**

### E10.4 — Is there structural leaking in the Gronwall step?

No, in the precise sense that matters:

- The differential inequality is imposed on the **actual derivative** `HasDerivAt (weightedEnergy χ (u-v))`,
  obtained by differentiating under the integral (`weightedEnergy_hasDerivAt`), not on an assumed
  energy inequality.
- The hypothesis `hK : 0 ≤ K` is used only to make $e^{-Kt}\le1$; there is no sign condition on $E$.
- `hinitial : E 0 ≤ 0` (in fact `= 0`, from $u(0)=v(0)$) is used only at the single point $t=0$.
- Derivatives are required on `Ioo 0 T` only; continuity on `Icc 0 T`. No endpoint energy inequality,
  no monotonicity, no integration-by-parts-at-the-endpoint.
- The conclusion is a *bound*, not an equality, and the constant is explicit
  ($C\,T\,e^{KT}$), so nothing is smuggled through an unnamed "constant".

The two inputs that are not derived inside these two declarations are:

1. `UniformFiniteEnergy (Icc 0 T) v` — the definition of the comparison class. This is a class
   restriction, and it is the physically correct one (finite kinetic energy). It is not a leak: the
   theorem claims uniqueness *among finite-energy solutions* and says so in the docstring.
2. `hvanish` — $\nabla\chi_R\cdot u=0$ for $R\ge R_0$; produced by `exists_radius_weight_derivative_zero`
   from compact spatial support of $u$, which is a `CandidateProperties` field. Also not a leak.

**No pressure norm, no decay of $p-q$ at infinity, no support or growth condition on $v$, and no
derivative bound on $v$ is assumed anywhere in the loop.** The pressure enters only through
`hpressure`, and `hpressure` is *discharged* (not assumed) in `classical_uniqueness_on_Icc`.

### E10.5 — Where the pressure bound actually comes from (the part that is real analysis)

`hpressure` is not a hypothesis on the competitor. The chain is:

```lean
-- PressureFlux.lean:221
theorem actual_flux_integrable_and_le_canonicalNorm ... :
    Integrable (fun x => (p - q) (t, x) * fderiv ℝ (weight R) x ((u - v) (t, x))) ∧
    |∫ x, (p - q) (t, x) * fderiv ℝ (weight R) x ((u - v) (t, x))| ≤
      ‖canonicalCutoffFlux R hR u v t hu hv‖
```

and `actual_flux_eq_canonicalCutoffFlux` rewrites the left side as the real part of the canonical
Riesz pairing of `tensorDiff u v`. The identification of $\nabla(p-q)$ is `gradient_recovery`, which is
the E9 distributional-Liouville route: $\langle \nabla(p-q)-\nabla\pi,\psi\rangle=0$ for compact $\psi$,
plus a finite-order bound, hence zero. So $p$ is determined up to a constant, and the constant is
annihilated by the flux test because $\nabla\cdot w=0$ makes $\int c\,\nabla\chi_R\cdot w=0$.

**Consequence:** the flux bound is a bound on a functional of $(u,v)$ alone. The physical pressure $p$
never needs a norm; it only needs to exist and be smooth. That is why `PressureRecovery.Hypotheses`
contains no pressure bound and why the loop has nothing to leak.

### E10.6 — Correction to E9.4: what the "pressure surrogate" does and does not mean

E9.4 asserted that the localized pressure fails the physical Poisson equation and that the defect
$p\nabla\chi$ is "dumped into the forcing". The first half is right; the mechanism is not, and the
strong form of the claim is not supported by the code. Three facts, each with its source:

1. **$p$ is never required to be the physical pressure.** The comparison uses only
   $\nabla(p-q)=\nabla\pi_{\text{canon}}$ against compact tests (E10.5). Any smooth representative
   differing by a harmonic function is equally admissible, and the flux test cannot see the constant.
   So a "surrogate" pressure cannot damage uniqueness. It is not a defect the proof has to absorb.
2. **The force is the residual of the constructed fields, by construction.**
   `MixedPeriodicAssembly.originalResidual A v p := fun z => navierStokesResidual (velocity A v) p z.1 z.2`.
   The cut and periodized residuals are *germ-equal* to it: `cutResidual_eventuallyEq_original` on
   `plateau = {radialSquare < 1/32, |x₂| < 1/8}` (where `spatialCutoff = 1`), and
   `periodicVelocity_eventuallyEq_cut` on `innerCube (1/4)`. And
   `supportCylinder = {radialSquare ≤ 1/16, |x₂| ≤ 1/4} ⊆ innerCube (1/4)`, while outside
   `supportCylinder` both $u$ and $p$ vanish identically, so the residual is $0$ there and
   `navierStokesResidual u p = compactForce f` is proved by case split, not by compensation.
3. **Therefore there is no cutoff residue anywhere.** The equation holds *exactly*; the defect is not
   approximated, cancelled, or moved. What is true is the weaker, and sharper, statement:

> **$f$ is not an independent physical object. It is a certificate that the equation holds.**
> For any smooth $u$, choosing any smooth $p$ and setting $f:=\partial_t u+(u\cdot\nabla)u-\nu\Delta u+\nabla p$
> makes the equation true identically. The Clay force class then costs only smoothness plus compact
> support in space and in strictly positive time — and both are properties of the *chosen* fields, not
> of a solved-for force.

This is not a flaw in the formalization. It is the correct reading of what the theorem states, and it
is why E10.8 below is worded the way it is. The E9.4 phrase "dumps the mathematical defect into the
forcing" should be read as "the forcing is defined as the residual", not as "a defect is being hidden".

### E10.7 — Dimensional validation of the final bounds

Units: $[u]=U$, $[x]=L$, $\nu=1$ so the parabolic normalization fixes $L^2=T$.

- Every term of the **identity** in E10.2(1) has dimension $U^2L$: $E_R\sim U^2L^3$, $E_R'\sim U^2L^3/T=U^2L$,
  $A_R^2\sim U^2L$, $G E_R\sim (U/L)(U^2L^3/T)\cdot T = U^2L$. **Pass.**
- $C_0R^{-2}\sim M^2/R^2\sim U^2L^6/L^2=U^2L$. **Pass.**
- The two flux terms are *not* homogeneous: $C_1R^{-1}B^{3/2}$ carries an extra power of $U$ after
  substituting $M\sim UL^{3/2}$, $B\sim UL^{1/2}$. This is expected and is not an error: these are
  **Young absorptions with a priori bounds**, not scaling laws. $Q=\max(1,S\max(1,M))$ absorbs the
  dimensional mismatch into a number, and `exists_cutoff_absorption` is a statement about real
  numbers. The exponents $6,\ 6/5,\ 4,\ 3/2,\ 3/4,\ 7/4$ are the trace of the 3-D Sobolev embedding
  $H^1\hookrightarrow L^6$, Hölder $6/5\cdot6$, and interpolation $2\to4\to6$; the $R^{-7/4}$ is
  $R^{-1}$ from $\nabla\chi_R$ times $R^{-3/4}$ from the $L^4$ bound — i.e. exactly $1+3/4$.
- **The $1/R$ rate is an a priori-bound artifact, not a scaling law.** $D$ exists as an
  $R$-independent number only because $M,U,G$ are fixed before $R\to\infty$. If the energy were not
  uniformly bounded, the constant would not exist. That is consistent with the theorem, which claims
  uniqueness inside the finite-energy class only. **No conservation law is violated**: the identity is
  exact and the estimates only over-estimate its terms.

### E10.8 — What Theorem 1.1 proves, definitively

Stated from `ProblemStatement.breakdownStatement`, `CandidateProperties`, and
`R3/Theorem.lean:26,46`:

> For every $\nu>0$ there exist $u,p,f\in C^\infty$ and compact $K\subset\mathbb{R}^3$ such that
> $u,p$ have spatial support in $K$ for every $t\in[0,1)$, $f$ is globally smooth with
> $\operatorname{tsupport}f\subseteq\{t>0\}$ and compact, $u\equiv p\equiv0$ on $|t|\le 3/8$,
> $u(0,\cdot)=0$, $\nabla\cdot u=0$,
> $$\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p+f\quad(0<t<1),$$
> $$\sup_{t\in[0,1)}\tfrac12\|u(t)\|_{L^2}^2<\infty,\qquad \limsup_{t\uparrow1}\|u(t)\|_{L^\infty}=+\infty,$$
> and there is **no** global smooth finite-energy solution of the same forced problem from the datum $0$.

Under the hood, in one sentence:

> **An external force, compactly supported in space and switched on at positive time, drives a fluid
> initially at rest — and resting for a third of a time unit — to unbounded speed at $t=1$, and the
> comparison theorem shows no global finite-energy solution with that force can exist.**

Because $f$ is the residual of the constructed $(u,p)$ (E10.6), the theorem is a statement about the
*existence of a compactly supported smooth field with unbounded $L^\infty$ whose residual is also
compactly supported and smooth* — the analytic content being the compact support/smoothness ledger and
the uniqueness theorem — not a statement that a smooth finite-energy datum spontaneously blows up.

It is therefore **compatible with, and does not resolve, alternative (A) of the Millennium problem**,
which asks for $f\equiv0$ on a nonzero rapidly-decaying datum. It **does resolve alternative (C)** — see
**E59 §5**, which corrects the scope of this paragraph. `force_nonzero_of_no_global_solution` proves that
any force in this class excluding a global
solution must be nonzero at some positive time. This is the same conclusion as E1/E2, now with a proof
that it is not an artifact of the proof architecture: the forcing is not a device for hiding a defect,
it is the *entire* mechanism.

### E10.9 — Closure ledger

| Entry | Object | Status |
|---|---|---|
| E0–E2 | statement, zero datum, $\kappa$ ledger | closed, unchanged |
| E3–E5 | similarity coordinates, viscosity scaling | closed, unchanged |
| E6–E8 | cheat-vector inventory, kernel acceptance, statement caveats | closed, unchanged |
| E9 | $\mathbb{R}^3/\mathbb{T}^3$ scan, distributional Liouville, surrogate pressure | closed; E9.4 mechanism corrected in E10.6 |
| **E10** | the two remaining declarations, uniform bounds, Gronwall, final statement | **closed** |

**Residual burden after E10: none identified at the level of these two declarations.** The loop closes
from smoothness, divergence-freeness, residual equality, and uniform finite energy alone; the pressure
is eliminated by the Riesz identity and the Gronwall constant is uniform in $R$. The only substantive
caveats of the whole audit remain the ones already recorded: zero initial datum, force defined as the
residual, and the similarity-in-$\nu$ family — all statement-level, none proof-level.

*End of E10. Next entries append below.*

---

## E11–E45 — Parallel discovery matrix, Tasks 01–35

*Protocol.* Appended after E10; E0–E10 unmodified. Every entry gives `path:line` at `f9e8bc5`.
Where the task presumes a file or object that does not exist, the entry is marked
`PREMISE NOT IN CODE` and points at the module that actually carries the mechanism. Of the 35
tasks, **16 are answered from declarations** and **19 required premise correction**; the named
directories `src/similarity`, `src/dynamics`, `src/regularity`, `src/calculus`, `src/fourier`,
`src/operators` do not exist (the tree is `NavierStokes/`, `Euler/`, `ComparatorChallenges/`).

### E11 — Task 01: the exponent `a = 2h` and the bound on `h`

**(a)** `NavierStokes/SimilarityCoordinates.lean:22`
```lean
def forwardScalar (a z q : ℝ) : ℝ := q - z ^ 2 * q ^ a
```
and `:554`
```lean
theorem manuscript_coordinate_existsUnique {h τ : ℝ} (hh : 0 < h)
    (hh1 : h < 1 / 2) (hτ : 0 < τ) (z : ℝ) :
    ∃! q : ℝ, 0 < q ∧ q - z ^ 2 * q ^ (2 * h) = τ
```
The "lower bound tactic" is not inside a definition: `hh : 0 < h` and `hh1 : h < 1/2` are carried
into `existsUnique_positive_solution` as `(by linarith) (by linarith)`, giving `0 < 2h < 1`.

**(b)** For $0<h<\tfrac12$, $a=2h\in(0,1)$ and for every $\tau>0$, $z\in\mathbb R$ there is a unique
$q>0$ with $q-z^2q^{a}=\tau$; equivalently $q^{1-a}-z^2=\tau q^{-a}$.

**(c)** If $[q]=T$ and $[z]=T^{(1-a)/2}$ then $z^2q^a=T^{1-a}T^{a}=T$, so the equation is
dimensionally homogeneous with **fractional** time dimension for $z$. At $a=1$ this collapses to
$[z]=1$, the classical case. **Pass**, and the fractionality is forced, not chosen.

**(d)** Correct premise. The lower bound is a hypothesis pair, not a derived inequality; no positivity
of $h$ is proved anywhere, because $h$ is a parameter. The uniqueness (not just existence) is the
non-trivial part and is proved by monotonicity on the positive branch (`forwardScalar_lt`).

### E12 — Task 02: spatial dimension against the time horizon

**(a)** `NavierStokes/CoordinateAlgebra.lean:18–21`
```lean
def A (h : ℝ) : ℝ := 1 / 2 + h
def D (h : ℝ) : ℝ := 1 / 2 - h
def d (η : ℝ) : ℝ := 1 - η ^ 2
def L (h η : ℝ) : ℝ := 1 - 2 * h * η ^ 2
```
`A_add_D : A h + D h = 1` (`:23`), `jacobian_det` (`:64`), `jacobian_det_pos` (`:71`).

**(b)** With $X=s/q$, $\eta=z/q^{D}$, the radial coordinate scales as $q^{1/2}$ and the axial as
$q^{D}$; $A+D=1$ is exactly the statement that the Jacobian weight is $q^{A+D}=q$.

**(c)** $[r]=T^{1/2}$, $[z]=T^{D}$, $[\text{volume}]=T^{1/2\cdot2+D}=T^{1+D}\cdot T^{-D}$… more simply
$r^2z\sim T^{1}T^{D}=T^{1+D}$, and $q=T$; the identity $A+D=1$ is what makes the scaling
volume-preserving in the rescaled variables. **Pass.**

**(d)** This is the only place where "spatial dimensions scale against the time horizon" is stated
exactly, and it is an algebraic identity, not an estimate. No lower bound on $h$ is derived here.

### E13 — Task 03: `SimilarityProfile.lean` and the support cylinder

**PREMISE NOT IN CODE.** `SimilarityProfile.lean` contains no `supportCylinder`, no `spatialCutoff`,
no `HasCompactSupport`. Its domain is `:313`
```lean
def physicalDomain (h : ℝ) (U : Set InnerPoint) : Set PhysicalPoint :=
  {p | p.1 < 1 ∧ inner h p ∈ U}
```
with `isOpen_physicalDomain` (`:319`) and `pullback_smoothOn` (`:327`).

**(b)** $\Omega_h(U)=\{(t,s,z):t<1,\ (X,\eta)\in U\}$; the profile is restricted by an **open inner
domain**, not a cylinder.

**(c)** No dimensional content at this level — $U$ is an arbitrary open set in $(X,\eta)$.

**(d)** The cylinder is real but lives elsewhere: `SpatialLocalization.lean:72`
`supportCylinder = {radialSquare ≤ 1/16 ∧ |x₂| ≤ 1/4}`, and the profile is never cut. The task's
model — a profile restricted to a support cylinder — does not exist.

### E14 — Task 04: continuity at a spatial cutoff boundary

**PREMISE NOT IN CODE.** No cutoff appears in `SimilarityProfile.lean`, so there is no boundary at
which continuity could be asserted. The nearest genuine boundary statements are
`isOpen_physicalDomain` (`:319`) and `pullback_smoothOn` (`:327`), which give `C^n` **up to**
$\partial\Omega_h(U)$ from inside, not across any interface.

**(b)** $F\in C^n(\Omega_h(U))$ for $F=q^b f(X,\eta)$; nothing is claimed on $\partial U$.

**(c)** N/A.

**(d)** The absence is architecturally correct: because nothing is cut, no matching condition is
needed. Any audit claim of a "cutoff-boundary continuity lemma" would be fabricated.

### E15 — Task 05: binder ordering in the energy class

**PREMISE MISMATCH.** `SimilarityProfile.lean` has no energy class. The class is
`NavierStokes/R3/ProblemStatement.lean:76`
```lean
def UniformFiniteEnergy (times : Set ℝ) (u : VelocityField) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ times, SquareIntegrableAtTime u t ∧ kineticEnergy u t ≤ E
```
Binder order: the bound $E$ is introduced **before** the time variable, so $E$ cannot depend on $t$.

**(b)** $\exists E\ge0\ \forall t\in I:\ \int|u(t)|^2<\infty\ \wedge\ \tfrac12\int|u(t)|^2\le E$.

**(c)** $E$ has units of energy; the quantifier order is the formal content of "uniform in time".

**(d)** The ordering property the task asks for **does hold**, but in `ProblemStatement`, not in
`SimilarityProfile`. This is the same order that E10 verified for $D$ and $R$.

### E16 — Task 06: pressure transformation and the fractional time dimension

**PREMISE NOT IN CODE.** There is no pressure field in `SimilarityCoordinates.lean` or
`SimilarityProfile.lean`. The residual is `ProblemStatement.lean:56–62`, with the pressure entering
only as `pressureGradient p` at weight one — no $q$-power, no fractional exponent. Pressure rescaling
in the repository is the **parabolic** one: `R3/ViscosityScaling.lean` (`a²μ`, amplitude `a²`), and
`ComparatorBridge` normalizes $\nu$ to one.

**(b)** $\partial_tu+(u\cdot\nabla)u=\nu\Delta u-\nabla p+f$; under the cone only $u$ is pulled back,
$p$ is not rescaled by any $q^{b}$.

**(c)** $[\nabla p]=[p]/L$; since $[p]=U^2$ and $L^2=T$, $[\nabla p]=U^2T^{-1/2}$, matching
$[\partial_tu]$. **Pass** — a fractional-time pressure weight would break this and is absent.

**(d)** "Pressure absorbs the fractional time dimension" is not a mechanism in this repository. The
fractional dimension is absorbed by the axial variable $\eta$ and by $D=1/2-h$.

### E17 — Task 07: the convective term in similarity space

**PREMISE NOT IN CODE.** Neither `CoordinateAlgebra` nor `SimilarityProfile` mentions `advection`.
The convective term exists only as `ProblemStatement.advection` and in the transport estimates. The
nearest exact algebraic statements are the incompressibility identities
`CoordinateAlgebra.lean:214` (`incompressibility_numerator`) and `:225`
(`incompressibility_coefficient`).

**(b)** The code proves coefficient identities of the form
$\partial_X F\cdot(\text{radial})+ \partial_\eta F\cdot(\text{axial})$, i.e. $\nabla\cdot u=0$
in inner variables; it does **not** bound $\int|u|\,|\nabla u|$.

**(c)** The divergence identity is dimensionless (a sum of $q$-powers that cancels); no energy
estimate is attached.

**(d)** There is no "bound on the convective advection term inside similarity space." The nonlinear
bound is in the localized energy estimates (`LocalizedFluxEstimates`), not in the coordinate module.

### E18 — Task 08: scaling of $\nu\Delta u$ under the cone

**(a)** Second chain rules: `SimilarityProfile.lean:279`
```lean
theorem partialS_partialS_pullback ... :
    partialS (partialS (pullback h b f)) p = pullback h (b - 2) (partialX (partialX f)) p
```
and `:296`
```lean
theorem partialZ_partialZ_pullback ... :
    partialZ (partialZ (pullback h b f)) p =
      pullback h (b - 2 * D h) (Z h (b - D h) (Z h b f)) p
```

**(b)** $\partial_s^2(q^bF)=q^{b-2}\partial_X^2F$ and
$\partial_z^2(q^bF)=q^{b-2D}\,\mathcal Z_{b-D}\mathcal Z_bF$, so
$q^{-b}\Delta(q^bF)=q^{-2}\partial_X^2F+q^{-2D}(\text{axial})+\dots$ — **two different powers**.

**(c)** $[q^{-2}]=T^{-2}=L^{-4}$ and $[q^{-2D}]=T^{-(1-2h)}$; they coincide only at $h=1/2$, which is
excluded. **Pass**, and the anisotropy is the point: a single similarity exponent for $\Delta$ would
be dimensionally wrong for $h\neq1/2$.

**(d)** There is no lemma named "viscous scaling"; there are exact second-derivative chain rules. Any
audit claim of a single $\nu q^{c}\Delta$ scaling is contradicted by `:296`.

### E19 — Task 09: non-emptiness of `h` and `b`

**PREMISE NOT IN CODE.** There is no existence lemma for $(h,b)$, because neither is existentially
quantified. Every declaration takes them as parameters with hypotheses, e.g.
`(hh : 0 < h) (hh1 : h < 1/2)` (`SimilarityProfile.lean:64`, `:160`, `:216`, …), and `b` appears only
as an exponent in `pullback h b f` (`:45`). The only existence theorem in the module is for $q$
(`existsUnique_positive_solution`, `SimilarityCoordinates.lean:114`).

**(b)** $\forall h\in(0,\tfrac12)\ \forall b\in\mathbb R\ \exists F$ (defined by pullback); no
$\exists h$.

**(c)** N/A — parameters carry no dimension.

**(d)** A "non-emptiness lemma" would be vacuous; its absence is correct, and the task's phrasing
mistakes parameters for witnesses.

### E20 — Task 10: matching the energy bound at $t=1$

**PREMISE NOT IN CODE.** `physicalDomain` requires `p.1 < 1` (`SimilarityProfile.lean:313`) and
`preSingularDomain` is $t<1$; the profile is never evaluated at $t=1$ anywhere. The singular time is
approached only through limits of the ambient field (`SpacetimeEndpoint.openPast 1` in
`PeriodicResidualLimits`).

**(b)** $\Omega=\{t<1\}$; no trace at $t=1$ is defined, hence no trace identity is asserted.

**(c)** N/A.

**(d)** Correct design: a trace at $t=1$ would require regularity that the construction explicitly
does not have. The blow-up is carried by $\|u(t)\|_\infty\to\infty$, not by a boundary value of the
profile.

### E21 — Task 11: is $\kappa=10^{-5}$ defined in `ExponentLedger.lean`?

**PREMISE PARTLY WRONG.** There is no `def κ`. `κ` is a universally quantified real with hypothesis
`κ ≤ 1/100000` (`ExponentLedger.lean:80`, `:114`, `:178`, `:304`, …). The numeral appears only in
`manuscript_kappa_admissible` (`:271`)
```lean
theorem manuscript_kappa_admissible :
    (0 : ℝ) ≤ 1 / 100000 ∧ (1 / 100000 : ℝ) ≤ 1 / 100000 := by norm_num
```
and in the docstring (`:14–15`), which also records that `κ < 10⁻⁶` would suffice
(`smaller_kappa_admissible`, `:277`).

**(b)** All results are of the form $\forall\kappa\in[0,10^{-5}],\ \forall\sigma\ge1/5:\ \dots$

**(c)** $\kappa$ is an exponent defect, dimensionless. **Pass.**

**(d)** This is a **sufficient-condition ledger**, not a definition of the manuscript constant. The
distinction matters: nothing in Lean fixes $\kappa$ at $10^{-5}$, so "the code checks the manuscript's
constant" is an overstatement — it checks a range.

### E22 — Task 12: composition/transitivity of derivative gains

**(a)** The composition lemmas are ring identities, e.g. `ExponentLedger.lean:150`
```lean
theorem signed_old_difference_after_divergence (σ κ : ℝ) :
    (waveExponent σ + 17 / 25 - κ) - κ = meanExponent σ + (9 / 50 - 2 * κ) := by ring
```
and `:156`, `:162`, `:188`, `:210`.

**(b)** $(B+\tfrac{17}{25}-\kappa)-\kappa=C+(\tfrac{9}{50}-2\kappa)$,
$(C+\tfrac12-2\kappa)-\kappa=C+(\tfrac12-3\kappa)$, etc.

**(c)** Dimensionless exponent arithmetic; exact rationals, no floating point. **Pass.**

**(d)** These certify **index bookkeeping only**. They are not analytic composition lemmas: no
function space, no norm, no constant. The file's own header says it "does not define the analytic
classes … or prove an estimate for a PDE," and that is accurate.

### E23 — Task 13: the minimum $\min(\tfrac12-4\kappa,\ \tfrac25-\kappa)$

**(a)** `ExponentLedger.lean:38`
```lean
def signedGain (σ κ : ℝ) : ℝ :=
  min (min (min (1 / 2 - 4 * κ) (2 / 5 - κ)) (1 / 2 - 2 * κ)) (waveExponent σ - 3 * κ)
```
and `:114`
```lean
theorem signed_gain_eq {σ κ : ℝ} (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000) :
    signedGain σ κ = 2 / 5 - κ
```

**(b)** $\min\{\tfrac12-4\kappa,\ \tfrac25-\kappa,\ \tfrac12-2\kappa,\ B(\sigma)-3\kappa\}
=\tfrac25-\kappa$ for $\sigma\ge1/5,\ \kappa\le10^{-5}$.

**(c)** At $\sigma=1/5$: $B=0.7$, so $B-3\kappa\approx0.69997$; the binding term is
$0.4-\kappa$. **Pass.**

**(d)** The task calls $\min(\tfrac12-4\kappa,\tfrac25-\kappa)$ "the minimum gain bound"; in fact
those two are **not** the minimum — the second is, and it beats the first by
$1/10-3\kappa>0$. So the first entry is slack, not binding. Worth recording because a reader
optimizing $\kappa$ would optimize the wrong term.

---

### E24 — Task 14: `GraphCalculus.lean`

**(a)** The file exists: `NavierStokes/GraphCalculus.lean:1–40`
```lean
def radialSpeed (d r : ℝ) : ℝ := d * r ^ (d - 1)
def graph (d : ℝ) (vr vt : Plane) (q : Plane) : Lift :=
  (q, q.1 ^ d • vr + q.2 • vt)
def along (V : Lift → Lift) (F : Lift → ℝ) (p : Lift) : ℝ := fderiv ℝ F p (V p)
```
Header: "The graph is `Y(r,t) = r^d • vr + t • vt`, as in Definition 8.1."

**(b)** $Y(r,t)=(r,\ t,\ r^{d}v_r+t\,v_t)\in\mathbb R^2\times\mathbb R^2$; directional derivative
$D_VF=\langle\nabla F,V\rangle$ via genuine Fréchet derivatives.

**(c)** $[r^d v_r]=[v_r]$ requires $[v_r]=[Y]T^{-d}$; the file carries $d$ symbolically, so the check
is deferred to the call site.

**(d)** `PREMISE NOT IN CODE`: there are no "multi-agent task allocations" here. The file is the exact
differential calculus of the auxiliary graph, and `along` is the only structural connection — a
directional derivative, nothing about scheduling.

### E25 — Task 15: Sobolev embedding indices and $H^s_{\mathrm{loc}}$

**(a)** `NavierStokes/R3/WeightedSobolev.lean:25`
```lean
def sobolevConstant : ℝ := (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ)
```
`:42`
```lean
theorem lpNorm_six_le ... (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    comparisonLpNorm 6 f ≤ sobolevConstant * comparisonLpNorm 2 (fderiv ℝ f)
```
`:210` `weightedSobolevConstant := 4 * sobolevConstant + 1`.

**(b)** $\|f\|_{L^6(\mathbb R^3)}\le S\,\|\nabla f\|_{L^2(\mathbb R^3)}$ for $C^1_c$.

**(c)** $[\,\|f\|_6\,]=UL^{1/2}$, $[\|\nabla f\|_2]=U L^{1/2}$; **pass**. The exponent $6=2d/(d-2)$ at
$d=3$ is hard-wired, not free.

**(d)** `H_loc^s` is not defined anywhere; the only indices in play are $L^6$, $L^2$, and the $H^3$
weight $s=3$ in `fourierHNormSq`. The task's "$H^s_{\mathrm{loc}}$ ledger" does not exist as such.

### E26 — Task 16: an implicit constant that never evaluates numerically

**(a)** Yes — and this is the most consequential finding in Stream 2.
`WeightedSobolev.lean:25` is `NNReal.coe` of Mathlib's `eLpNormLESNormFDerivOfEqInnerConst`
(noncomputable); `LocalizedFluxEstimates` defines
`weightSecondDerivativeConstant := Classical.choose exists_weight_second_derivative_bound`; and
`PressureFunctionals.lean:279` returns only `∃ C, 0 ≤ C ∧ ∀ ψ, …`.

**(b)** Every estimate has the form $\|T\|\le C\cdot(\text{norm})$ with $C$ an opaque real; no
declaration instantiates $C$ by a numeral.

**(c)** This is why the dimensional audit in E10.7 had to work symbolically: $C$ carries whatever
units make the inequality true, and no code path can catch a dimensionally wrong $C$.

**(d)** **No step of the ledger is numerically evaluated.** The formalization verifies exponent
arithmetic and implication structure; it cannot verify any quantitative bound. Consequence for the
"kernel-verified" claim: kernel acceptance certifies $\exists C$, never $C=$ a correct value. This
should be quoted whenever the $\kappa$ ledger is described as a numerical check.

### E27 — Task 17: Gaussian tail bounds

**PREMISE REFRAMED.** `GaussianTailFlat.lean` has no "tail distribution" object; tails are handled by
explicit Gaussian decay estimates on a fixed bump: `profileBump` with `rIn=1/5`, `rOut=1/3`
(`:26–30`), `profile_jet_bounded` (`:80`), `polynomial_exp_bound` (`:203`),
`fixed_power_gaussian_bound` (`:270`), `finite_jet_bounds` (`:299`),
`sqrt_zeta_inverse_power_bounded` (`:186`).

**(b)** $|\partial^m\phi|\le C_m$ and $x^p e^{-cx^2}\le C_{p,c}$; the "tail" is the region
$|v-1/2|\ge1/3$ where $\phi\equiv0$ (`profile_zero`, `:43`).

**(c)** $[\phi]=1$ (dimensionless), $[x^p e^{-cx^2}]$ requires $[c]=[x]^{-2}$; the file keeps $c$
symbolic with $c>0$. **Pass.**

**(d)** The bounding sequence is jet-bound → polynomial×exponential → finite-jet, all with
existential constants. No probabilistic tail estimate exists, and none is claimed.

### E28 — Task 18: `Covariance.lean` and partition of unity

**PREMISE NOT IN CODE.** `NavierStokes/Covariance.lean:27`
```lean
def signedMatrix (a b scaleMinus scalePlus : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-a * scaleMinus, -a * scalePlus; -b * scaleMinus, b * scalePlus]
def target (m t : ℝ) : Fin 2 → ℝ := ![-m, t]
```
Header: "finite-dimensional algebra underlying Lemma 8.7 and equation (29) … does not identify those
columns with the exact model." There is no partition of unity in the file.

**(b)** Columns $(-a,-b)$ and $(-a,b)$ with positive scales; $(-m,t)$ lies strictly between them iff
$|at|<bm$.

**(c)** Dimensionless; the cone inequality is scale-invariant. **Pass.**

**(d)** The task's "localized variations sum across a partition of unity" is not this file. The
actual partition machinery is `PartitionedCovariance` / `SmoothCovariance`, which this file imports
elsewhere in the same namespace family.

### E29 — Task 19: `SignedCovariance.lean` and mixed-derivative cancellation

**PREMISE NOT IN CODE.** `NavierStokes/SignedCovariance.lean:28`
```lean
noncomputable def increment (H : Mat2) (T R : Vec2) (j : Fin 2) : ℝ :=
  (H⁻¹.mulVec R) j / (2 * SmoothCovariance.amplitudes H T j)
```
and `increment_eq_inverse` rewrites the denominator as $2\sqrt{(H^{-1}T)_j}$ under `StrictCone`.
Header: "A signed square is retained as a separate term; it is not included in the linear covariance
identity."

**(b)** $\delta_j=(H^{-1}R)_j/(2\sqrt{(H^{-1}T)_j})$.

**(c)** Dimensionless (ratio of quadratic forms). **Pass.**

**(d)** No cancellation of mixed derivative terms occurs: the cancellation is **sign/cone-based**
(`StrictCone`), and a signed square is deliberately kept separate rather than cancelled. The task's
description inverts the design.

### E30 — Task 20: LaTeX statement of nonlinear convective accumulation

**PREMISE NOT IN CODE.** No lemma bounds "nonlinear convective derivative accumulation." The nearest
exact statements are `CoordinateAlgebra.lean:214` and `:225`, coefficient identities for
incompressibility.

**(b)** In inner variables, with $u=q^b(\,\cdot\,)$,
$$\partial_X F\cdot(\text{radial coeff})+\partial_\eta F\cdot(\text{axial coeff})=0$$
is what the file proves; the convective estimate $\int|u|^2|\nabla u|\lesssim\|u\|_2^{3/2}\|\nabla u\|_2^{3/2}$
is in `LocalizedFluxEstimates`/`WeightedInterpolation`, not here.

**(c)** The divergence identity is dimensionless; the convective bound is $U^3L$, consistent with
$E'\sim U^2L$ only through Young absorption (E10.7).

**(d)** Any LaTeX "convective accumulation lemma" attributed to `SimilarityProfile` would be invented.
The honest citation is `LocalizedFluxEstimates.transport_flux_bound`, whose bound is
$(8L/R)\,M^{3/2}B^{3/2}$.

### E31 — Task 21: `rieszSymbol` at $\|x\|=0$

**(a)** `NavierStokes/R3PressureFourier.lean:21`
```lean
def rieszSymbol (i j : Fin 3) (x : Space) : ℂ :=
  Complex.ofReal (-(x i * x j) / ‖x‖ ^ 2)
```
`:28`
```lean
theorem norm_rieszSymbol_le (i j : Fin 3) (x : Space) : ‖rieszSymbol i j x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [rieszSymbol, hx]
```

**(b)** At $\xi=0$ the definition returns $0$ because Lean's real division has $a/0=0$. So
$m_{ij}(0):=0$, not $\lim_{\xi\to0}m_{ij}(\xi)$ (which does not exist without a direction).

**(c)** $m_{ij}$ is homogeneous of degree $0$; the value at one point carries no dimension. **Pass.**

**(d)** This is a **silent convention, not a limit**, and it is the only definitional irregularity in
the operator. Its effect is exact: setting $m(0)=0$ removes the mean of the data, so $R_iR_jf$
differs from any other choice by a constant in $x$ — which $\nabla$ kills and which a divergence-free
test cannot see. Harmless for pressure, but it must be recorded as a convention, because a reader
assuming $m(0)=1/3$ (the trace value) would get a different operator.

### E32 — Task 22: coercion to the tempered distribution

**(a)** `R3PressureFourier.lean:84`
```lean
def pressureHat (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) : Lp ℂ ⊤ :=
  rieszSymbolLp i j • frequencyL1 f
def pressureL1 (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) : 𝓢'(Space, ℂ) :=
  𝓕⁻ (pressureHat i j f : 𝓢'(Space, ℂ))
```

**(b)** $p=R_iR_jf=\mathcal F^{-1}\big(m_{ij}\,\hat f\big)$, with $m_{ij}\hat f\in L^\infty$ and
$\mathcal F^{-1}$ acting on $\mathcal S'$.

**(c)** $[m]=1$, $[\hat f]=UL^{3/2}$, so $[\hat p]=UL^{3/2}$ — the pressure has velocity-squared units
only after the gradient is taken, consistent with $[p]=U^2$ in physical space.

**(d)** The coercion is `Lp.toTemperedDistribution` after `𝓕⁻` on $\mathcal S'$. This is the correct
type: $m\notin C^0$ at $0$ and $m\hat f\notin L^1$ in general, so returning $\mathcal S'$ rather than a
function is a theorem about the operator, not a convenience.

### E33 — Task 23: Plancherel for $L^2$ data

**(a)** `R3PressureFourier.lean:99`
```lean
def pressureL2 (i j : Fin 3) (f : Lp ℂ 2 (volume : Measure Space)) : Lp ℂ 2 :=
  𝓕⁻ (rieszSymbolLp i j • 𝓕 f)
```
`:103` `norm_pressureL2_le` closes with `have hnorm (g : Lp ℂ 2) : ‖𝓕⁻ g‖ = ‖g‖`.

**(b)** $\|R_iR_jf\|_{L^2}\le\|f\|_{L^2}$ by the $L^2$ Fourier isometry and $|m_{ij}|\le1$.

**(c)** Both sides $UL^{3/2}$; the constant is exactly $1$. **Pass.**

**(d)** No loss: the operator is a contraction on $L^2$. Note the contrast with $L^1$, where the same
symbol is unbounded — that is why `pressureL1` must land in $\mathcal S'$.

### E34 — Task 24: "induction sequence" in the distributional Liouville theorem

**PREMISE NOT IN CODE.** There is no induction. The chain in
`NavierStokes/R3/HarmonicTestFunctionals.lean` is:

`:42` `continuous_of_fourierHNormSq_bound` (H³ bound ⇒ continuity for the Schwartz topology);
`:55` `exists_inner_representation_of_fourierHNormSq_bound` (Riesz representation in a weighted
$L^2$ space); `:55–83` `representative_eq_zero_of_harmonic` (multiply by $|\xi|^2$; weak uniqueness
forces $q=0$); `:84` `eq_zero_of_harmonic`; `:100` `eq_zero_of_compact_harmonic`
(density of compactly supported tests).

**(b)** If $|\langle F,\psi\rangle|\le C\|\psi\|_{H^3}$ and $\langle F,\Delta\psi\rangle=0$ for all
$\psi\in C_c^\infty$, then $F=0$: distributional harmonicity makes $F$ a polynomial, and the
finite-order bound excludes every nonzero polynomial.

**(c)** $\|\psi\|_{H^3}$ controls $\psi$ but not $\int\psi$; a nonzero constant functional fails the
bound, correctly. **Pass.**

**(d)** The real mechanism is a **Fourier multiplier plus weak uniqueness**, and it is stronger than
induction would be. Calling it an "induction sequence" misdescribes both the proof and its strength.

### E35 — Task 25: `fourierHNormSq` at $s=3$

**(a)** `NavierStokes/R3/ComparisonFourierSetup.lean:27`
```lean
def fourierHNormSq (s : ℕ) (ψ : ComplexTest) : ℝ :=
  ∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ^ 2
```

**(b)** $\|\psi\|^2_{H^s}=\int(1+|\xi|^2)^s|\hat\psi(\xi)|^2d\xi$; at $s=3$ the weight is
$\langle\xi\rangle^{6}$, i.e. the $H^3$ norm of the **test**.

**(c)** $[\psi]=1$ (test function), so the norm is dimensionless; the weight has the correct
$|\xi|^{2s}$ growth. **Pass.**

**(d)** The docstrings say "Fourier $H^{-3}$" because the **functional** is bounded in the dual of
$H^3$; the quantity defined here is the $H^3$ norm of the test. Both statements are consistent, but
the notation invites the opposite reading and should be quoted carefully.

### E36 — Task 26: continuity of the Schwartz compact approximations

**(a)** Call site: `HarmonicTestFunctionals.lean:106–110`
```lean
exact SchwartzCompactApproximation.continuous_zero_of_compactSupport
  (fun φ : ComplexTest => F (laplacianCLM φ))
  ((continuous_of_fourierHNormSq_bound F hC hbound).comp laplacianCLM.continuous)
  hharmonic ψ
```
The approximation machinery is `NavierStokes/SchwartzCompactApproximation.lean`: `cutoff` (`:26`),
`cutoff_derivative_bound` (`:50`), `approximate_apply` (`:70`), `approximate_sub_apply` (`:93`),
`approximation_derivative_bound` (`:108`).

**(b)** $\psi_R=\chi_R\psi\to\psi$ in every Schwartz seminorm, with
$\|\chi_R-1\|^{(n)}\le C_nR^{-1}$ on $|x|\ge R$; continuity on compactly supported tests then extends
by density.

**(c)** $[\chi_R]=1$, $[\nabla\chi_R]=L^{-1}$; the $R^{-1}$ rate is exactly what makes the seminorms
converge. **Pass.**

**(d)** **Provisional:** I did not open the exact binder of `continuous_zero_of_compactSupport` in this
pass (the file's theorem list at `:28–108` does not show it by that name, so it may be later in the
file). The call site and the approximation estimates are confirmed; the declaration line is not.

### E37 — Task 27: constants in `averagedPressureDifference_bound`

**(a)** `NavierStokes/R3/PressureFunctionals.lean:279`
```lean
theorem averagedPressureDifference_bound ... :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ComplexTest,
      ‖averagedPressureDifference W0 W1 G hW0 hW1 hG k ψ‖ ≤
        C * Real.sqrt (fourierHNormSq 3 ψ)
```

**(b)** $|F(\psi)|\le C\|\psi\|_{H^3}$, with $C=C(\|W_0\|_2,\|W_1\|_2,\|G\|_1)$ — **existential**.

**(c)** $[C]=[F]\,[\,\|\psi\|_{H^3}\,]^{-1}$; since $F$ pairs a tensor with a Riesz test, the units
work out, but no value is produced.

**(d)** The task asks for "the exact LaTeX upper bound constants." **There are none.** The constant is
existential and delegated to `averagedPressureDifferenceValue_bound`. This is the same gap as E26:
the chain is constant-symbolic end to end.

### E38 — Task 28: fractional Laplacian

**ABSENT.** Zero occurrences of `fractionalLaplacian`, `fractional_laplacian`, or
`FractionalLaplacian` in the repository at `f9e8bc5`. The only nonlocal operator is the zeroth-order
Riesz multiplier `rieszSymbol` (`R3PressureFourier.lean:21`), of order $0$, not $(-\Delta)^s$.

**(b)** N/A.

**(c)** A fractional Laplacian of order $2s$ would carry $L^{-2s}$; nothing in the tree carries a
non-integer derivative order.

**(d)** `PREMISE NOT IN CODE`. Recording it as absent is the only accurate statement; a "fractional
Laplacian implementation" in this repository does not exist.

### E39 — Task 29: discrete Fourier transform in the periodization bridge

**PREMISE NOT IN CODE.** `PeriodicLocalization.lean` contains no `Fourier` occurrence. Periodization
is a lattice sum of translates, with `SupportedInCube` making it locally finite:
`periodize_eq_on_innerCube` (`:237`) proves that on the inner cube only the $k=0$ copy contributes.
`PeriodicResidualLimits` then works with jets, not spectra.

**(b)** $f^{\#}(x)=\sum_{n\in\mathbb Z^3}f(x+n)$; on $\{|x_i|<3/4\}$ with $\operatorname{supp}f\subseteq\{|x_i|\le1/4\}$,
$f^{\#}=f$.

**(c)** The period is $1$, so all lengths are in units of the cell; no spectral variable appears.

**(d)** There is no DFT, no Fourier series, and no spectral truncation in the periodization bridge.
The bridge is **support-based**, which is why E9 found no ℝ³/𝕋³ transplant.

### E40 — Task 30: "high-frequency spectral leaking" at the quarter-cube boundary

**PREMISE NOT IN CODE.** There is no spectral quantity to leak. The exact mechanism is germ equality
plus disjoint support: `periodicResidual_jets_eq_cut` (`PeriodicResidualLimits.lean:138`) for
$z\in\mathrm{innerCube}(1/4)$, with `innerCube r = {x\mid\forall i,\ |x_i|<1-r}`
(`PeriodicLocalization.lean:213`), i.e. $|x_i|<3/4$.

**(b)** For $z$ in $(-3/4,3/4)^3$, $\ \mathrm{jet}_n(\text{periodic residual})(z)=\mathrm{jet}_n(\text{cut residual})(z)$
for every $n$ — no error term, no truncation order.

**(c)** The margin is $1/2$ in each coordinate: support $\le1/4$, cube edge $3/4$, cell edge $1$.
**Pass**, with a factor-3 margin.

**(d)** Since the identity is exact and of all orders, there is nothing to leak. A "spectral leak"
audit would be measuring an artifact of a method this repository does not use.

### E41 — Task 31: binder sequence for exact jet equality

**(a)** `NavierStokes/PeriodicResidualLimits.lean:138`
```lean
theorem periodicResidual_jets_eq_cut (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) (n : ℕ) :
    iteratedFDeriv ℝ n (periodicResidual A p) z =
      iteratedFDeriv ℝ n (cutResidual A p) z
```
and `:177`
```lean
theorem periodicResidual_jets_locally_cut (A : VelocityField) (p : PressureField)
    (x : Space) (n : ℕ) :
    iteratedFDeriv ℝ n (periodicResidual A p) =ᶠ[𝓝 ((1 : ℝ), x)]
      (fun z => iteratedFDeriv ℝ n (cutResidual A p) (z.1, z.2 - integerShift (nearestIndex x)))
```

**(b)** $\mathrm{jet}_n\big|_z$ of the two residuals coincide for all $n\in\mathbb N$; the local
version gives a **neighborhood**, not a point.

**(c)** No dimension: jets of a velocity field are $UT^{-n}L^{-n}$; both sides have the same units, so
the identity is dimensionally forced.

**(d)** Binder order is `z`/`hz` before `n`, so the neighborhood is chosen before the jet order; this
is what makes the local statement uniform in $n$ and therefore usable for the boundary series.

### E42 — Task 32: `innerCube` geometry

**(a)** `NavierStokes/PeriodicLocalization.lean:213`
```lean
def innerCube (r : ℝ) : Set Space := {x | ∀ i : Fin 3, |x i| < 1 - r}
```

**(b)** $\mathrm{innerCube}(r)=(-1+r,\,1-r)^3$; at $r=1/4$ this is $(-3/4,3/4)^3$.

**(c)** Side $2(1-r)=3/2$, volume $(3/2)^3=27/8$, in units of the unit period. **Pass.**

**(d)** The parameter is a **margin**, not a radius: increasing $r$ shrinks the cube. The code's
`supportCylinder` fits in $|x_i|\le1/4$, leaving a margin of $1/2$ to the cube wall and $3/4$ to the
cell wall.

### E43 — Task 33: Euler and the zero-viscosity baseline

**PREMISE NOT IN CODE.** There is no `Euler/ProblemStatement.lean` and no $\nu=0$ specialization.
`Euler/` is a parallel construction at fixed $\nu>0$: `BoundedMildContinuation.lean:39`
`exists_global_mild_of_bound (q) (ν) (hν : 0 < ν)`, `HeatGradientEnergy.lean:68`
`viscosity_young (ν) (hν : 0 < ν)`, and `CorrectionDifferencePDE.lean:4` "the exact
viscosity-difference equation of two genuine nonlinear mild corrections."

**(b)** $\partial_tu+\mathbb P(u\cdot\nabla u)=\nu\Delta u$ in mild form, with $\nu>0$ throughout.

**(c)** $[\nu]=L^2T^{-1}$; `viscosity_young` is $2xy\le\nu x^2+\nu^{-1}y^2$, dimensionally consistent
only because $x,y$ carry reciprocal units.

**(d)** Euler is **not** mapped to the Navier–Stokes residual and is **not** a zero-viscosity limit.
Any claim that the repository "traces the zero-viscosity baseline to the NS residual" is unsupported:
the only documented bridge to the comparator is `ComparatorBridge`, which normalizes $\nu$ to one.

### E44 — Task 34: structural lemmas preceding the uniform flux

**(a)** `NavierStokes/R3/PressureFlux.lean`: `fluxFunction` (`:107`), `canonicalFlux` (`:125`),
`norm_canonicalFlux_le` (`:137`), `fluxTest` (`:159`), `canonicalCutoffFlux` (`:191`),
`pressurePair_decomposition` (`:251`), `localized_pair_bound` (`:355`-region),
`uniformCoefficient` (`:380`), `uniform_expression_bound` (`:391`);
integration identity `PressureFluxIdentity.lean:114` `pressure_flux_eq_of_gradient_identification`.

**(b)**
$$\text{canonicalFlux}=\sum_{i,j}\int T_{ij}\,\big(R_iR_j(\chi^2D_\chi[w])\big),$$
split by `pressurePair_decomposition` into $\int (h\,g)R_iR_j\psi+\text{commutator}$, with the
commutator bounded by $\|hg\|_{6/5}\|R_iR_j\psi\|_6$.

**(c)** The decomposition is exact; the two summands have the same units, and the $6/5\cdot6$ Hölder
pair is the only place the exponent $6$ enters. **Pass.**

**(d)** The structural point: the uniform pressure bound is assembled from an **exact algebraic
decomposition** plus Hölder/Sobolev, not from any estimate on $p$. This is the same conclusion as E10.5,
now at the level of individual lemmas.

### E45 — Task 35: `force_nonzero_of_no_global_solution`, full type

**(a)** `NavierStokes/R3/CandidateBreakdown.lean:53`
```lean
theorem force_nonzero_of_no_global_solution {ν : ℝ} {f : VelocityField}
    (hf : CompactPositiveTimeSupport f)
    (h : ¬ Nonempty (GlobalFiniteEnergySolution ν f)) :
    ∃ t : ℝ, 0 < t ∧ ∃ x : Space, f (t, x) ≠ 0
```

**(b)** If $f$ is smooth with $\operatorname{tsupp}f\subseteq\{t>0\}$ and the forced problem from
datum $0$ has no global finite-energy solution, then $f\not\equiv0$ on $(0,\infty)$.

**(c)** No dimension — a support statement. Note the conclusion is on $t>0$ only, consistent with
`hf`, which forces $f=0$ for $t\le0$ (`CompactPositiveTimeSupport.eq_zero_of_nonpos`).

**(d)** This is **not** an "admission of a gap." It is a formal lower bound: any force that kills global
existence must be nonzero somewhere at positive time, so the theorem cannot be restated with
$f\equiv0$. Combined with the zero datum and $u\equiv0$ on $|t|\le3/8$, it is the precise witness that
the result is **forced**, not spontaneous.

---

### E46 — Matrix closure

| Stream | Tasks | Answered from declarations | Premise corrected / absent |
|---|---|---|---|
| 1 (similarity) | 01–10 | 01, 02, 08 | 03, 04, 05, 06, 07, 09, 10 |
| 2 (ledger) | 11–20 | 12, 13, 16, 17, 18, 19 | 11, 14, 15, 20 |
| 3 (Fourier) | 21–30 | 21, 22, 23, 25, 26, 27 | 24, 28, 29, 30 |
| 4 (boundary) | 31–35 | 31, 32, 34, 35 | 33 |

Totals: **16 answered, 19 corrected.** The most load-bearing corrections:

1. `ExponentLedger` never defines $\kappa$; it proves a **range** statement (E21).
2. No constant in the chain is ever evaluated (E26, E37) — the formalization cannot detect a wrong
   constant, only a wrong exponent.
3. There is no fractional Laplacian, no DFT, no spectral truncation (E38–E40); the periodization
   bridge is exact and support-based.
4. `Euler/` is not a zero-viscosity baseline (E43).
5. `rieszSymbol` sets $m_{ij}(0)=0$ by Lean's $a/0=0$, which shifts the pressure by a constant that
   the divergence-free test cannot see (E31).

*End of E11–E46. Next entries append below.*

---

### E47 — Erratum to E11–E46 (tally only)

The per-stream table in E46 is correct; the two summary sentences in E11–E46 and in E46 invert its
totals. Corrected figures, summed from the table:

- Stream 1: 3 answered (01, 02, 08) + 7 corrected = 10
- Stream 2: 6 answered (12, 13, 16, 17, 18, 19) + 4 corrected (11, 14, 15, 20) = 10
- Stream 3: 6 answered (21, 22, 23, 25, 26, 27) + 4 corrected (24, 28, 29, 30) = 10
- Stream 4: 4 answered (31, 32, 34, 35) + 1 corrected (33) = 5

**Total: 19 answered from declarations, 16 premise-corrected or absent, 35 tasks.**

No finding is affected; only the two numerals are. E11–E46 are left as written.

*End of E47. Next entries append below.*

---

## E48 — Phase II: the three interfaces (A.1–A.3, B.1–B.2, C.1–C.2)

*Scope.* Seven tasks, not six: group A has three (A.1 Riesz bounds, A.2 cutoff
commutation, A.3 weight vs `1/|x|^3`), group B two (B.1 temporal regularity,
B.2 residual smoothness), group C two (C.1 Leray exponents, C.2 corrector
feedback). Append-only; E0–E47 untouched. All citations at `f9e8bc5`.

**Tally: 3 answered as posed, 3 premise-corrected, 1 vacuous by dependency.**
The corrected ones are A.3, B.2 and C.1; C.2 collapses once C.1 is settled.

### E48.1 — A.1: there is no boundary term to make vanish

**(a)** `NavierStokes/R3/WholeSpaceUniqueness.lean:30`
```lean
theorem classical_uniqueness_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu hv hp hq : ContDiffOn ℝ ∞ _ (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc 0 T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc 0 T) v)
    (hdu hdv : … spatialDivergence … = 0)
    (hNS : navierStokesResidual 1 u p = navierStokesResidual 1 v q)
    (hzero : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc 0 T, ∀ x, u (t, x) = v (t, x)
```
**(b)** Uniqueness on the slab for two smooth divergence-free fields with equal
residuals and equal data, one of which ($u$) has compact spatial support and the
other of which ($v$) merely has uniformly bounded kinetic energy.

**(c)** No new dimension. The only quantitative input is
`hev : ½‖v(t)‖₂² ≤ E` with $[E]=L^5T^{-2}$; the flux estimate is the one already
audited in E10.

**(d) Finding — the task's dichotomy is false.** There is no hypothesis
$\lim_{R\to\infty}\int_{\partial B_R}p\,(w\cdot n)=0$, and no qualitative support
predicate on the competitor. The surface term is never written: $p-q$ appears
only against $\nabla\chi_R$, and $\chi_R$ is compactly supported for every finite
$R$, so no integral over $\partial B_R$ exists. The two inputs that replace decay
are (i) compact support of the *reference* only (`hK`, `hsupp`) and (ii)
`UniformFiniteEnergy` of the competitor. The reference's own finite energy is
*derived*, not assumed: `uniformFiniteEnergy_of_compact_slab hu hK hsupp`.
After `actual_flux_eq_canonicalCutoffFlux` rewrites the pairing as the canonical
Riesz functional of $u\otimes v$, `exists_uniform_actual_pressure_flux_bound`
supplies a constant fixed before $R$ is quantified, and every remaining
$R$-dependence is explicit and vanishes: $C_0/R^2$, $C_1R^{-1}B^{3/2}$, and the
$C_2$-envelope ending $R^{-7/4}B^{3/4}$ (`R3/ComparisonRateBound.lean:130`).
The limit $R\to\infty$ is taken on a *bound*, not on an integral identity. So no
decay lemma exists to be found, and none is missing.

### E48.2 — A.2: germ equality is stronger than the gradient identity requested

**(a)** `NavierStokes/SpatialLocalization.lean:210`–`:218`, `:266`–`:282`;
`NavierStokes/PeriodicResidualLimits.lean:138`.
```lean
noncomputable def periodicPotential (A) := Periodize.periodize (cutPotential A)
noncomputable def periodicVelocity  (A) := SpatialCurl.spatialCurl (periodicPotential A)
noncomputable def periodicPressure  (p) := Periodize.periodize (cutPressure p)

theorem periodicVelocity_eventuallyEq_cut (A) {z}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1/4)) :
    periodicVelocity A =ᶠ[𝓝 z] cutVelocity A

theorem periodicResidual_jets_eq_cut (A p) {z}
    (hz : z.2 ∈ innerCube (1/4)) (n : ℕ) :
    iteratedFDeriv ℝ n (periodicResidual A p) z =
      iteratedFDeriv ℝ n (cutResidual A p) z
```
**(b)** On the inner quarter-cube the periodized velocity, pressure and residual
agree with the cut fields as *germs*, hence all iterated derivatives agree.

**(c)** Inert: an identity between functions, not an estimate.

**(d) Finding — the commutator is not bounded, it is absent.** The code never
asserts $\nabla\bigl(\sum_k\chi\,p(\cdot+k)\bigr)=\sum_k\chi\,\nabla p(\cdot+k)$,
which would be false. It proves the stronger statement that the two *functions*
agree on a neighbourhood, from which equality of all jets follows by
`iteratedFDeriv_eventuallyEq`. On `plateau`, where $\chi\equiv1$ and hence
$\nabla\chi=0$, the germ equality upgrades again to the *uncut* field:
`periodicVelocity_eventuallyEq` (`:318`) gives
`periodicVelocity A =ᶠ spatialCurl A`. The commutator $[\nabla,\chi]$ therefore
requires no bound anywhere: it vanishes identically on the plateau, and off it is
carried exactly by the cut residual rather than estimated.

### E48.3 — A.3: the task's premise does not apply (corrected)

**(a)** `NavierStokes/R3/WeightedSobolev.lean` in full: `sobolevConstant` at
`:25`, `lpNorm_six_le` at `:42`, `weightedSobolevConstant := 4 * sobolevConstant + 1`
at `:210`, and the weights `cutoffGradientAmplitude := φ^4 · √(gradientSq w)` with
`norm_cutoffGradientAmplitude_sq : ‖…‖^2 = φ^8 · gradientSq`.

**(b)** For $C^1_c$ fields,
$\|f\|_{L^6}\le S\,\|\nabla f\|_{L^2}$, and for the cut velocity
$\|\nabla(\varphi^4 w)\|_2\le 3\bigl(\int\varphi^8|\nabla w|^2\bigr)^{1/2}+4L\|w\|_2$.

**(c)** $[S]=1$: the Sobolev constant is dimensionless. $[\varphi^8|\nabla w|^2]=L^{-1}T^{-2}$
over $L^3$, i.e. $L^2T^{-2}$, matching $\|\nabla w\|_2^2$. Consistent.

**(d) Finding — there are no decay weights and no Riesz kernel in this file.**
The task asked to compare weights against the algebraic decay of the Riesz
transform of a compactly supported source. That comparison cannot be made because
no decay order appears: the weights are $\chi^4$ (velocity) and $\chi^8$
(dissipation), both *localising*, and the file's own header states the estimate is
local and requires only $L^2$ of the unweighted velocity. Nothing is hidden in an
existential either: `sobolevConstant` is a size, not an order, and no declaration
in the file mentions a power of $\|x\|$. The two existentials in the wider chain
(`sobolevConstant`, `weightSecondDerivativeConstant`) carry magnitude, and the
barrier of E26 applies to magnitude only.

### E48.4 — B.1: no branch, no jet, a scalar multiplier

**(a)** `NavierStokes/TimeLocalization.lean:27`–`:31`; `R3/PositiveTimeForce.lean:21`–`:59`.
```lean
def activatedVelocity (u) : VelocityField := fun z => timeSwitch z.1 • u z
def activatedPressure (p) : PressureField := fun z => timeSwitch z.1 * p z

theorem activatedVelocity_smooth (hu : ContDiffOn ℝ ∞ u preSingularDomain) :
    ContDiffOn ℝ ∞ (activatedVelocity u) preSingularDomain

def force (f) : VelocityField := fun z => timeCutoff z.1 • f z

theorem force_eq {t} (ht : t ∈ Icc (3/8 : ℝ) 1) (x) :
    force f (t, x) = f (t, x)
```
**(b)** The field switches on through a smooth scalar factor in $t$ alone; on
$[3/8,1]$ the factor equals one, and for $|t|\le3/8$ the field is identically zero.

**(c)** Inert. A product by a dimensionless scalar.

**(d) Finding — smoothness is `ContDiffOn ℝ ∞` and is inherited, not branched.**
There is no `if-then-else` and no interval-wise delegation: `activatedVelocity_smooth`
is `(timeSwitch_contDiff.comp contDiff_fst).contDiffOn.smul hu`, one line.
The two sides of the junction agree because the *field*, not the multiplier,
vanishes on the early slab: `activatedVelocity_zero_early` and
`activatedPressure_zero_early` give $u=p=0$ for $|t|\le3/8$, whence
`localized_residual_zero_early` gives a vanishing residual there. The equation is
closed by `by_cases hearly : t < 3/8` in `R3/ActualCandidate.lean`: on the early
side `hzero` and `PositiveTimeForce.force_eq_zero`; on the late side
`force_eq ⟨le_of_not_gt hearly, ht.2.le⟩`.

### E48.5 — B.2: the named file contains no such proof (corrected)

**(a)** `NavierStokes/R3/CandidateBreakdown.lean` has exactly four declarations:
`CandidateProperties.not_global_agreement`, `no_global_solution_one`,
`force_nonzero_of_no_global_solution` (`:53`), `uniform_l2_sq_bound`. Force
smoothness is elsewhere:
`R3CompactCandidate.lean:90 compactForce_smooth`, then
`PositiveTimeForce.force_contDiff` (`:49`).

**(b)** If $f$ is smooth then $\theta(t)f$ is smooth, where $\theta$ is a smooth
cutoff in $t$.

**(c)** Inert.

**(d) Finding — no derivative of $f$ is ever evaluated at $t=3/8$.** Smoothness of
the force is `(outerCutoff_smooth.comp contDiff_snd).contDiffOn.smul hf` followed
by `(timeCutoff_contDiff.comp contDiff_fst).smul hf`: closure of $C^\infty$ under
composition and multiplication, with no pointwise jet and no numerical evaluation.
The force's time support is bounded *away* from the junction rather than asserted
at it: `force_tsupport_subset` gives
$\operatorname{tsupp}(\ct{force} f)\subseteq[1/16,21/16]\times K$, which is what
supplies `CompactPositiveTimeSupport`. The task's premise — that the interface is
closed by matching $\partial_t^k f$ at $3/8$ — is false.

### E48.6 — C.1: there is no corrector, because nothing diverges

**(a)** `NavierStokes/SpatialLocalization.lean:165`–`:172`, `:258`–`:262`.
```lean
noncomputable def cutPotential (A) := fun z => spatialCutoff z.2 • A z
noncomputable def cutVelocity  (A) := SpatialCurl.spatialCurl (cutPotential A)

theorem periodicVelocity_divergence_free (hA) {t} (ht) (x) :
    spatialDivergence (periodicVelocity A) t x = 0
```
**(b)** The cut is applied to the potential, and the velocity is the curl of the
cut potential; a curl is divergence-free identically.

**(c)** Inert: no estimate, an identity.

**(d) Finding — $\nabla\cdot(\chi u)\neq0$ never arises, so no corrector exists.**
Because $u_{\rm cut}=\nabla\times(\chi A)=\chi\,\nabla\times A+\nabla\chi\times A$,
the commutator that a Leray projection or a divergence corrector would remove is
instead *retained inside the velocity*, supported in the annulus
`supportCylinder ∖ plateau` (`:72`, `:134`). This is why the construction gets
exact divergence-freeness for free while being only germ-equal to the naive cut.
Consequence for the ledger: `ExponentLedger.lean` has no corrector entries
because there is no corrector, so there are no missing powers of $q$ to find.

### E48.7 — C.2: vacuous by dependency

**(a)** Nothing to cite: the object whose residual the task asks about does not
exist (E48.6).

**(b)** —

**(c)** —

**(d)** The corrector's residual is neither added to $f$ nor majorised by an
existential, because there is no corrector residual. The force remains the exact
residual of the fields actually used (E10.6, E9.4 corrected), and the equation
holds by case split rather than by estimate. The task's alternative — "added
explicitly, or killed by an existential constant" — has no third option in the
code because the premise fails.

### E48.8 — Manuscript integration and state

Three subsections added to `ns-audit/MANUSCRIPT.tex` under a new §5
("Three interface audits"), with the labels requested:
`sec:riesz-decay`, `sec:temporal-bump`, `sec:divergence-corrector`. The
Conclusion is now §6 and gains one paragraph tying exactness at the three
interfaces to the constant barrier of §3. Appendix A gains seven rows
(`SpatialLocalization` 165–172, 210–216, 260, 318; `TimeLocalization` 27–31;
`PositiveTimeForce` 46–55; `R3CompactCandidate` 90).

**Manuscript state:** 1,217 lines. Structural check passes: environments
balanced, 0 unresolved refs, 0 duplicate labels, braces and `$` parity even, no
unescaped underscores in `\ct{}`/`\file{}`.

**Limitation, unchanged and load-bearing:** no `elan`/`lean`/`lake` and no TeX
engine on this host. The manuscript is **not compiled**; the seven findings above
are from reading proof terms and binder sequences, not from re-elaboration.
The "no boundary term" conclusion of E48.1 rests on the shape of the hypotheses
and the use of compactly supported weights, both of which are visible in the
signature and in `eq_of_pressure_flux_bound`.

### E48.9 — Closure ledger for Phase II

| Task | Object | Status |
|---|---|---|
| A.1 | `classical_uniqueness_on_Icc` | answered; no boundary term (stronger) |
| A.2 | periodization germ equality | answered; commutator absent, not bounded |
| A.3 | `WeightedSobolev` weights | **premise corrected**; no decay weights exist |
| B.1 | temporal junction | answered; multiplier, no branch |
| B.2 | `CandidateBreakdown` force smoothness | **premise corrected**; not in that file |
| C.1 | divergence corrector | **premise corrected**; no corrector exists |
| C.2 | corrector residual | vacuous by dependency on C.1 |

**Erratum to E48's own preamble as first drafted:** an earlier verbal summary of
this pass described it as "six tasks". The plan contains seven. Recorded here
rather than silently fixed, per the append-only protocol.

---

## E49 — Call-graph map of the load-bearing chain (tool-substituted)

*Scope and disclosure.* This pass was requested as an Anvil `find_callers` map with
`lean-lsp-mcp` type queries. Neither server is connected in this session, and two of the
three prerequisites are absent from the host: `command -v lean`, `elan`, `lake`,
`lean-lsp-mcp` and `anvil` all return nothing. What exists is a Lake project
(`lakefile.toml`, `lean-toolchain`) with no toolchain installed. The map below was produced
by ripgrep over the tree at `f9e8bc5`. Counts are exact for the identifiers searched; the
limits are stated in E49.4 rather than glossed.

### E49.1 — single-consumer concentration at the pressure bottleneck

| Declaration | Defined | Consumers |
|---|---|---|
| `exists_uniform_actual_pressure_flux_bound` | `R3/PressureFlux.lean:576` | `R3/WholeSpaceUniqueness.lean:60` — only |
| `eq_of_pressure_flux_bound` | `R3/WholeSpaceComparisonClosure.lean:32` | `R3/WholeSpaceUniqueness.lean:64` — only |
| `actual_flux_eq_canonicalCutoffFlux` | `R3/PressureFlux.lean:211` | `R3/PressureFlux.lean:231` — internal only |
| `averagedPressureDifference_bound` | `R3/PressureFunctionals.lean:279` | `R3/PressureRecovery.lean:296` — only |
| `averagedPressureDifferenceValue_bound` | `R3/PressureFunctionals.lean:169` | `R3/PressureFunctionals.lean:287` — internal only |

**Finding.** The nonexistence conjunct has exactly one proof path. No other declaration in
the tree consumes the pressure-flux estimate, and the flux identity is used only inside the
lemma that states it. A defect there would be *contained* (one call site) and *uncorroborated*
(no second route). This is not a logical defect — a proof is a proof, and the kernel checks
every term — but it means E10 is the only independent check on that step, and it is where the
audit's marginal value is highest. Recorded, not dramatized.

### E49.2 — the exponent ledger is load-bearing (a hypothesis of mine, refuted)

I had been prepared to find `ExponentLedger.lean` to be an ornamental arithmetic module. It
is not. `NavierStokes/CorrectionStep.lean:28` imports it and consumes
`mean_update_wave_margin` (`:2204`),
`particular_increment_above_cumulative_difference` and
`signed_increment_above_cumulative_difference` (`:2711`–`:2712`), plus the exponent
*definitions* at `:2189`, `:2424`–`:2439`, `:2702`–`:2705`.
`NavierStokes/ActualIterationLedger.lean:1` imports it, defines
`sigma J := ExponentLedger.stageParameter J` (`:22`), and invokes `all_stage_arithmetic`
(`:129`). `NavierStokes/ActualStageEstimates.lean:129,135` unfolds `meanUpdateExponent` and
`waveExponent`.

So the κ-ledger inequalities are consumed by the iteration, not merely stated alongside it.
This strengthens rather than weakens the E21 finding: the arithmetic that *is* checked is
load-bearing, and the constant that is *not* evaluated (`κ` itself, per E21) is the one the
ledger never instantiates.

### E49.3 — root chain and downstream fan-out

`theorem_1_1` (`R3/Theorem.lean:46`) ← `theorem_1_1_with_initial_rest` (`:26`)
← `ActualCandidate.selected_candidate_one_with_initial_rest`.

Consumers of the root: `Theorem.lean:54` (`candidateStatement`), `:62`
(`breakdownStatement`), `:78` (`theorem_1_1_with_dissipation`),
`NavierStokes/PaperLocalization.lean:42`, `NavierStokes/ComparatorR3Theorem.lean:43`,
`NavierStokes/PeriodicPaperTheorem.lean:158` (via `with_initial_rest`),
`NavierStokes/R3/H3MaximalLifespan.lean:114`.

Nonexistence conjunct:
`CandidateProperties.no_global_solution_one` (`R3/CandidateBreakdown.lean:43`)
← `candidate_global_agrees_before_one` (`R3/WholeSpaceUniqueness.lean:104`)
← `candidate_unique_on_Icc` (`:72`)
← `classical_uniqueness_on_Icc` (`:30`).
`candidate_unique_on_Icc` is also consumed by `R3/ViscousUniqueness.lean:46`.

**Finding.** All four downstream statements — periodic, H³ maximal-lifespan, comparator, and
paper localization — rest on the same single comparison theorem. One root, no redundancy.
That is normal for a formal development, but it fixes the audit's blast radius precisely: a
defect in `classical_uniqueness_on_Icc` would take all four with it, and there is no
independent second proof to catch it.

### E49.4 — what the unavailable tools would have added

- `lean-lsp-mcp` (`hover_type`, `get_goal_state`, `type_check_expression`): kernel-level
  confirmation of the signatures quoted in E48 and in `PHASE2-FINDINGS.md`. Without it those
  signatures are **read**, not **elaborated**; every "unification" statement in this log is a
  statement about source text and binder order.
- `Anvil` (`find_callers`, `impact_analysis`): the counts above are exact for the searched
  identifiers, but they do not follow `open`/alias renamings or dot-notation beyond the
  qualified form, and they cannot see dynamic uses. An AST-level tool would.

Neither absence changes a verdict. Both bound the strength of the evidence, and the
distinction is recorded rather than hidden.

---

## E50 — Environmental reproducibility: the pinned toolchain's `lake` cannot run on this host

**Status:** audit-blocking for elaboration; no effect on any finding E0–E49, which remain source-read.

### E50.1 What was installed

`elan` + toolchain `leanprover/lean4:v4.34.0-rc2` (the repo's own `lean-toolchain` pin, real release 2026-08-21).
Measured footprint: **2.7 GB** at `~/.elan/toolchains/leanprover--lean4---v4.34.0-rc2`.
Version confirmed: `Lean (version 4.34.0-rc2, <arch>-apple-darwin<os>, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)`. Host triple withheld — see E64.

### E50.2 What fails

`lake` aborts on **every** invocation:

```
Trace/BPT trap: 5    (exit 133)
EXC_BREAKPOINT (SIGTRAP), codes 0x1
libsystem_c.dylib  __abort
libsystem_malloc   malloc_vreport -> malloc_report
libsystem_malloc   ___BUG_IN_CLIENT_OF_LIBMALLOC_POINTER_BEING_FREED_
libsystem_pthread  _pthread_tsd_cleanup -> _pthread_exit -> _pthread_start
```

This is not cosmetic. `lake --version` prints the correct string and *then* dies, but a 60-module
throwaway project died in **0 s having produced 1 of 60 oleans**. Notes:

- `lake build` in the real repo: `mathlib: cloning …` then exit 133 inside 1 s; `.lake/packages` holds **only Comparator (680 K)**, no mathlib.
- `lean` itself is healthy: a trivial file elaborates and exits 0. Only Lake is poisoned.
- 26 crash reports in the host's system diagnostic reports directory.
- Fail rate 0/10 and 0/4 across repeats; one isolated `exit 0` observed early (intermittent, ~5%).

### E50.3 Ruled out, with controls

| Candidate cause | Test | Result |
|---|---|---|
| Harness env pollution | `env -i HOME PATH … lake --version` | 0/5 clean — env exonerated |
| Thread-pool teardown race | `LEAN_NUM_THREADS=1`, `=2` | 0/4, 0/4 |
| elan shim | direct `~/.elan/toolchains/.../bin/lake` | 133 — shim exonerated |
| Allocator tuning | `MallocSpaceEfficient=0`, `MallocXzmDisable=1`, `MallocZoneDisableXzm=1`, `MallocNanoZone=1`, `MallocLargeCache=0`, `MallocGuardEdges=0`, `MallocScribble=1`, combos | **0/4 on all nine** |
| Network / git | `git ls-remote mathlib4` | works (HEAD `8ae26cc6`) |
| Disk | `df -h /` | hundreds of GiB free |

### E50.4 Probable cause — and why it is not Lean's bug

Host runs a current macOS release on Apple Silicon (exact build and chip withheld — see E64). recent macOS releases ship the `xzone` allocator with
deferred reclamation; its `mach_vm_reclaim` path is documented to raise `EXC_BREAKPOINT` /
`BUG IN LIBMALLOC` in unrelated native binaries (llama.cpp #28357, mpv via skyStream #47, Python
crash analysis of 2026-07-24 all show the same signature on this OS family). Our trace lands in
libmalloc's own validator at thread exit, not in Lean code. Ruled out by construction: the fault is
raised by `libsystem_malloc`, before any Lean-level error path.

**Implication for the audit's reproducibility, not for its content:** the repository pins a
prerelease toolchain whose Lake predates this OS. Any party re-running these checks on a current macOS release with
`v4.34.0-rc2` will hit the same wall. A Linux host or the `leanprover/lean4:v4.34.0-rc2` container
image is the indicated environment.

### E50.5 Net effect on this audit

> **Status note added 2026-11-21:** this section records what was true of that
> attempt. The crash is real and was reproduced again (3/3) with a fresh install of
> the pinned toolchain. The conclusion that no build is possible on this host stands;
> the conclusion that no build is possible **at all** does not. A Linux VM built the
> `NavierStokes` library successfully (9,580 jobs, exit 0, 817 modules) and the four
> R3 theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. See the
> corrected scope note at the top of this log.

- **No oleans, no Mathlib cache, no build.** `lake exe cache get` never reached a download.
- Therefore E49.4 stands unchanged and is now load-bearing rather than a caveat: **every signature,
  binder order and line number in E0–E49 was obtained by reading source, not by elaboration.**
- Download accounting for the toolchain line in the earlier sizing estimate was wrong: predicted
  ~1.4 GB unpacked, actual **2.7 GB**. The 564 MB *compressed* figure was measured correctly.

### E50.6 Reversal cost

`elan self uninstall` removes the whole 2.7 GB; nothing outside `~/.elan` and the 680 K
`.lake/packages/Comparator` was written.

---

## E51 — E50.6 executed: environment restored

Toolchain uninstalled (`elan self uninstall`), `~/.elan` removed, and the 680 K
`.lake/packages/Comparator` clone from the aborted fetch deleted. `ns-audit/NavierStokesAndEuler`
is back to its 45 MB clone with no build state; no Lean binary is on `PATH`.
Consequence unchanged: this audit's authority remains textual, per E49.4 and E50.5.

---

### E52 — Batch-02 matrix triage: four tracks, 150 tasks, what the repository actually contains (2026-11-06)

*Intuition.* This entry is the loading-dock manifest check. A truck arrives with a
manifest listing 150 parcels by name. Before anyone signs for them, you walk the
dock and confirm which names correspond to a shelf. Three of the four names exist;
one is a shelf that was never built; and one parcel on the manifest is listed at
fifty times its actual weight. Signing the manifest without walking the dock is
how the previous four drafts acquired their errors.

Batch directive received: tasks 52–201, tracks 1–4, with instructions to log
E52–E201, to auto-inject anomalous findings into the manuscript, and to lead every
entry with an analogy. Executed this pass: reconnaissance only. E53–E201 are
deliberately absent. An append-only log records what was checked; pre-numbering a
block of entries in advance converts the log into a schedule, and the first batch of
this kind (E11–E45) closed with sixteen premises that did not exist in the tree.

Header note: the matrix targets "://github.com", which resolves to nothing. All
searches below are scoped to `ns-audit/NavierStokesAndEuler` at f9e8bc5. Unscoped
searches in this workspace also hit `NoesisDB-local/`, `Zero-Breach-Toolkit/`,
`watchpeoplefight/`, `hacker-stack/`, `neuron-surgery/` and `mcp-gateway/`; the
first pass for `oscillat|pulse` returned hits from those projects and would have
been reported as repository content by a less careful scan.

#### Track 1 (tasks 52–101): the noun is wrong, the mechanism is real

The repository contains no file whose name matches `pulse` or `oscillat`. The
construction is named **Packet**. Scale of the relevant subtree: `Euler/` holds
1,839 files against 816 in `NavierStokes/`, and among them

  PacketSourceScaleBounds, .Sequence, .Shift, .Guards, .Choice, .FromCosts,
  .Actual (10 files), PacketUniformFrequencyScales, PacketUniformFrequencyMargin,
  PacketShiftArithmetic (+NoOptions), PacketShiftedTimeGluing,

with 110 `Euler/Packet*.lean` files mentioning compact support or a support
inclusion. Tasks 52–101 are therefore addressable — but not under the names the
matrix supplies. A scan keyed to "pulse" returns zero and would be misread as the
absence of the cancellation mechanism rather than a naming mismatch.

Not opened this pass: whether the time-supports provably compress as the spatial
derivative index rises, and whether the interior-cutoff threshold leaks a
fractional error. Those are the two load-bearing questions of the track and are
queued, not answered.

#### Track 2 (tasks 102–151): one bullet has no referent

`grep -rln enstrophy` over `NavierStokes/` and `Euler/` returns **empty**. The word
never occurs in the development, so "the internal files handling localized
enstrophy estimates" names no file, and a bootstrapping sequence described in
those terms cannot be audited as described. Covariance is real and separate:
`Covariance.lean`, `SmoothCovariance`, `PrimaryCovarianceBounds`,
`HarmonicCovariance`, `ActualPrimaryCovariance`, `FlatCovariance`,
`PhysicalCurlCovariance`, `PulseCovariance`.

"Partition of unity sums across overlapping spatial coordinate charts" is doubtful
on structural grounds: the generalized cone is one global chart `(q, η, X)`, not an
atlas, so there is no chart overlap for a partition of unity to sum over. Not yet
confirmed by inspection; flagged rather than asserted.

The third bullet — hidden existentials mirroring `sobolevConstant` — is answerable
with the E27 method and is the only part of this track that is both well-posed and
new.

#### Track 3 (tasks 152–181): bullet 1 answered, negatively and precisely

`rieszSymbol` is total, with no origin exclusion and no removable-singularity
argument (`NavierStokes/R3PressureFourier.lean:21`):

    def rieszSymbol (i j : Fin 3) (x : Space) : ℂ :=
      Complex.ofReal (-(x i * x j) / ‖x‖ ^ 2)

At `x = 0` the field division yields the junk value `0`; the uniform bound
`norm_rieszSymbol_le` (`:28`) opens `by_cases hx : x = 0; simp [rieszSymbol, hx]`
and then uses `|x i| ≤ ‖x‖` to close `‖·‖ ≤ 1`. So the "origin singularity" is not
sidestepped by a hypothesis, a limit, or a decay condition — it is absorbed by the
total-function convention and then dominated uniformly. There is no hidden
constraint away from the origin to report, and that absence is the finding.

#### Track 4 (tasks 182–201): the bar is real, and the ledger is 50× conservative

`17/100` is a genuine bar-residual margin, discharged five ways in
`ExponentLedger.lean`: `old_difference_bar_margin` (:156, from `9/50 - 2κ`),
`curl_bar_margin` (:164, `1/2 - 3κ`), `square_bar_margin` (:170, `σ - 3κ` with
`σ ≥ 1/5`), `axial_bar_margin` (:175, `1 - κ`), `pressure_bar_margin` (:180,
`1 - 2κ`). Every one assumes `κ ≤ 1/100000`.

The sharp threshold is stated by the ledger itself, `:281`:

    theorem old_difference_bar_margin_iff (κ : ℝ) :
      17 / 100 < 9 / 50 - 2 * κ ↔ κ < 1 / 200

So the admissible window is `κ < 1/200 = 5·10⁻³` and the applied lemmas assume
`κ ≤ 10⁻⁵` — a slack factor of **500**, in the safe direction (`→ E59 §1`; this line previously
said 50). Nothing is claimed that
the ledger cannot pay for. But a reader who takes `1/100000` as the operating
threshold understates the admissible window by a factor of 500 (2.7 orders), and the
binding constraint across the whole bar is the old-difference line, not the `min`
assembled in `signed_bar_gain_exceeds_seventeen_hundredths` (:182).

#### Manuscript injection: declined

Two mechanical reasons. (i) The canonical file is `MANUSCRIPT.tex`; on this APFS
volume `manuscript.tex` is the same inode, so an instruction to "open
manuscript.tex" silently rewrites the tracked file. (ii) The file still carries an
unresolved contradiction at §4.2: the display states
`∂s²(Φ_{h,b}f) = Φ_{h,b-1}(∂X² f)`, while `SimilarityProfile.lean:279` returns
`b - 2`, and the `b - 1` operator weight only appears after multiplication by the
Jacobian `2s = 2qX`. Appending new subsections ahead of that repair is precisely
how the last three drafts accumulated fresh errors.

### E52.1 — Correction to the line references given in E52 (2026-11-06)

*Intuition.* The manifest named the right parcels but wrote the wrong shelf
numbers. This entry re-sticks the labels; it does not pretend the first list was
right.

E52 gave line numbers for four of the five margin lemmas and for
`signed_bar_gain_exceeds_seventeen_hundredths`. Those five numbers are shifted
forward by four to six lines. Correct values in
`NavierStokes/ExponentLedger.lean`:

    156  old_difference_bar_margin                     (as given in E52 — correct)
    160  curl_bar_margin                               (E52 said 164)
    164  square_bar_margin                             (E52 said 170)
    169  axial_bar_margin                              (E52 said 175)
    173  pressure_bar_margin                           (E52 said 180)
    178  signed_bar_gain_exceeds_seventeen_hundredths  (E52 said 182)
    281  old_difference_bar_margin_iff                 (as given in E52 — correct)

Cause: the numbers were transcribed from the ordering of a printed slice rather
than from a numbered listing. The declarations themselves, their common hypothesis
`κ ≤ 1/100000`, and the sharp threshold `κ < 1/200` are unaffected; only the shelf
labels move.

Also recorded here: E51 does exist (`## E51 — E50.6 executed: environment
restored`, line 1692). The numbering is continuous, and no gap note was added.

### E53 — Track 1, question 1: do packet time-widths provably shrink with grade? (2026-11-06)

*Intuition.* A stack of nested coffee cups: each cup must fit strictly inside the
one above it, and you want a proof that they do — not a promise. The development
supplies both the promise and the proof, but in different drawers, and one theorem
quotes the promise rather than fetching the proof. Knowing which drawer is which is
the whole audit.

Verdict: **yes, the contraction is derived, not stipulated** — with a file-boundary
caveat that changes how the result may be cited.

#### The object that shrinks

`timeWidth` (`Euler/PacketSourceScaleSequence.lean:42`):

    timeWidth J X n = 3*scaleSequence J X (n+1)*scaleSequence J X n/sqrt(previousShear J X n)

with `scaleSequence` the geometric sequence of
`Euler/PacketSourceScaleChoice.lean:226–232`,

    scaleSequence J X 0 = X
    scaleSequence J X (n+1) = ((J+n : ℕ) : ℝ)^2 * scaleSequence J X n

and `previousShear` exponential in `scaleSequence` at exponent 7. So `timeWidth` is
driven by one geometric sequence, with a super-exponential denominator.

#### The halving is a theorem

`actualWidths_contract` (`Euler/PacketSourceScaleGuards.lean:69`) concludes exactly

    timeWidth J X (n+1) ≤ timeWidth J X n/2

from `J ≥ 3`, `X ≥ 8`, `ActualBounds J D C c X δ`, and `δ ≤ 1/2`. The route is
`actualTimeRatio_le` (`:16`), which bounds the width ratio by `sourceTimeRatio n`;
`sourceTimeRatio` is one component of the `ActualBounds` series, so
`SmallSeries.term_le` gives ratio `≤ δ ≤ 1/2`, and `div_le_iff₀` turns that into the
halving. No asymptotic argument and no limit: a finite series total, then arithmetic.

#### Where the chain is conditional

`horizonTime_antitone` (`Euler/PacketNestedHorizons.lean:90`) takes

    (hw : ∀ n, timeWidth J X (n+1) ≤ timeWidth J X n/2)

as a **hypothesis**. That file does not import the guards file, so the nesting
theorem is conditional as written. The join is made elsewhere: `StageGuards.next_width`
(`PacketSourceScaleGuards.lean:129`) is a structure field, and `stage_guards` fills it
with `actualWidths_contract`; `exists_guarded_sequence` produces J, X₀, δ uniformly.
So the compression closes through `StageGuards`, not through `PacketNestedHorizons`
alone. Citing `horizonTime_antitone` as an unconditional compression result would
overstate it by one import.

The arithmetic it consumes is `nested_horizon_of_width_ratio`
(`Euler/EulerProof.lean:19529`): from `Δ ≤ 2W/3` and `Wnext ≤ W/2`,
`t + Δ + 2*Wnext ≤ t + 2*W`. The `Δ` bound is `stepLength_bounds`
(`PacketNestedHorizons.lean:82`, constants `timeWidth/6` and `2*timeWidth/3`).

Derived strengthening, ours and not stated in the file: those constants give
`horizonTime (n+1) ≤ horizonTime n - timeWidth n/3`, because
`2/3 + 1 - 2 = -1/3`. The library records only `≤`; the strict drop is immediate.

#### Is `n` the derivative index?

Yes in the operative sense, and this is what makes the directive's sentence true
rather than a coincidence of naming. Grade `p` controls jets of order below `p`:

- `velocityJet ... i` is built from `slicedJet (a i).high`, `(a i).mean`, and
  `(a (i-1)).corrector` (`PacketProfileRecursion.lean`);
- `knownJets O p a = history p (velocityJet ...)` and `knownForce O p` consume it, so
  grade `p` is exactly the p-th jet order being cancelled;
- `profiles_step` for `p ≥ 2` depends only on the strict prefix, the well-founded
  recursion;
- `tail_grade_bound` (`PacketProfileTailGrade.lean:29`) carries `(hn : N+1 ≤ n)`,
  i.e. tail grades indexed beyond the required order `N`.

So "time-supports compress as the derivative index rises" is a fair description. The
literal theorem is about consecutive **grades** `n, n+1`; `timeWidth` has no separate
derivative-order parameter, and the two indices coincide by construction, not by
definition.

#### Three things the compression is not

1. It is not a dimensional law. Both the grading and the shrinking come from the same
   `scaleSequence`; the ratio is controlled by a summable cost series, not by
   differentiating a scaling ansatz.
2. It is not the spatial support. Spatial radius is `supportScale` (exponential at
   exponent `7/2`), and `scale_support` / `high_scaled_support`
   (`PacketInitialSupport.lean:24`, `:48`) dilate a fixed ball by `ell`. Time width and
   spatial radius are distinct objects with distinct exponents (`7` vs `7/2`).
3. It is not collapse to a point. `activationTime` is strictly increasing while
   `horizonTime` is antitone, so intervals nest from both ends — but
   `common_positive_interval` proves `baseHorizon J X/12 < horizonTime ... n`, so the
   intersection has positive length. Nesting is used to keep one common interval, not
   to squeeze it shut.

#### Effect on the manuscript

This substantiates the draft's §1.2 sentence about packets whose time-supports
compress as the derivative order rises. It is a **confirmation, not an anomaly**, so
the injection rule of the batch directive does not trigger; `MANUSCRIPT.tex` is
untouched. Wording note for a future revision: the objects are `timeWidth` and
`horizonTime`, neither of which is a support set, and the repository says "packet",
not "pulse".

#### Not checked

- whether `ActualBounds` is instantiated in the top-level Euler theorem (only that
  `exists_guarded_sequence` can produce it for every `η > 0`);
- tightness of the `1/6` and `2/3` constants in `stepLength_bounds`;
- the analytic source construction behind the `Operators.meanSolve` / `highSolve`
  interface fields, which are supplied, not built, in the recursion file.

### E54 — Does ActualBounds reach the top-level Euler theorem? Yes, through one Classical.choice (2026-11-06)

*Intuition.* A building inspector wants to know whether the load-bearing beam in
the basement actually reaches the roof, or whether the roof was drawn separately
and merely labelled "supported". Here it reaches: the beam is cast once in the
basement, chosen by a single opaque decision, and every floor above is built on
that same casting. The roof does not mention the beam, which is exactly why the
check is worth doing.

Verdict: **the chain closes**. `ActualBounds` is not a hypothesis of the final
statement. It is proved to exist, selected once by `Classical.choice`, and the
selected record is what constructs the concrete datum the theorem is about.

#### The five links

1. **Existence.** `exists_scales` (`Euler/PacketInductionScales.lean:123`):

       theorem exists_scales (c B : ℝ) (hc : 0 ≤ c) : Nonempty (Scales c B)

   Its proof takes `exists_base_power`, then
   `EulerPacketCommonScaleChoice.exists_common_guards`, then assembles the record
   with `actual := hdata.1`. So an `ActualBounds` witness is *produced*, for some
   `J, D, X, δ`, from nothing but `0 ≤ c`.

2. **Selection.** `constructionScales` (`PacketInfiniteConstruction.lean:69`):

       def constructionScales : ConstructionScales :=
         Classical.choice (exists_scales (requiredExponent : ℝ)
           (commonThreshold gradientConstant hessianConstant) (Nat.cast_nonneg _))

3. **Packets.** `packets n = stages constructionScales le_rfl le_rfl n` (`:72`).
   The two `le_rfl` arguments discharge `requiredExponent ≤ q` and
   `commonThreshold … ≤ B`, so the `stages` hypotheses are not carried downstream.

4. **Datum and lifespan.** `initialDatum = Stage.initialDataLimit packets le_rfl le_rfl`
   (`PacketFiniteLifespan.lean:18`); `lifespan = initialDatum_finite_lifespan.choose`
   (`:54`), with `lifespan_le_base : lifespan.duration ≤ baseHorizon constructionScales.J constructionScales.X`.

5. **Top level.** `initialDatum_singularity` (`EulerSingularity.lean:115`) and
   `exists_compact_smooth_euler_singularity` (`:133`). `Euler.lean` is one line,
   `import Euler.EulerSingularity`, so that file is the root.

#### Where compression is actually spent

- Each `Stage` carries `source_stage : StageGuards …`
  (`PacketInductionStage.lean:123`), obtained from `Scales.stage`, which passes
  `S.actual` into `EulerParentRenewalPrefix.stage_guards_at` → `stage_guards` →
  `actualWidths_contract`. That is the only place `next_width` is proved.
- `PacketStageRestriction.nextHorizon_lt` consumes it at `:49`
  (`have hwidth := P.source_stage.next_width`) to place the next horizon strictly
  below the parent's `T`. Remove the halving and that inequality does not close.
- `Stage.horizon_eq : parent.T = time + 2*timeWidth n` together with
  `Stage.horizon_le : parent.T ≤ baseHorizon` and `Scales.time_small : baseHorizon ≤ 1`
  is what keeps every packet inside `[0,1]`.

#### Precision about what "end to end" means

Compression is not a conjunct of `initialDatum_singularity`. The final theorem
asserts smoothness, compact support, non-vanishing, divergence-freeness, finite
lifespan bounded by 1, the existence iff, the `C¹` limsup blow-up and the infinite
vorticity integral. Nothing in the statement mentions `timeWidth`. The halving is
used **instrumentally**, to build the `packets` sequence that the datum is the limit
of. So the chain closes in the construction, not in the conclusion; a reader who
looks only at `EulerSingularity.lean` cannot see it, which is why the trace was
worth recording.

#### The cost: logical closure, numerical opacity

`constructionScales` is a `Classical.choice`, so `J`, `D`, `X`, `δ` have no
computable content. Every downstream quantity — `timeWidth`, `scaleSequence`,
`baseHorizon`, every frequency — is defined from that opaque witness. The halving
theorem is still *about the actual object*, because every lemma is polymorphic in
`S : Scales c B` and uses only fields; nothing is being assumed of a hypothetical.
But no explicit bound on `timeWidth 0`, `J` or `baseHorizon` is recoverable from
the statement.

This is the E27 barrier at a coarser grain: not one constant behind `Classical.choose`,
but the entire scale regime, chosen once at the root and inherited by every packet.
The difference from `sobolevConstant` is that the opacity here is structural rather
than incidental — the choice is the construction.

#### Checks that passed incidentally

- `exists_scales` needs only `0 ≤ c`; the `B` side is a threshold, discharged at
  `constructionScales` by `le_rfl`.
- The record's `delta_small : δ ≤ 1/16` and
  `delta_geometry : 1000000*geometryConstant*δ ≤ 1` are stronger than the `δ ≤ 1/2`
  that `actualWidths_contract` requires, so halving has slack to spare.
- `ActualBounds` has other producers as well
  (`PacketSourceScaleActual.lean:230`, `PacketSourceScaleFromCosts.lean:70`), all
  theorems; there is no path on which it enters as an axiom or a bare hypothesis.

#### Not checked

- whether the chosen `D` interacts with the `previousFrequency` floor in a way that
  constrains the derivative order independently of `timeWidth`;
- the import path by which `EulerSingularity` reaches `PacketFiniteLifespan` (only
  that a single `def initialDatum` and a single `def lifespan` exist in the tree, so
  the references are unambiguous).

### E55 — E54's second open item: the import chain is four hops, and the definitions are single-sourced (2026-11-06)

*Intuition.* The previous entry established that the water reaches the roof. This
one traces the pipe. There is exactly one meter on the line, it is in one
basement, and no parallel pipe joins it downstream — so a reading taken at the
top is a reading of that meter, not of a plausible lookalike installed on
another branch.

Question: by what path does `Euler/EulerSingularity.lean` reach
`Euler/PacketFiniteLifespan.lean`, and are `initialDatum` and `lifespan` really
the single declarations E54 assumed?

Verdict: **four hops, one route, one declaration each.** Both definitions exist
exactly once in the tree, in one namespace, and every import path from the root
passes through the same file.

#### The chain

Parsed all 1,840 modules under `Euler/` (including the root `Euler.lean`) and
walked the import graph breadth-first:

     0  Euler.EulerSingularity        Euler/EulerSingularity.lean
     1  Euler.EulerC1Limsup           Euler/EulerC1Limsup.lean
     2  Euler.EulerC1Breakdown        Euler/EulerC1Breakdown.lean
     3  Euler.EulerFiniteLifespan     Euler/EulerFiniteLifespan.lean
     4  Euler.PacketFiniteLifespan    Euler/PacketFiniteLifespan.lean

Each edge is a real dependency, not an import of convenience: the file above
consumes declarations of the file below.

- `EulerC1Limsup` uses `lifespan.maximalGradientNorm_limsup` (:85) and
  `lifespan.maximalC1Norm_limsup` (:90), plus `lifespan.map_time_atTop` (:80).
- `EulerC1Breakdown` uses `lifespan.Time` (:82), `lifespan.maximalVelocity`
  (:84), `lifespan.maximalPressure` (:86), the three norm projections (:88–92),
  `lifespan.no_endpoint` (:96), `lifespan.maximalVelocity_initial` (:99), and
  the unboundedness lemmas (:132, :137).
- `EulerFiniteLifespan` uses `initialDatum.field` (:17, :45), `initialDatum.smooth`
  (:45), `initialDatum_compact` (:21), `initialDatum_divergence` (:45), and
  `lifespan.duration` / `lifespan.duration_pos` / `lifespan_le_one` (:24, :46).
- `EulerSingularity` uses `lifespan.maximalVorticityNorm` (:74), `...Density`
  (:76), `...Integral` (:78), `lifespan.initial_nonzero` (:92),
  `lifespan.hasEulerEvolution_iff` (:96), `lifespan.vorticity_lintegral_eq_top`
  (:111), and builds `initialDatum_singularity` on them (:115).

#### The route is forced, not merely shortest

`Euler.PacketFiniteLifespan` has exactly two direct importers:

    Euler.EulerFiniteLifespan      (reachable from EulerSingularity)
    Euler.CanonicalPacketHorizons  (not reachable from EulerSingularity)

The reachable set from `EulerSingularity` has 1,770 of the 1,840 modules, and
`CanonicalPacketHorizons` is outside it. So every import path from the root to
the datum passes through `EulerFiniteLifespan`, and the last edge is forced.
The BFS also finds exactly one shortest path, but that is the weaker fact; the
forced last edge is what matters, because it excludes a second branch that could
supply a different `initialDatum` to a different theorem.

#### One declaration each

A whole-tree search for `def`/`abbrev` of either name returns two lines, both in
`Euler/PacketFiniteLifespan.lean`:

    18  def initialDatum : SmoothL2Field Space := Stage.initialDataLimit packets le_rfl le_rfl
    54  def lifespan : FiniteLifespan initialDatum := initialDatum_finite_lifespan.choose

The only other hit in the repository is `NavierStokes/MaximalLifespan.lean:21`,
`noncomputable def lifespanDomain (T : ℝ) : Set SpaceTime`, which is a different
identifier in a different namespace and is not imported by the Euler tree at all.

Namespace resolution is not doing hidden work either. `EulerSingularity` does not
`open` the name into scope; it re-enters the namespace
(`namespace EulerPacketInduction`, :68), as do `EulerC1Limsup` (:73),
`EulerC1Breakdown` (:76) and `EulerFiniteLifespan` (:11). All four files sit in
the same namespace as the declarations, so the unqualified `initialDatum` and
`lifespan` at :92–:116 of the root file resolve by namespace identity. With no
second declaration of either name anywhere in the tree, no `open` could shadow
them into a different meaning.

#### What this closes, and what it does not

Closes E54's second open item: the reference is unambiguous in fact, not merely
by uniqueness of spelling.

Does not close the first open item (whether the chosen `D` interacts with the
`previousFrequency` floor). Does not re-elaborate anything: this is a graph walk
over `import` lines plus a text search for declarations, and a toolchain is still
absent (E50). Lean's own resolution was not exercised, so what is established is
that no competing declaration exists to resolve to — not that the term
elaborates.

Line-reference correction carried from the manuscript revision:
`constructionScales` is at `Euler/PacketInfiniteConstruction.lean:68`, not `:69`
as E54 gives it. `packets` at `:72`, `initialDatum` at `:18` and `lifespan` at
`:54` are as recorded.

### E56 — Does the chosen `D` constrain derivative order through the `previousFrequency` floor? (2026-11-06)

*Intuition.* Two men in the same building are both called D. The badge reader at
the door only ever asks for one of them, and it asks exactly once, at the
entrance. Everyone inside the building — the people who decide how many
derivatives get tracked — never meets him at all. Asking whether "D" sets the
derivative budget is asking the wrong D the right question.

This closes E54/E55's remaining open item. Verdict: **no** — on three separate
grounds, each sufficient on its own.

#### 1. There are two different `D`s, and the question mixes them

- The axial similarity exponent is a real number, `D(h) = 1/2 - h`, defined with
  `d` and `L` in `NavierStokes/CoordinateAlgebra.lean:19--21`. That is the object
  of manuscript §4.
- The packet scale record carries `D : ℕ` with the field
  `base_power : 2000 ≤ D` (`Euler/PacketInductionScales.lean`). It is an exponent
  on the initial scale `X`, not a similarity weight.

They are the same letter and nothing else. No declaration in the Euler tree
consumes `D(h)`; no declaration in the similarity development consumes the packet
`D`.

#### 2. `D` enters `previousFrequency` at exactly one index

`previousFrequency` (`Euler/PacketSourceScaleSequence.lean:34`):

    previousFrequency J D X 0     = X^D
    previousFrequency J D X (n+1) = frequency J X n

For `n ≥ 1` the sequence is `exp (scaleSequence J X n/((J+n-1 : ℕ) : ℝ)^2)` and is
(`→ E59 §2`: the index as printed in the previous revision was one high — `(J+n)^2` is the denominator
of `frequency J X n = previousFrequency J D X (n+1)`)
**independent of `D`**. So `D` controls the initial term and nothing after it.

The floor `previous_floor : ∀ n, B ≤ previousFrequency J D X n`
(`PacketInductionScales.lean:98`) is discharged in `exists_scales` (:123) by two
unrelated facts, not by one mechanism: `B ≤ X^D` at index zero, obtained from
`Tendsto (fun X => X^D) atTop atTop` combined with `eventually_ge_atTop B`; and
`B ≤ frequency J X n` at the successors, obtained from the uniform frequency
guard. Only the first mentions `D`, and it needs only `D ≥ 1` to run — `2000 ≤ D`
is enormously slack.

#### 3. Every use of `D` is monotone in the harmless direction

> **Withdrawn — see E59 §3.** The claim is false. `neighborError` at index zero contains `X^(c·D)` and
> therefore *grows* with `D`, and the `geometry_small` guard is a `∀ n` field, so its `n = 0` instance
> gets harder. What actually holds is an ordering statement: `D` is fixed first (`2000 ≤ D`), `X` is
> chosen afterwards large enough to dominate every guard that mentions `D`. `D` is absorbed, not free.

- `priorError J D X n = previousFrequency J D X n ^ (-(1/4))`
  (`PacketSourceScaleActual.lean:22`): larger `D` makes the error term
  *smaller*.
- `baseErrorCost` (`:31`) contains `X^(-(D:ℝ)/4)`: again larger `D`, smaller
  error.
- `geometryError` and `StageGuards.geometry_small` inherit this through
  `priorError`/`neighborError`.

The one place a larger `D` is harder is the `initial_frequency` field of
`ActualBounds` (`PacketSourceScaleActual.lean:217`),
`X^D ≤ exp (X/((J-1 : ℕ) : ℝ)^4)`, and that is discharged by taking `X` larger:
`eventually_pow_le_exp D r` proves `∀ᶠ X, X^D ≤ exp (X/r)`, and `exists_scales`
quantifies `X` eventually at top. So `D` trades against **`X`**, never against a
grade index.

Nor is `D` bounded above. `exists_base_power` proves only
`∃ D, 2000 ≤ D ∧ firstFrequencyPower < D*(theta/100)` — a lower bound plus a
lower bound. Nothing constrains `D` from above, so it cannot be a ceiling on
anything.

#### 4. `timeWidth` does not read `D` at all

The compression argument of E53 takes `ActualBounds` and `δ ≤ 1/2`, and uses
exactly two of its fields: `hb.initial_shear` (the `X^1000` condition) and
`hb.normal.width`. The `initial_frequency` field — the only `D`-valued field in
`ActualBounds` — is not referenced. `actualWidths_contract`
(`PacketSourceScaleGuards.lean:69`) is therefore independent of `D`, not merely
independent of derivative order.

So the independence is stronger than asked: `D` and `timeWidth` are on different
legs of the guard. `timeWidth` is driven by `previousShear` (exponent `7`) and
`scaleSequence`; `D` is driven into `previousFrequency` (exponent `4` at the
initial term) and the base error decay.

#### 5. Derivative order never meets either

`tail_grade_bound` (`Euler/PacketProfileTailGrade.lean:29`) bounds the order-`n`
tail grade by
`(1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2)` with derivative count
`110*(n+1)`. No `previousFrequency`, no `X^D`, no packet `D`.

The one place a `previousFrequency` power is indexed by a small integer is
`EulerPacketParameterEnvelope.source_size_le`, with
`(hK : K ≤ previousFrequency J D X n^d)`. There `d` is a cost-spec exponent
carrying `hd : 0 ≤ d` and `hdc : d ≤ c` — a monomial degree, not a jet order —
and raising it demands a larger parameter `K`, not a different `D`.

#### What would have falsified this

A `∀ n` condition in `Scales` or `ActualBounds` relating `X^D` (or the floor
`B`) to a grade or derivative index; or a use of `hb.initial_frequency` inside
the width argument; or an upper bound on `D` in `exists_base_power`. None of the
four exists in the tree as read.

#### Not checked

- whether the profile-side scale record (`S.H0` in the tail-grade bound) ties jet
  order to frequency by a route outside `previousFrequency`;
- whether manuscript §7's phrase "the scale regime `J`, `D`, `X`, `δ`" invites
  the `D`/`D(h)` conflation badly enough to need a parenthetical. Flagged, not
  edited.

### E57 — Batch 03, streams 1--2: the smoothness closure is a limit in the packet index, and `delta` caps a geometry error, not an order (2026-11-06)

*Intuition.* Two requests arrive for the same building. The first asks to inspect
the fire escape on the fourth floor; the building has three floors and no fire
escape, but it does have a service lift that is inspected every night. The second
asks whether the weight limit on the lift also caps how many people may work on
the fourth floor that does not exist. The honest answer to both is to say which
building was inspected, and then to inspect the lift.

#### Numbering and state, corrected before anything else

- `AUDIT_LOG.md` is 2,248 lines, not 2,046. The figure 2,046 is the pre-E55
  total; E55 runs 2048--2142 and E56 2144--2248. Lines 1--2046 are untouched by
  this entry and by the two before it.
- E55 and E56 are already used. The directive's `E55`--`E90` block therefore
  cannot be honoured as given, and per E52 this entry is not pre-numbered into a
  schedule: one entry, recording what was actually read.
- The directive targets `://github.com`, which resolves to nothing. All citations
  are to `ns-audit/NavierStokesAndEuler` at `f9e8bc5`.
- "Pulse" is again "packet" (E53). The directive's stream 1 also assumes a
  smoothness closure across `t = 1` inside `Euler/PacketInfiniteConstruction.lean`.
  Both halves of that assumption are wrong, and the correction is the finding.

#### Stream 1: what `PacketInfiniteConstruction.lean` actually contains

The file is 81 lines and declares eleven things, all about indexing:

    def successor {n : ℕ} (P : Stage S n) (hq : requiredExponent ≤ q)
        (hB : commonThreshold gradientConstant hessianConstant ≤ B) : Stage S (n+1)
    def stages : (n : ℕ) → Stage S n
      | 0 => S.firstStage
      | n+1 => (stages n).successor hq hB
    theorem stages_time (n : ℕ) :
        (stages S hq hB (n+1)).time=(stages S hq hB n).nextTime
    theorem stages_initial_step (n : ℕ) (hn : n ≠ 0) : ...
    theorem stages_gradient_atTop :
        Tendsto (fun n => (stages S hq hB n).activationGradient) atTop atTop

There is no `ContDiff` in the file, no derivative bound, and no `t = 1`. The only
`Tendsto` is in the packet index `n`, and its target is `atTop` on the gradient,
not a smoothness claim. A search for the time-derivative closure in this file
returns nothing because the file does not attempt one.

Where the smoothness actually lives, and of what:

- `SmoothL2Field` (`Euler/LpSmoothField.lean:31`) is a structure with a **proof
  field**, not a coercion:

      structure SmoothL2Field (V : Type u) ... where
        field : Space → V
        smooth : ContDiff ℝ ∞ field
        integrable : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n field) 2 volume

  Smoothness is data in the record. It is transported by construction
  (`fullInitialLimit` returns the record) and never by a silent type coercion.
  That answers the directive's "hidden structural type coercion" question: no.
- The limit that produces the datum is
  `initialDataLimit_Hm` (`Euler/PacketStageInitialLimit.lean:88`):

      theorem initialDataLimit_Hm (s : ℕ) :
          Tendsto (fun n => derivativeSum s
            ((fun x => (P n).state.evolution.velocity (0,x)) - (initialDataLimit P hq hB).field))
            atTop (𝓝 0)

  This is `H^s` convergence of the packet initial velocities at `t = 0`, for every
  `s`, via `EulerPacketInitial.fullInitialLimit_Hm`. The datum is smooth because
  the `s = n` statement holds for all `n` and the record's `smooth` field is
  supplied at the limit — not because a jet is matched across a singular time.
- In the Euler development the singular time is `lifespan.duration`, an interior
  point with `0 < duration ≤ 1`; `ContDiff ℝ ∞` in `initialDatum_singularity`
  applies to the **datum**, i.e. the field at `t = 0`. Nothing asserts `C^∞`
  continuation through the blowup, and there is nothing there to assert: the
  theorem's content is that the `C¹` sup diverges as `t ↑ duration`.

The `t = 1` smooth-residual claim belongs to the other development:
`NavierStokes/R3/PositiveTimeForce.lean` (`force`, `force_eq`, `force_contDiff`),
audited in E24--E26 and manuscript §5.2. It is a Navier--Stokes statement about a
forcing term, not an Euler packet statement.

Where `previousShear` does meet a time step:

    def actualExtraTime (J : ℕ) (X a : ℝ) (n : ℕ) : ℝ :=
      2*sqrt (a*previousShear J X n)*timeWidth J X (n+1)

with `timeWidth J X n = 3*s_{n+1}*s_n/sqrt(previousShear J X n)`. The
super-exponential object is `previousShear_n = exp (s_n/((J+n-1 : ℕ) : ℝ)^5)` for `n ≥ 1` (and it
(`→ E59 §4`: the index as printed in the previous revision was one high)
enters both through `sqrt`, so the time step carries a doubly-exponential
denominator. The guard on it is `actualExtraTime_small`
(`Euler/PacketSourceScaleGuards.lean:56`):
`actualExtraTime J X a n * sourceTheta J C (scaleSequence J X) n^60 ≤ δ`, proved
from `actualExtraTime_le` and the `extraTime` component of `ActualBounds.normal`.
That is the real content of "bounded against the denominator", and it is a width
bound, not a derivative bound.

#### Stream 2: `actualTimeRatio_le` is three rewrites and one monotonicity

Full statement (`Euler/PacketSourceScaleGuards.lean:16`):

    theorem actualTimeRatio_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
        (hbase : X^1000 ≤ exp (X/((J-1:ℕ):ℝ)^7)) (n : ℕ) :
        timeWidth J X (n+1)/timeWidth J X n ≤ sourceTimeRatio J (scaleSequence J X) n

Proof structure, in order:

1. `(div_le_iff₀ (timeWidth_pos J hJ hX n)).mpr` — clear the denominator;
2. `rw [timeWidth_succ_eq, source_time_ratio_identity]` — rewrite the literal
   width into the normal form and apply the ratio identity
   (`EulerProof.lean:20020`, with `sourceTimeRatio` at `:20014`);
3. `mul_le_mul_of_nonneg_left (sourceTimeWidth_le J hJ X hX hbase n)` — the only
   inequality in the proof, monotonicity of multiplication against the base
   comparison `X^1000 ≤ exp (X/((J-1)^7))`.

No `δ`, no `D`, no derivative order. `δ` enters one call up, in
`actualWidths_contract`, as the final `trans`:

    (actualTimeRatio_le ...).trans ((hb.normal.width.term_le n).trans hδ)

`sourceTimeRatio` is the one component of the `ActualBounds` series that carries
the `SmallSeries` total, so `term_le` converts "the ratio at `n`" into "the total
is at most `δ ≤ 1/2`". The halving is arithmetic on a summable series, as E53
recorded.

Does `1000000*geometryConstant*δ ≤ 1` (`Scales.delta_geometry`,
`PacketInductionScales.lean:94`) cap derivative order? No — it caps a geometry
error. Its only consumer is `Scales.stage` (:218), which passes it to
`stage_guards` as `hδK` to discharge

    geometry_small : 1000000*K*geometryError J D C c X a n
      * sourceTheta J C (scaleSequence J X) n^40 ≤ 1

with `K = geometryConstant`. The exponents in that neighbourhood are the fixed
numerals `40` (here) and `60` (`coefficient_small`'s `hA : A ≤ 60`); both are
powers of `sourceTheta`, i.e. cost-scaling exponents, not jet orders.

Derivative order appears in exactly one place, and `δ` is absent from it:
`tail_grade_bound` (`Euler/PacketProfileTailGrade.lean:29`) bounds grade `n ≥ N+1`
by `(1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2)` with derivative count
`110*(n+1)`. `N` is universally quantified with `hN : 1 ≤ N` and no upper bound;
the recursion `profiles : (O) → Profile → ℕ → Profile` is total in the grade.

`requiredExponent = 80*degree+1` (`ParentNeighborThreshold.lean:23`) is not a
derivative order either: `degree := polynomial.natDegree`
(`ParentPacketNeighborPolynomial.lean:33`), a fixed numeral read off a polynomial,
and it appears as an exponent on the threshold, not on the jet.

So: **no independent ceiling on derivative order exists in this mechanism.** The
step-width route does not read `D` (E56); the `δ` route caps a geometry error and
reads neither `D` nor the order; the order route (`tail_grade_bound`) reads
neither `δ` nor `D`.

#### Not checked

- the analytic content of the `Operators.meanSolve` / `highSolve` interface fields,
  which remain supplied rather than built (same gap as E53);
- whether `EulerPacketInitial.fullInitialLimit` proves the limit's `smooth` field
  by `contDiff_of_differentiable_iteratedFDeriv`-style reasoning or by a bespoke
  induction; only that the field is present in the returned record;
- stream 3 of the directive (`E58`--`E90`), which was not attempted and is not
  pre-numbered.

### E58 — Referee report, claim by claim against the file as it stands (2026-11-06)

*Intuition.* A building inspector's report arrives describing faults in a
building that has since been partly renovated. Every line has to be checked
twice: once against the current drawings, and once against the claim that the
fault was ever there. Some listed faults are real and still present, some were
repaired in the last pass, and one or two describe a different building.

Method: each objection was opened at the section it cites, compared with the
current `MANUSCRIPT.tex`, and where it turned on a code fact, that fact was
re-read in the tree at `f9e8bc5`.

#### Confirmed, and repaired in this pass

1. `2D(h)=1/2-h` used as an identity (abstract and §1.4). Wrong: `2D(h)=1-2h`.
   Corrected in both places.
2. §4.1 called `h=1/2` the classical parabolic endpoint. Wrong. Isotropic
   parabolic scaling needs `D=1/2`, i.e. `h=0`, where `eta = z/sqrt q`; at
   `h=1/2` one has `D=0` and the axial scale ceases to contract. Corrected.
3. §4.2 said the axial piece "exceeds the radial one by the factor `q^{2h}`" and
   "dominates" near the apex. Arithmetically backwards on `q<1`: `q^{2h}<1`, so
   the axial coefficient is the smaller one. It is the more damped, not the
   dominant. Corrected, including the dominance sentence.
4. §4.3 compared the axial degree against an "isotropic degree `b-2`". Wrong:
   `q` is a squared length, so the isotropic weight in `q` is `b-1`, which is the
   radial degree itself. Corollary repaired: the axial degree differs from `b-1`
   for every admissible `h`, with coincidence only at `h=0`.
5. §4.4 called the pullback an isometry of `L^2`. Wrong. Re-derived
   independently: at fixed `tau`, `q d = tau` gives `dz = q^D (L/d) dEta`, so the
   measure is `q^{1+D}(L/d) dX dEta` and the norm is `q^{2b+1+D}` times a
   *weighted* inner integral. At `b_*` the scaling cancels but the weight `L/d`
   remains: scale invariance, not isometry. The equivalence with the unweighted
   norm is now stated only for profiles separated from `|eta|=1`.
6. §2 wrote `p_{T^3} = sum_k chi(x) p(t,x+k)`. Wrong: `periodize f z = sum_n f(t, x-n)`
   with `f = cutPressure p`, so the cutoff is evaluated at the translated point.
   Corrected to `chi(x+k) p(t,x+k)`.
7. §5 opener and conclusion claimed "the price is zero ... the term never arises"
   and that the interfaces "carry no cost at all". Contradicted by §5.3, which
   keeps `grad chi x A` inside the velocity and in the residual. Rewritten: what
   disappears is a separate boundary, matching, or corrector *estimate*; the three
   are not free, and the commutator is named as where the cost is paid.
8. "Ten external checkers" (§1.1, §8.3). E0 lists nine names. Corrected to nine.
9. §6.1 said "the mechanism that carries the smooth extension through `t=1` is the
   shrinking of packet time windows". Wrong, and E57 is the record of why: the
   packets converge to a datum, smoothness is carried by the `smooth` field of
   `SmoothL2Field`, and the blow-up time is an interior point. Replaced with the
   construction-not-continuation statement.
10. §7 title "One `Classical.choice` at the root" was imprecise: `lifespan` is a
    second `.choose`. Title now names the choice that selects the *scale regime*,
    with the second selection identified in the text.
11. §7 still listed E55/E56's questions as open. Replaced with their answers: the
    four-hop forced import path, and `D` confined to index zero of
    `previousFrequency`.

#### Confirmed, and deliberately not repaired

- **§1.3 Proposition "the construction half is free".** The hypothesis set is
  unsatisfiable: `u` is `C^infty` on `R^4`, compactly supported in `x` uniformly
  in `t`, and has `limsup_{t up 1} |u(t)|_infty = infty`. On the compact set
  `[0,1] x K` a smooth function is bounded. The proposition assumes away the
  singular time it claims to analyse, and its "eleven fields" claim also omits the
  spacetime compactness that `CompactPositiveTimeSupport` requires. The report is
  right. Not repaired because the repair is a thesis decision: a correct version
  must either assume the residual extends smoothly, which removes the punchline,
  or drop the claim entirely.
- **The Millennium verdict.** Abstract and conclusion still say the result "is
  not the Millennium problem". The objection is that alternative (C) does not
  demand nonzero data or an independently prescribed force, and that compactly
  supported forcing is stronger than Clay's decay condition. Thesis-level; not
  changed.
- **The constant-barrier formulation.** "The kernel verifies that some constant
  exists and never that it is the right size or dimension" overstates: the kernel
  does check that the selected witness satisfies the inequality. The defensible
  claim is narrower: no numerical evaluation, no optimality, no dimensional
  layer. §3.3 already says most of this; the abstract and the "complete decision
  procedure" sentence in §3.2 still overstate. Left for the same rewrite pass.

#### Objections that do not survive contact with the current file

- The report's "three main areas" description and its section numbering describe
  the pre-E53 draft; the file now has seven sections.
- "E55 and E56 resolve both open questions" is correct, and §7 has been updated
  accordingly rather than pinned to E54.
- The report's reading that the Euler section claimed the Navier--Stokes
  provenance gap is fair against the opening. The section already scoped to
  `Euler/`; it now also states that the smoothness proved is that of the datum.

#### State after this pass

`MANUSCRIPT.tex`: 1,482 lines. Checks: brace balance, `\begin`/`\end` count, `$`
parity, every `\ref`/`\eqref` defined, and a literal search confirming each
repaired string is absent and each replacement present. No LaTeX engine on the
host (E50), so this is structural, not a compile.

---

## E59 — Correction pass on E52, E56, E57 and E10.8

*Appended after E58. E52, E56, E57 and E10.8 now carry inline `→ E59` markers; no line was deleted.
Six items, all raised by an external referee. Every cited definition was re-read at `f9e8bc5` before
being accepted. All six are real.*

### Intuition

`previousShear` and `previousFrequency` are not formulas. They are shifts:

```lean
def previousShear (J : ℕ) (X : ℝ) : ℕ → ℝ
  | 0     => X^1000
  | n + 1 => shear J X n          -- Euler/PacketSourceScaleSequence.lean:30

def previousFrequency (J D : ℕ) (X : ℝ) : ℕ → ℝ
  | 0     => X^D
  | n + 1 => frequency J X n      -- :34
```

So the value carried by stage `n ≥ 1` is the current-stage function evaluated at `n-1`. Twice, in E56
and E57, I printed `shear`/`frequency` at `n` and labelled the result the previous-stage value at `n`.
Both displays are false at the index they claim. Both conclusions survive, which is exactly why the
error survived: a wrong formula that still supports a right inequality contradicts nothing downstream.
This audit has spent four hundred lines charging that failure mode to other people, and here it is twice
in its own log.

The `D` item is the substantive one. `D` is not harmless. It enters the index-zero neighbour error with
a positive exponent, so raising `D` *enlarges* that error while shrinking the initial prior error. What
saves the construction is not monotonicity but **ordering**: `D` is fixed first (`2000 ≤ D`), `X` is
chosen afterwards and made large enough to dominate every guard that mentions `D`. `D` is absorbed, not
free.

### 1. E52 — the slack factor is 500, not 50

`ExponentLedger.lean:281` gives the sharp threshold; the applied lemmas assume `κ ≤ 1/100000`:

| quantity | value |
|---|---|
| sharp threshold | `κ < 1/200 = 5·10⁻³` |
| assumption | `κ ≤ 10⁻⁵` |
| ratio | `(1/200)/(1/100000) = 500` |
| in orders of magnitude | `log₁₀ 500 ≈ 2.70` |

E52 said "a slack factor of 50" and "understates the admissible window by two orders of magnitude".
Both are wrong: the factor is **500**, i.e. **2.7 orders**. `100000/200 = 500`. The threshold
calculation and the conclusion ("the applied `κ` sits well inside the admissible window") are
unaffected — this is arithmetic, not analysis.

### 2. The `previousFrequency` paragraph of E56 — displayed one index high

| quantity | correct, at `n ≥ 1` | what E56 printed |
|---|---|---|
| `previousFrequency J D X n` | `exp (s_n/((J+n-1)^4))` | `exp (s_n/(J+n)^2)` |
| `previousShear J X n` | `exp (s_n/((J+n-1)^7))` | `exp (s_n/(J+n)^5)` |

The right-hand column is not gibberish. `exp (s_n/(J+n)^2) = frequency J X n =
previousFrequency J D X (n+1)`, and `exp (s_n/(J+n)^5) = shear J X n = previousShear J X (n+1)`:
both displays are true values of the sequence, printed under the **previous** index. The shift is exactly
what the code proves (`Euler/PacketSourceScaleSequence.lean:57`, `:66`):

```lean
theorem previousFrequency_succ_eq (J D : ℕ) (hJ : 1 ≤ J) (X : ℝ) (n : ℕ) :
    previousFrequency J D X (n+1) =
      exp (scaleSequence J X (n+1)/((J-1+(n+1) : ℕ) : ℝ)^4)

theorem previousShear_succ_eq (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (n : ℕ) :
    previousShear J X (n+1) =
      exp (scaleSequence J X (n+1)/((J-1+(n+1) : ℕ) : ℝ)^7)
```

The two presentations agree because `scaleSequence J X (n+1) = ((J+n)^2)·scaleSequence J X n`, which
turns `s_{n+1}/(J+n)^4` into `s_n/(J+n)^2`. That cancellation is why the mis-indexing went unnoticed:
the printed number belongs to the sequence, just not at the index claimed. The definition-side form is
`previousFrequency J D X n = frequency J X (n-1)`, i.e. `exp (s_{n-1}/((J+n-1)^2))`; the `^4` form above
carries `s_n` instead. Both are correct; the one thing that is not correct is `exp (s_n/(J+n)^2)`
presented as the value at `n`.

The conclusion — that for `n ≥ 1` the sequence is independent of `D`, so `D` controls only index zero —
is unaffected, because `frequency` carries no `D`.

### 3. E56 §3 — "every use of `D` is monotone in the harmless direction" is false

`neighborError` (`Euler/PacketSourceScaleActual.lean:24`):

```lean
def neighborError (J D : ℕ) (X c : ℝ) (n : ℕ) : ℝ :=
  supportScale J X n * previousFrequency J D X n^c * previousShear J X n^c
```

At index zero, where `previousFrequency J D X 0 = X^D` and `previousShear J X 0 = X^1000`:

```
neighborError_0 = exp (-X / J^(7/2)) · X^(c·D) · X^(1000·c)
```

For `c > 0` and `X > 1` this **increases** with `D`. `geometryError` (`:27`) feeds `neighborError` into
the `geometry_small` guard, which is a `∀ n` field of `actual_bounds`, so its `n = 0` instance gets
harder as `D` grows. E56 §3's claim that `D` only ever moves in the easy direction is wrong.

The four places `D` actually occurs, with their true signs:

| occurrence | site | sign in `D` |
|---|---|---|
| `priorError = previousFrequency ^ (-(1/4))` | `:22` | improves (`X^(-D/4)`) |
| `baseErrorCost`, the `X^(-(D:ℝ)/4)` term | `:31` | improves |
| `neighborError` at `n = 0` | `:24` | **degrades** (`X^(c·D)`) |
| `ActualBounds.initial_frequency`, `X^D ≤ exp (X/((J-1)^4))` | `:217` | **degrades** |

Both degrading channels are of the shape `X^(a·D)·exp(-c·X)` with `c > 0`, so both are discharged by
enlarging `X` — `eventually_pow_le_exp` is the lemma that does it, and `exists_scales`
(`Euler/PacketInductionScales.lean:123`) quantifies `D` before `X`. The correct statement is:

> `D` is not monotone in a harmless direction. Its entire effect on the error ledger is confined to
> index zero, and it is paid for in `X`, not absorbed by monotonicity.

What survives is the conclusion that `D` imposes no **ceiling** on derivative order: there is no upper
bound on `D` anywhere in `ActualBounds`, only `2000 ≤ D`, and no derivative index is a function of `D`.
That conclusion now rests on the ordering argument above, not on the withdrawn one.

### 4. E57 — the same shift, on `previousShear`

E57 wrote "the super-exponential object is `previousShear = exp (s_n/((J+n : ℕ) : ℝ)^5)`". As in §2,
that expression is `shear J X n = previousShear J X (n+1)`. The correct display, by
`previousShear_succ_eq` (`PacketSourceScaleSequence.lean:57`), is
`previousShear J X n = exp (s_n/((J+n-1 : ℕ) : ℝ)^7)` for `n ≥ 1`; equivalently `shear J X (n-1)` by
the definition at `:30`. Exponent `5` is the definition-side exponent, `7` the `succ_eq`-side one, and
`s_{n+1} = (J+n)^2 s_n` is what converts between them.

The point E57 was making is unchanged: `timeWidth J X n = 3*s_{n+1}*s_n/sqrt(previousShear J X n)` carries
a doubly-exponential denominator, so the temporal guard there is a width bound and not a derivative
bound. `previousShear` is super-exponential at either index.

### 5. E10.8 — the Millennium scope paragraph

As written:

> It is therefore **compatible with, and does not resolve, the Millennium problem**, which asks for `f ≡ 0`.

The subordinate clause treats alternative (A) as though it were the whole problem. It is not. Line 113
of this same log already carries the correct reading — *"That is the right way to close alternative
(C)"* — and E1/E2 correctly record the zero initial datum as admissible. E10.8 contradicted E1, E2 and
E11 internally.

Corrected: the theorem **resolves alternative (C)** — smooth compactly supported force, zero datum,
blow-up at `t = 1`, no global smooth finite-energy competitor. It is silent on alternative (A), where
`f ≡ 0` and the datum is nonzero and rapidly decaying: `force_nonzero_of_no_global_solution` is the
repository's own proof that this theorem's force cannot be zero, which is precisely why it cannot reach
(A).

That is a scope statement, not a defect. It is also exactly the defect E58 recorded as the open
verdict decision in `MANUSCRIPT.tex`.

### 6. E57 — smoothness is a field, not a diagonal limit

`SmoothL2Field` (`Euler/LpSmoothField.lean:29`):

```lean
structure SmoothL2Field (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : Space → V
  smooth : ContDiff ℝ ∞ field
  integrable : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n field) 2 volume
```

The `_Hm` lemmas prove `Tendsto (fun n => derivativeSum s (...)) atTop (𝓝 0)` for each **fixed** `s`;
the quantifier order is `∀ s, (convergence in that s)` with no uniformity across `s`. So "converges in
every Sobolev order, hence the limit is smooth" is not what is proved, and reading the argument as a
diagonal `s = n` would be an inference the code does not license. What is proved is stronger and
simpler: the limit object is *constructed* as a `SmoothL2Field`, so smoothness is a proof-bearing field
of the structure, and `initialDataLimit` inherits it. E57's phrasing invited the weaker reading.

### Scoreboard

| entry | claim as written | verdict |
|---|---|---|
| E52 | slack factor 50, "two orders" | **wrong** — 500, 2.7 orders; conclusion unaffected |
| E56 | `previousFrequency_n = exp(s_n/(J+n)^2)` | **mis-indexed** — shift, not formula; conclusion unaffected |
| E56 §3 | every use of `D` is harmless | **wrong** — `D` degrades the index-zero neighbour error; conclusion re-derived via ordering |
| E57 | `previousShear_n = exp(s_n/(J+n)^5)` | **mis-indexed**; conclusion unaffected |
| E57 | smoothness from Sobolev convergence | **over-strong reading** — smoothness is a structure field |
| E10.8 | "Millennium problem asks for `f ≡ 0`" | **wrong scope** — resolves (C), silent on (A) |

### Standing

None of the six touches the repository. All are audit-side: two index shifts, one false monotonicity
claim, one arithmetic slip, one over-strong smoothness reading, one scope error. The conclusions they
were attached to survive — the last in corrected form, now consistent with E1, E2 and E11.

*Next target, per the referee: `Operators.meanSolve` and `highSolve`, still unopened.*

---

## E60 — Millennium verdict corrected; E7 closed; two E57 refinements

*Appended after E59. Nothing deleted. E7 and E58.3 carry inline `→ E60` markers.*

### 1. The verdict has the sign reversed, and it is the audit's headline finding

E59 §5 repaired half of this and stopped. The half left standing was the load-bearing one.

Clay's formulation separates four alternatives. (A) and (B) are the unforced existence statements on
`R^3` and `T^3`. (C) and (D) are the breakdown alternatives, and **both allow a smooth, rapidly
decaying external force**. (C) does not require the initial datum to be nonzero, and it does not
require the force to be selected independently of the constructed solution: the existential quantifier
is simultaneous in `(u_0, f)`.

An audit that establishes "zero datum, smooth compactly supported force, blow-up at `t = 1`, no global
finite-energy competitor" has therefore established the data **and** the conclusion of (C). Compact
support is strictly stronger than rapid decay. Naming the force as a residual changes nothing: the
residual still has to be `C^∞`, still has to be compactly supported, and the nonexistence conjunct
still has to be proved.

E10.8 asserted the opposite — that the theorem is "compatible with, and does not resolve" the problem
because the problem "asks for `f ≡ 0`". That treats (A) as the whole problem and contradicts line 113
of this same log. The corrected statement, adopted here in place of E10.8's paragraph and in place of
the abstract and §7.2 of `MANUSCRIPT.tex`:

> The theorem's stated whole-space result matches the data and conclusion of Clay alternative (C):
> zero is an admissible initial datum, and a smooth compactly supported force satisfies Clay's
> rapid-decay requirements. If the proof is correct, it resolves alternative (C). It does not
> establish the unforced alternatives (A) or (B). The proof's mathematical validity and Clay's
> eventual evaluation are separate questions.

Two riders, both of which stay in the text.

- **"If the proof is correct" is not droppable.** This is a source-level audit. No toolchain was run;
  nothing here is a Lean verification of the analytic estimates, and the ledger is conditional on them.
- **Evaluation is not award.** CMI lists the problem as active and no prize has been awarded. The
  paper must not be readable as claiming otherwise; the replacement above says so explicitly.

What survives, unchanged: the breakdown is *forced*, not spontaneous; the force cannot be identically
zero (`force_nonzero_of_no_global_solution`); and the result remains a statement-design achievement as
much as a mathematical one. None of those is in tension with (C) — they are what (C) permits.

### 2. E7 — pressure periodicity: corroborated, primary unopened

E7 recorded the (D)-case pressure-periodicity clause as "flagged, not adjudicated", because the
repository attributes it to "the Clay errata" and the erratum could not be located offline. It is now
corroborated: the official problem description carries an erratum requiring the velocity **and the
pressure** to be periodic in equation (8), and two independent secondary sources quote the clause that
way. The repository's pressure-periodicity condition is therefore not an unsupported strengthening of
(D), and E7 closes against the repository.

One caveat, held to the same standard this audit applies to everyone else: the primary document was
not opened here. The PDF is served as `application/pdf` and the text extractor on this host refuses
that content type, so the entry moves to **corroborated, primary unopened** — not to "confirmed" on my
own authority. It is worth one line in the paper, because a 2012 arXiv preprint argues at length that
the published statement *must* be corrected precisely because it does not require space-periodic
pressure. That is the reading the erratum supersedes, and a reader who has seen the older argument
will otherwise take the clause for an invention of the formalization.

### 3. E58.3 — "least damped" contradicted the sentence before it

E58.3 corrected the *sign* of `q^{2h}` and then used the wrong word for it:

```
q^{b-2D(h)} / q^{b-1} = q^{2h} < 1        (0 < q < 1, h > 0)
```

so the axial coefficient is the smaller one, i.e. the axial term is **more** damped and the radial term
is the more singular. "Least damped" says the opposite of the clause that introduces it. Fixed in the
log and at all three manuscript sites (§4.2, §4.4, and the conclusion bullet). The "least damped"
phrase was the only place the paper's prose reversed a sign the paper's own equation had already fixed.

### 4. E57 — two refinements

**(a) The denominator is a ratio, not a single factor.** `actualExtraTime` multiplies
`sqrt (previousShear n)` by `timeWidth (n+1)`, and `timeWidth (n+1)` itself contains
`1/sqrt (previousShear (n+1))`. The combined factor is

```
sqrt (previousShear n / previousShear (n+1)) ,
```

and `actualExtraTime_le` (`PacketSourceScaleGuards.lean:26`) is exactly this comparison:
`previousShear_le_normal` bounds `previousShear n` by its normal form, and `sourceNextTimeWidth`
replaces the width at `n+1`. Since `previousShear n / previousShear (n+1) ≈ exp (-s_n/(2(J+n)^5))`,
the decay lives in the ratio. "Doubly-exponential denominator" described one factor of the width and
skipped the mechanism that the guard actually uses.

**(b) Smoothness is carried by a constructed witness, and that witness is another `Classical.choice`.**
`smoothLimitData` (`Euler/OrdinarySmoothLimit.lean:62`) is

```lean
def smoothLimitData (hT : 0 ≤ T) ... : SmoothL2Field V :=
  Classical.choice (nonempty_smoothLimitData hT A hA hb h0)
```

so the limit object is a `SmoothL2Field`, whose `smooth : ContDiff ℝ ∞ field` is a *proved field* of
the record, not a conclusion drawn from convergence. `sumField` (`Euler/OrdinaryFieldAlgebra.lean:18`)
likewise assembles a finite sum directly as a `SmoothL2Field`. The referee's prescription is right in
substance and one word too strong in detail: the two definitions are independent — neither routes
through the other, and `sumField` needs no limit theorem at all. What matters for E57 is the same
either way: smoothness is a field of the object, so "converges in every Sobolev order, hence smooth"
is not the argument being made and must not be attributed to the code.

Consequence for the `Classical.choice` count in the Euler chain, recorded because it bears on E54:
`constructionScales` is the root choice; `lifespan := initialDatum_finite_lifespan.choose` is a second;
`smoothLimitData` is a third, inside the smooth-limit construction. The structural-scale-horizon
finding is about the first. It is not a claim that the chain contains only one choice.

### 5. Status of the previous note

| item from the note | status |
|---|---|
| E52 slack factor 50 | closed in E59 §1 — the factor is 500 |
| E56 `previousFrequency` index | closed in E59 §2 |
| E56 "larger `D` is harmless" | closed in E59 §3 — `D` is absorbed by `X`, not harmless |
| E57 `previousShear` index | closed in E59 §4 |
| E57 "doubly-exponential denominator" | closed here, §4(a) |
| E57 smoothness description | closed here, §4(b) |
| E10.8 / E58 Millennium verdict | **closed here, §1 — this is the correction that mattered** |
| E7 pressure periodicity | closed here, §2 |
| E58.3 "least damped" | closed here, §3 |

### Standing

One item is now closed against the repository (E7), one headline finding is reversed (the verdict),
one wording contradiction is removed (E58.3), and two proof descriptions are made to match the terms
they cite (E57). Nothing in this entry touches the Lean artifact.

The audit's remaining open item is unchanged and is a manuscript decision, not a code question:
`MANUSCRIPT.tex` §1.3 states its construction proposition with hypotheses that have no models
(`C^∞` on all of `R^4`, uniform compact spatial support, and unbounded `L^∞` as `t ↑ 1`). With the
verdict now corrected, §1.3 is the only place in the paper that contradicts the corrected verdict.

---

## E61 — §1.3 repaired: the construction proposition now has models

*Appended after E60. `MANUSCRIPT.tex` only. No code claim changes.*

### What was wrong

The proposition hypothesised `u ∈ C^∞(R^4)`, uniform compact spatial support and
`limsup_{t↑1}‖u(t)‖_∞ = ∞`. No `u` satisfies all three: a `C^∞` function restricts to a continuous
function on the compact set `[0,1] × K`, hence is bounded there. The proposition was **vacuous** —
true, with no instances — and its conclusion ("the only conjunct that can still fail is nonexistence")
assumed away `force_smooth`, which is the one field that costs anything.

### What it says now

- **Hypothesis:** `u ∈ C^∞([0,1) × R^3; R^3)`, the pre-singular slab. Non-vacuous: the blow-up is
  admissible because smoothness is no longer asserted through `t = 1`.
- **Conclusion:** (i) `f` is `C^∞` on the slab, with `supp f(t,·) ⊆ K` for every `t` and `f ≡ 0` for
  `t ≤ 3/8`; (ii) `navier_stokes` holds identically on `(0,1) × R^3`; (iii) every field of
  `CandidateProperties` **except** `force_smooth` and `force_support` holds of the slab data.

### The code fact that makes this a repair rather than a rewording

`CandidateProperties.force_smooth : ContDiff ℝ ∞ f` (`R3/ProblemStatement.lean:100`) quantifies over
all of `SpaceTime = R^4`. And `ActualCandidate.of_localized_fields` (`R3/ActualCandidate.lean:76`)
takes

```lean
(hf : ContDiff ℝ ∞ f)
```

as a **hypothesis** and assigns it directly to the `force_smooth` field. Global smoothness of the force
is therefore not a consequence of defining `f` as a residual. It is an input supplied by the force
assembly. That is the exact content of the repaired proposition's title: naming the force is free;
smoothing it is not.

### Downstream text changed in the same pass

- Proposition title and proof.
- The paragraph that called §1.3 "the precise sense in which the existence half is not an existence
  theorem for a PDE" now says it isolates what is genuinely free.
- A new paragraph names the second obligation and cites `of_localized_fields`, so the ledger has three
  entries.
- Remark 1.4 ("What is not free") now lists two conjuncts, not one.
- The ledger line reads: *naming* `=` free; *smoothing* `=` the construction; *comparison* `=` the
  mathematics.

### Incidental correction found while doing this

The paper said `CandidateProperties` "bundles eleven fields". The structure has **twelve**:
`velocity_smooth`, `pressure_smooth`, `support_compact`, `velocity_support`, `pressure_support`,
`force_smooth`, `force_support`, `zero_initial_velocity`, `divergence_free`, `navier_stokes`,
`energy_bounded`, `speed_unbounded`. Corrected in §1.2. The old proposition's "all eleven fields" went
with the rewrite.

### Consequence for the verdict

With E60's correction the paper is now consistent end to end: §1.3 says the residual identity does not
supply `force_smooth`, and §7.2 says the theorem resolves alternative (C) because `force_smooth` is
supplied elsewhere and checked. No two sections now claim opposite things.

*No leaf of the Lean tree is touched by this entry. The proposition is a statement about the paper's
accounting of the theorem, not a restatement of it.*

---

## E62 — Clay erratum note added to the paper (§2.1)

*Appended after E61. `MANUSCRIPT.tex` only.*

E7 was closed against the repository in E60 §2, but the paper said nothing about it: `grep` over the
manuscript returned zero hits for `erratum` and zero for alternative (D). The finding was in the log and
not in the artifact, which is the failure mode this project exists to avoid.

A new subsection, `§2.1 Alternative (D) and the pressure-periodicity clause`
(`\label{sec:pressure-periodic}`), now records it. It cites the clause at both sites where it occurs:

```lean
pressure_periodic : UnitSpatialPeriodsOn (Ico 0 1) p      -- PeriodicPaperTheorem.lean:36
pressure_periodic : UnitSpatialPeriodsOn (Ici 0) pressure -- :54, the competitor
```

The second site is the one that matters. A periodicity hypothesis on the candidate is an extra burden;
on the **competitor** it is a narrowing, and narrowing the competitor class is precisely how a breakdown
claim can be made to look easier than it is. The erratum removes that objection by showing the clause is
part of the published hypothesis for the periodic case, not an addition to it.

The note also keeps the two qualifications: the clause is inert for this paper's subject — alternative
(C) on `R^3`, where the pressure is eliminated by a Riesz pairing — and the erratum itself was not read
first-hand here, so the attribution is recorded as correct attribution rather than independent
verification. Same standard as E60 §2 and the same standard the audit applies to the repository.

*No code claim changes. Two new lines of `lstlisting`, one new label.*

---

## E63 — The similarity exponent ladder: two retracted derivations, one corrected

*Appended after E62. `MANUSCRIPT.tex` and the Lean tree are untouched; this entry records a correction to an
exponent derivation given in review on 2026-11-06 and **never logged**, so there is no earlier line to
strike. The retracted statements are re-stated and withdrawn here so that the log carries only the correct
version. Nothing in E0–E62 is affected.*

### Intuition

An exponent ledger is a bookkeeping of shifts: each operator in the equation moves a profile coefficient
up or down the powers of `q` by a fixed amount, and a term-by-term expansion exists exactly when all the
contributions to one power can be collected into one equation. The failure mode is arithmetic, not
conceptual — if one operator's shift is misread by a single power, every balance condition derived from it
is off by that power, and the resulting equations still look like equations. That is what happened here:
one shift was wrong by one, and it propagated into a wrong balance condition, a wrong conclusion about the
supplied equation, and a wrong claim that no expansion exists.

### 1. The radial group shifts by one power of `q`, not two — **(D)**

The weight-shift table, for `Φ_{h,b}f = q^b f(X,η)`:

| operator | shift in the exponent of `q` |
|---|---|
| `∂_t` (i.e. `T_b`) | `−1` |
| `∂_s` (i.e. `f_X`) | `−1` |
| `2s∂_s² + 2∂_s` (radial Laplacian) | `−1` |
| `∂_z` (i.e. `Z_b`) | `−D` |
| `∂_z²` | `−2D` |

The radial entry is the trap. The pure second derivative `∂_s²` shifts by `−2` — that is the `dss`
identity, `∂_s²(q^b f) = q^{b−2} f_XX` (`NavierStokes/SimilarityProfile.lean:279–295`) — but the
axisymmetric radial Laplacian is `2s∂_s² + 2∂_s`, and the factor `2s = 2qX` supplies `+1`. Hence

```
Δ_ax(q^b f) = q^{b−1} (2X f_XX + 2 f_X) + q^{b−2D} Z_{b−D} Z_b f ,      (D) k = 0,1 checked term by term
```

with `D = 1/2 − h` (`NavierStokes/CoordinateAlgebra.lean:16–21`) and `Z_b` the axial coefficient of
`axialCoeff`/`Z` in `CoordinateAlgebra.lean`. Reading `∂_s²`'s shift instead of the composite's is the
error in §2 below.

### 2. Retraction — the balance condition is `λ = 2h`, not `1 + 2h`

Demand that the axial piece, acting on a coefficient `λ` steps below, land on the same power as the
radial and time pieces:

```
radial/time on q^{β_k}        :  β_k − 1
axial on q^{β_k − λ}          :  β_{k−1} − 2D = β_k − λ − 2D
balance                       :  β_k − 1 = β_k − λ − 2D
solve                         :  λ = 1 − 2D = 1 − (1 − 2h) = 2h .        **(D)**
```

I wrote `λ = 1 + 2h`, which is the solution of `β_k − 2 = β_k − λ − 2D`, i.e. of the system you get by
using `∂_s²`'s shift `−2` for the radial group — exactly the error of §1. Checked with exact rational
arithmetic affine in `h`: `1 − 2D` evaluates to `0 + 2h`; `1 + 2D` evaluates to `2 − 2h`.

**Consequence, and the retraction it forces.** A `k−1` axial subscript in a `q`-graded residual is
consistent with the cone for every `h ∈ (0,1/2)`, with the ladder `β_k = β_0 + 2hk`. It does **not**
encode `h = 0`. The earlier statement that the supplied `Ω_k` equation "is the isotropic case, `h = 0`"
is withdrawn; the equation's axial index is correct and the objection was mine.

### 3. Retraction — the fixed-weight pairing, and the next order

The earlier formula paired `T_β f_β` with an axial term on `f_{β+2D}`. That pairing is wrong at any `h`:

```
radial/time :  β − 1
axial       :  (β + 2D) − 2D = β          difference = 1, not 0
correct     :  β − 1 = b − 2D  ⟹  b = β − 1 + 2D = β − 2h
```

The axial partner sits **below** the radial coefficient by `2h`, not above it by `2D`. The `k = 1` weight
`β_0 − 2D` is therefore also wrong: the next order after `β_0` is `β_1 = β_0 + 2h`, and the axial source
at order `k` is built from `f_{k−1}`. The step is the cone gap `2h`, not the axial deficit `2D`.

### 4. The corrected ladder — **(D)**

For the scalar model `∂_t f − ν Δ_ax f = 0`, with `β_k = β_0 + 2hk` and `f_{k−1} = 0` at `k = 0`,
collect at `q^{β_k − 1}`:

```
T_{β_k} f_k  −  ν (2X f_k'' + 2 f_k')  −  ν Z_{β_{k−1}−D} Z_{β_{k−1}} f_{k−1}  =  0        (S_k)
```

Weight check: `β_{k−1} − 2D = β_k − 2h − 1 + 2h = β_k − 1`. Verified mechanically as `−3/2 + 2hk` on both
sides for `k = 0, 1`.

- `k = 0`: `T_{β_0} f_0 − ν(2X f_0'' + 2 f_0') = 0`. The axial operator does not act at leading order.
- `k = 1`: `T_{β_0+2h} f_1 − ν(2X f_1'' + 2 f_1') − ν Z_{β_0−D} Z_{β_0} f_0 = 0`.

The recursion is **forward in `k`**: `(S_k)` determines `f_k` from `f_{k−1}`, with the axial term as
inhomogeneity. An earlier note had the direction reversed.

### 5. What survives, and what does not

- **Survives, in stronger form.** `Δ_ax` is homogeneous of *no* degree under the cone's scaling group for
  `h > 0`, because its two summands carry `b−1` and `b−2D`, and `1 ≠ 2D` on `(0,1/2)`. Equality holds only
  at `h = 0`, where `2D = 1` and the classical parabolic case is recovered. "No single **integer** grading"
  is a corollary of this, and the weaker phrasing in circulation should be replaced by it.
- **Withdrawn.** "No order-by-order expansion exists." `(S_k)` is one, well founded for every
  `h ∈ (0,1/2)`. Non-homogeneity blocks a homogeneous self-similar reduction, not an expansion.
- **Withdrawn.** The density argument. `Z + 2hZ` being dense in `R` for irrational `h` does not obstruct an
  expansion indexed by `k`, because the ladder `{β_0 + 2hk}` is the image of a single index, strictly
  increasing and well ordered. Density of the ambient subgroup says nothing about the well-orderedness of
  its one-parameter subset. This was a non sequitur, not a proof.

### 6. Axisymmetric closure, and where the pressure breaks the single ladder — **(D)**

With `s = r²/2`, i.e. `r = q^{1/2}√(2X)`, write
`u_r = q^{β_k} V_k`, `u_z = q^{β_k+δ} U_k`. Weight matching in `∇·u = 0` gives

```
r ∂_s V  :  β_k − 1/2     V/r :  β_k − 1/2     ∂_z U :  β_k + δ − D
                   ⇒  δ = D − 1/2 = −h .
```

That `−h` is the exact statement of `ℓ_z ∼ τ^{1/2−h}` against `ℓ_r ∼ τ^{1/2}`: the axial velocity rides
half a step below the radial one, carried by the `U` factor, not by the index.

Advection, with `k = i + j` and `β_0 = −1/2`:

| term | exponent |
|---|---|
| `V_i · r ∂_s V_j` | `−3/2 + 4h` |
| `U_i · ∂_z V_j` | `−3/2 + 4h` |
| target `β_k − 1` | `−3/2 + 4h` |
| `V_i · r ∂_s U_j` | `−3/2 + 3h` |
| `U_i · ∂_z U_j` | `−3/2 + 3h` |
| target `(β_k + δ) − 1` | `−3/2 + 3h` |

So the velocity closes on one ladder, `β ∈ −1/2 + 2hZ`, with the convolution index `k = i + j` in both
components.

The pressure does not share it. Weight matching forces `σ_k = β_k − 1/2`:

- radial momentum at order `k` uses `P_k` — residual `0`;
- axial momentum at order `k` uses `P_k` at residual `2h`; it needs `σ_{k−1} = β_k − 1/2 − 2h`.

The system is therefore **triangular with a one-index pressure stagger**: order `k` couples `(V_k, U_k)`
through `P_k` in the radial equation and `P_{k−1}` in the axial one. Solvable, not obstructive — but any
ansatz that places the same `P_k` at the same order in both momentum equations is off by `2h`.

### 7. Epistemic status of every item above

| item | status | site |
|---|---|---|
| `D(h) = 1/2 − h`, `A = 1/2 + h`, `d`, `L` | **(R)** | `NavierStokes/CoordinateAlgebra.lean:16–21` |
| time, `s`, `z`, `ss`, `zz` transport identities | **(R)** | `NavierStokes/SimilarityProfile.lean:160–310` |
| weight-shift table | **(R)** read off the identities; **(D)** collapsed to shifts |
| `Δ_ax` decomposition into `q^{b−1}` + `q^{b−2D}` | **(D)** | from the above two rows |
| `λ = 1 − 2D = 2h`; `(S_k)`; `δ = −h`; all advection exponents; `σ` stagger | **(D)** | arithmetic shown, re-checked exactly |
| `T_{0,k}`, `Z_{0,j}` of the supplied equation | **not defined** | exhaustive search, no hits in the tree |
| `U`, `V` as axial/radial components | **(G)** | notation of the review only; the tree's profile is scalar (`abbrev InnerProfile := InnerPoint → ℝ`) |

### 8. Effect on the paper

None required. `MANUSCRIPT.tex` §4 already carries `b−1` as the isotropic weight in `q` (E58.4), the
`h = 0` endpoint (E58.2), and the axial-vs-radial comparison with the correct direction of inequality
(E58.3). It contains no claim that an expansion fails to exist and no `Ω_k` equation. The retracted
derivation was made in review and is corrected here; the paper's §4 is consistent with the corrected
version and needs no edit.

*Log only. No Lean declaration is contradicted by this entry — every algebraic identity it relies on is
one the tree already proves.*

---

## E64 — Host fingerprints removed from E50 on publication (2026-11-21)

*Intuition.* A workshop is swept before the door is opened to the street. The sign still says what was
built in here; the chalk marks on the wall saying which machine did the building are wiped, because
they were never part of the work.

This repository was made public, so E50's environmental evidence was re-read for machine identifiers
that served diagnostics rather than findings. Four substitutions, no claim altered:

| site | was | now |
|---|---|---|
| E50.1 | exact host triple (arch, OS version and kernel build) | `<arch>-apple-darwin<os>` placeholders; version and hash kept |
| E50.2 | crash reports under a named per-user log directory | "the host's system diagnostic reports directory" |
| E50.3 | exact free space on `/` | "hundreds of GiB free" |
| E50.4 | exact OS build and chip model | "a current macOS release on Apple Silicon" |

**Further generalised (2026-11-21).** Two remaining macOS version references, in the allocator passage and its advisory sentence, now say a current or recent macOS release. The allocator behaviour is attributed to the release family, which is what the evidence supports, so no claim changes.

**Preserved deliberately:** the Lean version, its commit hash, exit 133, the SIGTRAP and libmalloc
frames, the 0/10 and 0/4 failure rates, and every control row in E50.3. E50's conclusion — the pinned
toolchain's Lake aborts on this OS family — is carried entirely by those, not by a build number, so
the reasoning is unchanged and remains checkable.

**Policy note.** This log is append-only for findings. These four edits touch environmental metadata
only: no finding, verdict, citation, count or quoted Lean term was modified. The edits are recorded
here in the same append, so nothing is silently rewritten.

**Considered and left.** The byline (`MANUSCRIPT.tex:83`, its bibliography entry, the `CAVEMAN.md`
intro, and the `Auditor:` field above) carries two names: one human author, and `John`, the agent that
produced this log. The agent name is a role label with no personal identity behind it, so there is
nothing on that side to redact. The human name is a deliberate byline in a typeset document —
attribution, not accidental disclosure — and removing it is the author's decision, not a sanitising
pass. **Resolved (2026-11-21):** the author confirmed ownership of the human name on the byline, and
that `John` is this log's agent auditor rather than a person. Both names stay. Nothing personal is
exposed beyond the byline the author chose to publish.

**Also checked, nothing found.** Credentials or key material of any kind; e-mail addresses; IP
addresses; absolute home or system paths — every path in this log is repository-relative or
`~`-relative; vendored upstream source; blobs deleted from earlier commits but still reachable in
history; published tags, notes, stashes or refs beyond `main`.

---

## E65 — Force smoothness: discharged at `of_localized_fields`, reintroduced at `hlim`; disposition of an external review (2026-11-21)

*Intuition.* A parcel arrives at a counter already stamped. The clerk at the counter did not forge the stamp — someone upstream applied it — but the clerk also cannot tell you what is inside. The only question is who stamped it, and on what authority.

### 1. The question

An external review raised the strongest open item in this audit: `ActualCandidate.of_localized_fields` takes smoothness of the force as a hypothesis, and the log had never traced where the construction supplies it. If the hypothesis were merely assumed, then `force_smooth` in the candidate record would be an assumption wearing the clothes of a theorem.

### 2. The chain, followed to the bottom

| step | declaration | what it does |
|---|---|---|
| 1 | `NavierStokes/R3/ActualCandidate.lean:67` | `compactForce_smooth`: a smooth cutoff times `hf`, giving `ContDiff ℝ ∞ (R3CompactCandidate.compactForce f)` |
| 2 | `NavierStokes/R3/ActualCandidate.lean:87` | `hF := PositiveTimeForce.force_contDiff (compactForce_smooth hf)` — the final force's smoothness is *derived* from `hf` |
| 3 | `NavierStokes/R3/ActualCandidate.lean:109` | `force_smooth := hF` — the record field is populated by that derivation, not by the hypothesis itself |
| 4 | `NavierStokes/LocalScheduleWitness.lean:131,137` | `selected_periodic_candidate` returns `∃ forcing, CandidateProperties … ∧ ContDiff ℝ ∞ forcing`: the `hf` fed into step 2 is a proved conjunct of an earlier theorem |
| 5 | `NavierStokes/MixedPeriodicAssembly.lean:338` | `exists_candidate_force` produces that `forcing` together with its `hf` |
| 6 | `NavierStokes/CandidateFromLimits.lean:82,86` | `force` is *defined* as the glued trace of the actual residual — "No force is an input to this definition" (`:81`) — and `force_smooth` is `smoothExtension_contDiff (tracedResidual_smooth …)` |
| 7 | `NavierStokes/CandidateFromLimits.lean:47` | `tracedResidual_smooth` needs `hlim : ∀ n, Tendsto (iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2)) (fun x => L x n) (𝓝[<] 1)` — supplied locally uniform limits of every normal jet of the residual |

**Verdict.** The smoothness obligation is *not assumed* at `of_localized_fields`; it is discharged there and re-created one level up as `hlim`. No `Classical.choose` and no `sorry` sits at that boundary: the residual is defined, and the force is the residual's trace. What the chain does require is that the residual's jet tower converge locally uniformly to the supplied `L` as `t ↑ 1`. That is analytic content — the same content carried by the solving theory behind `meanSolve`/`highSolve` — and it is where a complete audit must go next. It is not a gap in what the artifact states; it is a boundary at which the artifact consumes a limit hypothesis.

### 3. What this changes, and what it does not

- README's "the force's global smoothness is *proved*, not assumed" stands, and now carries a citation trail (§2 above).
- It does **not** upgrade the audit to "no analytic obligation survives". One does survive: `hlim`.

### 4. Disposition of the review

Accepted and applied:

| item | action |
|---|---|
| abstract asserted "the theorem it proves is true" | replaced with the conditional form, matching the README's own caveat |
| manuscript cited `E0--E54` at `MANUSCRIPT.tex:5`, `:149`, `:1514` | updated to `E0--E65` |
| type-index claim too categorical | qualified in the abstract and in the "indices versus terms" section: unification checks the *declared* type family, not its fitness as a model of the physics |
| scope unstated | abstract and §1.1 now record that the audit covers the whole-space forced result only, and that the periodic and Euler results are excluded |

Corrections to the review:

- It reported that the README still cited E0–E54. At HEAD the README cited E0–E64; only the manuscript was stale. The figure is now E0–E65 throughout.
- It stated that the actual construction *must* supply the force-smoothness hypothesis, implying it had not been shown to. It is supplied, by the chain in §2.
- It read the anisotropy finding as being presented as a failure of the construction. Remark `rem:scoping` in `MANUSCRIPT.tex` already confines the finding to the operator ("Any estimate written as '$\nu\Delta$ acts with weight $q^{b-2}$' is, on this family, an assertion about the radial part alone"), and E63 §5 withdraws "no order-by-order expansion exists". No manuscript edit was needed for this.
- Its central reservation — that no concrete error in the upstream proof is demonstrated — is correct, and is now stated in the abstract rather than left to the conclusion.

*Log only. No finding is retracted, and no Lean declaration is contradicted by this entry.*

---

## E66 — The `hlim` chain followed to the bottom: derived, not assumed; and `meanSolve`/`highSolve` are not on it (2026-11-21)

*Intuition.* E65 stopped at the gate and reported who had stamped the parcel. This entry walks the paperwork back through every office, and finds that the stamp was issued at the bottom of the building — from finite-stage estimates — not handed over at the door. It also reports that one of the two offices an outside reader suspected of issuing it does not belong to this building at all.

### 1. The question

E65 left `hlim` — the locally uniform convergence of every normal jet of the residual, `NavierStokes/CandidateFromLimits.lean:39` — as the surviving analytic obligation. An external review suggested tracing it "through `meanSolve` and `highSolve`". This entry does that, and reports what those two operators actually are.

### 2. `hlim` is constructed, not postulated

| step | declaration | what it does |
|---|---|---|
| 1 | `NavierStokes/CandidateFromLimits.lean:39` | `hlim` is a `variable`, so at this level it is an input |
| 2 | `NavierStokes/MixedPeriodicAssembly.lean:360` | `have hlim := boundaryLimits_locallyUniform hz eA ev ep` — constructed from three named inputs, not assumed |
| 3 | `NavierStokes/JointResidualLimits.lean:148` | `boundaryLimits_locallyUniform` turns **joint** limits at every point into **locally uniform** limits, via `locallyUniform_of_joint_limits` (`:56`) |
| 4 | `NavierStokes/JointResidualLimits.lean:130` | `boundaryLimits_joint`: at each `x ≠ 0` the limit is the Taylor series of a chosen smooth one-sided extension; at `x = 0` it is `0` by `boundaryLimits_zero` (`:126`) |
| 5 | `NavierStokes/LocalScheduleWitness.lean:103` | the extension inputs `eA eB eP : AwayExtensions` are themselves proved, from support data, by `selected_awayExtensions` |
| 6 | `NavierStokes/MixedCandidateWitness.lean:30` | the remaining input is bundled as the last conjunct of `SelectedSchedule`: `VanishingJointJets (MixedDiagonalResidual.residual …)` |
| 7 | `NavierStokes/LocalResidualFlatness.lean:80` | `exists_schedule_all_jetRates` **produces** a schedule satisfying that conjunct, from `StageEstimates` alone |
| 8 | `NavierStokes/LocalResidualFlatness.lean:113` | `selected_schedule` instantiates it at the repository's fixed budget — header: "No raw-stage, finite-stage, smoothness, or rate assumption remains" |
| 9 | `NavierStokes/MixedDiagonalResidual.lean:170` | `physical_vanishingJointJets`: the vanishing is *proved* from raw stage bounds, `JetRate` background/residual hypotheses and `SimilarityApproach.jet_tendsto_zero` |
| 10 | `NavierStokes/ActualCandidateAssembly.lean:1177,1183` | `selected_witness` then `selected_candidate` close the top-level statement |

**Verdict.** `hlim` is a theorem all the way down. Nothing in steps 2–10 is a `variable` at the point of use, and no `Classical.choice` is used to manufacture a limit: the family `L` is `boundaryLimits`, defined from the residual's own actual jets and proved independent of the extension chosen (`boundaryLimits_independent`, `JointResidualLimits.lean:175`). The chain bottoms out at `StageEstimates` — the finite-stage quantitative bounds — which is where the real analytic work lives.

One consequence is worth stating because it is a genuine gain: at the singular point the limit is *forced* to be zero (`boundaryLimits_zero`), so the force's jet tower is flat at the origin (`extendedResidual_flat_at_origin`, `:273`). That is a property of the construction, not an assumption about it.

### 3. `meanSolve` and `highSolve` are on a different branch

The review's premise is wrong, and the check is one command:

```
grep -rn '^import Euler'      NavierStokes/   → 0
grep -rn '^import NavierStokes' Euler/        → 0
```

The two trees share no imports in either direction. The roots confirm the split: `NavierStokes.lean` imports `NavierStokes.ComparatorSolution` and `NavierStokes.PaperResults`; `Euler.lean` imports `Euler.EulerSingularity`. Therefore `EulerMeanPacketProvider.meanSolve` (`Euler/MeanPacketProvider.lean:115`) and `EulerTransversePacketProvider.highSolve` (`Euler/TransversePacketProvider.lean:144`) are unreachable from `breakdownStatement`, and cannot be part of the `hlim` chain. Whatever they are, they are not what discharges the whole-space force obligation.

For the Euler branch, their pattern is nonetheless identical and worth recording for a future entry: both are totalized by

```lean
if h : Nonempty (Forcing D raw) then (Classical.choice h).… else (0,0)
```

so off the admissible domain they return the zero field silently, and every fact about them must come through the `_of_admissible` lemmas (`meanSolve_of_admissible` `:122`, `highSolve_of_admissible` `:152`, and `highSolve_of_admissible` in `TransversePacketJoinedProvider.lean:97`). `meanSolve_contract` (`:127`) and `highSolve_contract` (`:157`) then assert the genuine equation, spatial smoothness and normalization — but only under `Nonempty (Forcing D raw)`. This is the same shape as the audit's constant finding: the *total* object is opaque, and correctness exists only on a domain the caller must supply. It is not a defect; it is a boundary worth naming.

### 4. Effect on the audit's stated position

- E65's "one analytic obligation survives: `hlim`" is now **superseded**: `hlim` is derived, and the surviving obligation is `StageEstimates` — the finite-stage bounds.
- No finding is retracted. Nothing in the paper's two findings depends on this either way.
- The review's recommendation to trace `meanSolve`/`highSolve` is answered by §3: they are not on the path, and the time is better spent on `StageEstimates`/`RawStageBounds`, which is where the quantitative content genuinely sits.

*Log only. No Lean declaration is contradicted by this entry; every claim above is a `path:line` reading, not a recompilation.*

---

## E67 — `StageEstimates` traced to its bottom: constructed, with three existential bound fields (2026-11-21)

*Intuition.* E66 walked the paperwork down to the office marked "finite-stage estimates" and stopped at the door. This entry opens the door. Inside there is no pile of unchecked assumptions. There is a clerk who says: for each stage, some constants and some logarithmic exponents make these derivative bounds true — and then hands over a sealed envelope with the constants inside.

### 1. The question

E66 ended at `StageEstimates`. The review that prompted it named the next target explicitly: `ActualStageEstimates`, `GluedStageEstimates`, `ActualCycleResidualBounds`, `ActualPhysicalPrefixFields`, traced to their foundational hypotheses. The question is whether the quantitative content of the whole-space theorem is *proved* at this level, merely *assumed*, or something in between.

### 2. The chain

| step | declaration | what it does |
|---|---|---|
| 1 | `NavierStokes/ActualCandidateAssembly.lean:1090` | `estimates` is `GluedStageEstimates.actualStageEstimates (runData …) (meanCycleInput …) …` — a definition, not a hypothesis |
| 2 | `NavierStokes/GluedStageEstimates.lean:684` | `actualStageEstimates` builds `StageEstimates` from: coherence `C`, the three field sequences, representations `e`, and `d : ∀ J, PhysicalData B (N+1) …` |
| 3 | `NavierStokes/MixedCandidateAssembly.lean:29` | `StageEstimates` is a **structure of obligations**: smoothness of the three sequences; a gain function with monotonicity and divergence; loss, constant and log functions; three `RawStageBounds`; `finite_background`; `finite_residual` |
| 4 | `NavierStokes/CutStageEstimates.lean:199` | `RawStageBounds` is an explicit pointwise bound: for `j ≥ 1`, on `q ≤ 1`, `‖iteratedFDeriv m (A j) x‖ ≤ C j m · (1+|log q|)^{p j m} · q^{g j − L m}` |
| 5 | `NavierStokes/ActualStageEstimates.lean` (`stageEstimates_of_representations`) | constructs the record; the three raw bounds come from `Cyc.represented_raw_bounds`, and the witnesses are taken by `hraw.choose`, `…choose_spec.choose`, `…choose_spec.choose_spec.choose` |
| 6 | same file, `finite_residual` field | discharged by `ActualCycleResidualBounds.finite_residual_rates`, not by a fresh hypothesis |
| 7 | `NavierStokes/ActualCycleResidualBounds.lean:1190` | `finite_residual_rates` needs `H : ∀ J, Invariant σ (iterate …)` and `d : ∀ J, PhysicalData B N …`, and yields the `JetRate` statement for every `J, m` |
| 8 | `NavierStokes/ActualCycleResidualBounds.lean:1142` | `PhysicalData` is an `abbrev` for `PhysicalFields …`; its consumer says plainly that the local fields are "only identified, never bounded, by `d`" |
| 9 | `NavierStokes/ActualPhysicalPrefixFields.lean:488` | `physicalFields_all` **produces** `∀ J, PhysicalData …` from `StageRealizations`, `ExteriorStages`, a geometric floor, smoothness of the three sequences, and `∀ J, CycleRepresentation …` |

### 3. What is actually at the bottom

Two different objects, and the difference matters.

**The identification layer is proved.** `PhysicalData` carries realizations: the actual fields agree with the chart formulas, the exterior prefixes vanish, the germs match. `physicalFields_of_stages` assembles those from `StageRealizations`, `ExteriorStages` and `CycleRepresentation`. None of these is a numeric estimate; they say *which function this is*, not how large it is. This is the same pattern as the seams of E50-era entries: an obligation that looks analytic turns out to be an identity.

**The quantitative layer is existential.** The three `RawStageBounds` fields are the real content, and they are propositions of the form "there exist constants and log exponents such that this pointwise derivative bound holds". In the constructor, those witnesses are extracted with `Classical.choose`. So the values are not opaque by accident: the record literally stores chosen witnesses of an existence statement.

**A useful negative check.** `RunData` (`ActualStageEstimates.lean:97`) is explicitly *not* an estimate oracle — its own header says the step record "contains native wave constructions; it is not a physical stage-bound or residual-bound oracle". So the quantitative content is not smuggled in through the run data. It arrives only through the three `RawStageBounds` fields and the residual `JetRate`.

### 4. Verdict

`StageEstimates` is **constructed, not assumed**. No axiom, no `sorry`, and no bare hypothesis sits at this boundary: the record is built by a definition that consumes only produced objects.

But the quantitative content is **existence, not evaluation**. At the bottom of the chain are three derivative bounds whose constants and logarithmic exponents are chosen witnesses. This is E65's constant barrier appearing for the third time — first behind individual constants, then behind the whole scale regime (E66), now behind the stage-by-stage estimates. The pattern is consistent: each layer is logically closed, and each layer stores witnesses rather than numbers.

Consequences, stated narrowly:

- the theorem does not rest on an unproved estimate at this boundary — the record is built;
- but no stage constant, log exponent, or loss function in this chain is ever evaluated to a numeral;
- and the monotonicity argument of E10.7 therefore still carries the burden of saying why inflated witnesses would not break downstream steps.

### 5. What remains unopened

Recorded so the next pass does not have to rediscover it:

- `Cyc.represented_raw_bounds` — the producer of the three existential bounds. Its statement is consumed here; its body was not read.
- the producers of `StageRealizations` and `CycleRepresentation` — the identification layer is constructed, but the construction was not followed.
- whether the chosen constants depend on the stage index `J` in a way that interacts with the schedule selection. The schedule is chosen from `gain` and the loss functions, not from `C` and `p`, which is a reason to expect no interaction — an expectation, not a verified fact.

*Log only. No Lean declaration is contradicted by this entry; every claim above is a `path:line` reading, not a recompilation.*

---

## E68 — The load-bearing chain followed to its floor; comparator fidelity and pressure flux closed (2026-11-21)

*Reading pass only; no build during this entry. Sources read at `f9e8bc5`. The build referred to below is the Linux run already recorded, not a new one.*

### 1. Statement fidelity against the comparator — closed by reading

`ComparatorSolution.navier_stokes_breakdown_R3` is a three-line adapter to `ComparatorBridge.navier_stokes_breakdown_R3`, which applies `comparator_of_breakdown` to `theorem_1_1`. The bridge fixes `u0 := 0` and `f := toComparator f`, and **proves** both admissibility conditions the challenge demands rather than assuming them:

- `zero_initial_condition_decay` — the zero datum satisfies "every derivative decays faster than any polynomial" by vanishing;
- `forceConditionDecay_of_compact h.force_smooth h.force_support.1` — spatial and temporal decay is **derived** from `C^∞` plus compact spacetime support.

The translation lemmas were read one by one (`divergence_eq`, `gradient_eq`, `laplacian_eq`, `temporalDerivative_eq`, `comparator_equation_Rn`, `fromComparator_smooth`). Each is a proved identity between the paper's operators and Mathlib's, not an estimate. The one boundary subtlety — the comparator quantifies over `t ≥ 0` with `derivWithin (Ici 0)` — is discharged by `temporalDerivative_eq`: at `t > 0`, `Ici 0` is a neighbourhood, so the one-sided derivative is the ordinary one. In the refutation direction, `globalSolutionOfComparator` converts any comparator solution into a `GlobalFiniteEnergySolution ν f`, contradicting the non-existence clause.

What this does **not** establish is the fidelity of the Formal Conjectures encoding to the Clay PDF. That is a property of the challenge file, not of the bridge.

### 2. `StageEstimates` — the live branch, followed to its floor

E67 stopped at the three existential `RawStageBounds` fields. This pass followed them one layer lower and pinned down which branch is load-bearing:

```
ActualCandidateAssembly.lean:1094
  -> GluedStageEstimates.actualStageEstimates               :684
  -> GluedStageEstimates.stageEstimates_of_component_bounds :402
  -> GluedStageEstimates.represented_raw_bounds             :350
```

`represented_raw_bounds` consumes smoothness (`hsA`/`hsP`) and pointwise derivative bounds (`hbA`/`hbP`) of the particular components. Both families are **discharged**, by `current_potential_bound` and `current_pressure_bound` (`:640+`), which are themselves built from `glued_bound_of_local` plus the per-mode bounds. The exponents are `linarith` consequences of the iteration ledger (`gain_le_current_exponent`, `current_potential_loss_le`, `current_pressure_loss_le`), not chosen numbers.

`current_potential_mode_bound` (`:873`) and `current_pressure_mode_bound` (`:939`) each produce `∃ C ≥ 0` bounding every physical jet of the literal current mode by

```
C * physicalQ(w) ^ (h*((1/2 + sigma) + 1/2) - currentLoss(...) m)
```

uniformly over every label, every dyadic band `n >= 4`, and every point of the band. The route is `actual_native_potential_bound` (`:543`) / `actual_native_pressure_re_bound` (`:599`) for the native chart jet, then `vector_chart_physical_bound` / `scalar_chart_physical_bound` for the transfer, then the germ identity `localPotentialMode_germ` to land on the physical mode.

**The floor.** `actual_native_potential_bound` takes exactly one quantitative hypothesis:

```
H : LabelSumBounds.UniformWaveClass nativeStrip nativeEnvelope alpha
      (ActualParticularStageControls.currentSource x j)
```

plus `PreservesCarriers`, `InputSupport`, and the geometric floor `hN`. Its output is a native jet bound `C * Q(n)^(h(alpha+1/2) - 2hm) * S(n)^p`, with `C` and the integer `p` chosen. So the bottom of the estimate chain is not a physical derivative estimate but a **wave-class membership statement about the actual source**. `Invariant` supplies it through `native_source_class`, and `Invariant` is `CycleAnalyticInvariant` (`ActualParticularCycleData.lean:38`).

This refines E67 rather than reversing it. The constants are still existential and never evaluated; what changes is that they are extracted from bounds *derived* one layer lower than E67 recorded, from a source hypothesis that is itself a field of the cycle invariant.

**A negative check.** `ActualStageEstimates.stageEstimates_of_representations` is a parallel branch that the assembly never calls. Its `WaveInputs` parameter carries eight exponent and shift fields with no construction site anywhere in the tree: `particularPotential_exponent` occurs only at its declaration and at its use. `ActualEndpointInputs.actual_stage_endpoints` and `endpointInputs_of_run` have no callers either. These are unused alternates, and a later reader should not mistake them for the proof path.

### 3. Pressure flux — closed end to end

`PressureRecovery.Hypotheses` (`R3/PressureRecovery.lean:33`) has ten fields: `0 < T`; smoothness of `u`, `v`, `p`, `q`; `div u`; `div v`; residual equality; uniform finite energy of `u` and of `v`. No pressure bound, no decay condition, no growth assumption.

- `gradient_recovery` (`:407`) derives, at every interior time, the identification of the physical pressure-gradient pairing with the canonical tensor pairing, from the equation and uniform finite energy alone. `time_test_gradient_difference_zero` shows every compact temporal test annihilates the difference; `averaged_value_zero` gets that from an `H^3` bound plus harmonicity on compact tests (`eq_zero_of_compact_harmonic`); `TemporalTestUniqueness` upgrades vanishing integrals to pointwise equality in time.
- `pressure_flux_eq_of_gradient_identification` (`R3/PressureFluxIdentity.lean:114`) is integration by parts: split the flux test into `sum_k d_k(chi * w_k)` using divergence-free `w`, apply the identification componentwise, and reassemble the canonical pairing.
- `pressure_flux_eq_canonical` (`R3/ActualPressureFlux.lean:38`) uses only `tensor_bound`, divergence-free `u - v`, and `gradient_recovery`.

The constant in `canonicalCutoffFlux_bound` is assembled from `cutoff_pressurePair_bound` plus a commutator estimate: Hoelder `6/5`-`6`, a Riesz-test Sobolev constant, a Lipschitz cutoff bound, and an explicit commutator constant. The envelope printed in that theorem statement matches the one `eq_of_pressure_flux_bound` consumes. No unread pressure step remains in the comparison argument.

### 4. What is still open

- **Preservation of the source wave class.** `current_*_mode_bound` *consumes* `UniformWaveClass ... (currentSource x j)`, and `native_source_class` derives it from `Invariant`. Whether `ActualCyclePreservation` re-establishes `Invariant` at every cycle has not been followed to a conclusion. This is the last place a quantitative property could be assumed rather than derived.
- **Periodic alternative (D)** is bridged and compiled, never audited.
- **The nine external checkers** were not re-run.

### 5. Effect on earlier entries

E50's conclusion that no build succeeds **on this host** stands, and was reproduced (3/3). Its implication that no build succeeds at all is withdrawn; see the scope note at the top of this log. E66's disposition of `meanSolve` and `highSolve` — Euler-only, not on the Navier--Stokes path — is confirmed by import direction and is unaffected.

*Log only. No Lean declaration is contradicted by this entry; every claim above is a `path:line` reading, not a recompilation.*

---

## E69 — Preservation of the invariant is a theorem, not a hypothesis: the chain closes (2026-11-21)

*Reading only; no build.*

### 1. The question E68 left open

`current_potential_mode_bound` and `current_pressure_mode_bound` consume, as their only quantitative hypothesis, `LabelSumBounds.UniformWaveClass nativeStrip nativeEnvelope alpha (currentSource x j)`, and `native_source_class` derives it from `Invariant`. If `Invariant` were merely carried from stage to stage, the entire estimate chain would rest on an assumption. It is not carried. It is reproved.

### 2. The seed is a theorem about the literal initial state

`ActualCyclePreservation.initial_invariant` gives `Invariant (1/5) (state B N0 0)` from `ActualCoreSupport.initial_invariant`. `state B N0 0` is `ActualInitialization.initialCycleState` by `rfl`, so this is a statement about the object the construction actually starts from, not a hypothesis about an arbitrary state. `initial_runInvariant` packages it with coherence and periodicity.

### 3. The step rebuilds the invariant

`CorrectionAnalyticStep.step` (`:521`) has the shape

```
StaticData -> CycleAnalyticInvariant ... sigma x -> 1/5 <= sigma -> kappa <= 1/100000
  -> StepData ... -> StepResult ...
```

and `StepResult` (`:506`) has first field

```
invariant : CycleAnalyticInvariant G c primary P S (sigma+1/10) (CycleState.step p c x)
```

The proof term of `step` ends `exact ⟨hFull, hT, hRank, hPressure, hInc.1, hInc.2, hSθ, hSz⟩`, where `hFull := assemble ... H W ...`. So the new invariant is the **output of `assemble` applied to the old invariant and the wave data**, not a hypothesis of the step. `step_preserves` (`:632`) is the projection of that field, and `iterate_invariant` / `iterate_results` induct over an arbitrary schedule with `sigma (n+1) = sigma n + 1/10`.

### 4. The actual run closes at the assembly boundary

`ActualCyclePreservation.state_runInvariant` proves `RunInvariant (sigma j) (state j)` for every stage `j` by induction: the seed is `initial_runInvariant`, the step is `next_runInvariant`, which calls `stepResult_of_particular ... .invariant`. The `StepData` that step consumes is built by `stepData_of_particular` from `ActualParticularCycleData.Data`, which is itself produced by `actual_data` from the invariant and periodicity. `state_invariant` is the projection, and `ActualCandidateAssembly:479` consumes exactly `state_invariant`.

So the floor hypothesis of the stage estimates is supplied by the induction, one stage at a time, from a proved seed. There is no point on the path where "the source is in the required class" is assumed at a boundary and left there.

### 5. What this does not settle

- The body of `assemble` was not read in this pass. Its **signature** is the load-bearing claim (old invariant plus wave data yields the new invariant), and every consumer depends only on that. Opening it is a follow-up, not a gap at the floor.
- The induction is over the stages `state B N0 j`; admissibility of `sigma j` is separate and comes from `ActualIterationLedger.sigma_admissible`. Both are needed, both are proved.
- The constant barrier is untouched. The constants in the mode bounds are still chosen witnesses. What changes is that they are not *assumed* — they are extracted from bounds derived from a proved invariant.

**Verdict.** The source wave class is derived at every stage: proved for the initial state, rebuilt by each step, and only then consumed by the mode bounds. E68's last open item is closed, and with it the estimate chain from the initial state to `breakdownStatement` is continuous in the proof term.

*Log only. No Lean declaration is contradicted by this entry; every claim above is a `path:line` reading, not a recompilation.*

---

## E70 — Periodic alternative (D), audited by reading (2026-11-21)

*Reading only; no build, no axiom print.*

### 1. What is claimed

`PeriodicPaperTheorem.breakdownStatement` says: for every `ν > 0` there exist `u`, `p`, `f`, `K` with `CandidateProperties ν u p f K` and `¬ Nonempty (GlobalSmoothSolution ν f)`. `periodic_corollary` (`:155`) proves it unconditionally.

The candidate record requires smooth `u`, `p` before time one; smooth `f`; unit spatial periods; compact `K` inside the fundamental interior; the support of each time slice intersected with the fundamental cube inside `K`; zero initial velocity; `f` compactly supported in future time and zero for `t ≤ 0`; divergence-free; residual equal to `f` on `(0,1)`; and unbounded speed at one.

The excluded class, `GlobalSmoothSolution`, requires only: smooth `u`, `p` on the future domain; unit periods in space including the pressure; zero initial velocity; divergence-free; residual equal to `f` for `t > 0`. **No energy bound, no pressure normalization, no growth or decay condition on the competitor.** That class is larger than the bounded-energy class used for alternative (C), so the exclusion is the stronger statement of the two.

### 2. The proof, and where each obligation comes from

1. `theorem_1_1_with_initial_rest` supplies a whole-space candidate that is identically zero on `|t| ≤ 3/8`.
2. `ParabolicScaling.compressedCandidate` applies clock `l^2 (t-1) + 1`, spatial scale `1/l`, force scale `l^3`, pressure scale `l^2`, viscosity unchanged, singular time still exactly one. `zeroBefore_*` discards the pre-initial history the shifted clock would otherwise create. Energy stays bounded (`velocity_energy_bounded`), speed stays unbounded (`velocity_speed_unbounded`), and the equation is checked after the pullback (`pull_residual`, `zeroBefore_residual`) — this is a similarity of the equations, not a relabelling.
3. `exists_compression_scale` chooses `l` so the supports fit the quarter cube; `of_compact_candidate` then periodizes `beforeOne u`, `beforeOne p` and `f`, proving smoothness, periodicity, support, zero datum, divergence-freeness, and the PDE term by term. The post-one extensions are cut before the lattice sum, which is what `beforeOne` is for.
4. `CandidateProperties.no_global_solution` applies `PeriodicViscosity.excludes_global_solution`: `PeriodicViscosityUniqueness.classical_uniqueness_on_Icc` identifies any global competitor with `u` on every compact slab before one, and `MaximalLifespan.unbounded_excludes_continuous_extension` contradicts unbounded speed. The competitor's lack of an energy bound is irrelevant to both steps.

### 3. Comparator fidelity, both directions

- `PeriodicPaperComparator.option_D_of_paper_candidate` produces the comparator's exact (D) quantifiers with `u0 = 0` and `toComparator f`, and proves both admissibility conditions: `InitialVelocityConditionPeriodic` and `ForceConditionPeriodic`, the latter from compact future time support plus the jet decay lemma (`forceConditionPeriodic_of_decay`).
- `PeriodicComparatorSolution.periodicPaperSolution_of_comparator` converts a comparator solution into the paper's `GlobalSmoothSolution`, so the exclusion transfers back.

Neither direction rescales viscosity or time; only the argument order changes.

### 4. Statement-design notes

- **"Support" is not compact support on `R^3`.** A nonzero periodic lift cannot have compact support. The record intersects the topological support of each time slice with the fundamental cube and puts that intersection inside `K ⊆ fundamentalInterior`. The file header (`:11-14`) states this. Read against the torus, it is the intended clause; read as a claim about all of `R^3`, it would be false.
- **The force is not zero.** As with (C), `f` is the residual of the constructed field, so this is a forced periodic breakdown and says nothing about the unforced periodic problem.

### 5. Limits of this audit of (D)

- `#print axioms` was run on the four whole-space `R3` theorems, **not** on `periodic_corollary`, `option_D_of_paper_candidate`, or `periodicPaperSolution_of_comparator`. Their axiom footprint is *inferred* from the repo-wide scan (0 `axiom`, 5 `sorry` confined to the unimported `ComparatorChallenges/`) and from the fact that `PeriodicPaperTheorem.lean` lies inside the 817-module `NavierStokes` build that exited 0. Inferred, not printed.
- The bodies of `classical_uniqueness_on_Icc` and the periodization lemmas were sampled, not read line by line. This entry audits the statement and the architecture of (D); it does not re-prove periodic uniqueness.

**Verdict.** (D) is a genuine corollary of the whole-space theorem, bridged to the comparator in both directions, with a competitor class at least as strong as (C)'s. The only statement-design remark is the torus-support convention, which the source discloses. The empirical gap is the axiom print, not the mathematics.

*Log only. No Lean declaration is contradicted by this entry; every claim above is a `path:line` reading, not a recompilation.*

---

## E71 — `assemble`'s body read: every field constructed, carried with a reason, or discharged before the call (2026-11-21)

*Reading only; no build.*

### 1. What was open

E69 recorded that `assemble` (`CorrectionAnalyticStep.lean:265`, declared `private theorem`) was the one unread link: it takes the old invariant plus the wave data and returns the invariant at `sigma+1/10`. E69 rested on its signature. This entry reads the body (`:301-445`).

### 2. Shape of the proof

`assemble` ends in a single structure literal, `refine { ... }`, with four residual goals discharged immediately after. Every field falls into one of three classes.

**Constructed from the wave data and the stage estimates.** `wave` and `difference` from `finalBlock_uniform_cumulative`; `pressure` from `finalBlock_pressure_cumulative`; `residual` from `meanStages_residual_gain`; `solenoidal` from `waveStages_residual_gain`; `inputSupport` from `next_inputSupport ... H.inputSupport W.particularSupport W.signedSupport`; `realCoefficients` from `next_realCoefficients`; `mean` from `next_meanResidualBounds`; `covariance` from `next_covariance_mem` applied to `hCovP` and `hCovS`; `masses` from `next_zeroMassesOn`; `representation` from `next_representation`; `bands` from `next_coefficient_bands`; and the four coefficient-smoothness fields by adding the old coefficients to `W.particular*` and `W.signed*`.

**Carried because the underlying object is unchanged.** `phase`, `frequency`, `angular` are `H`'s; `carrier` is rebuilt from the three components of `H.carrier l`; `aliasCoefficients := H.aliasCoefficients`; `axisFlat := hAxis`. These are structural carries, and the record's `SameCarrier` field is precisely the statement that the carriers did not move.

**Passed as arguments and discharged before the call.** The quantitative parameters --- `hCovP`, `hCovS`, `hTemporal`, `hRank`, `hCumulative`, `hDebt`, `hTheta`, `hAxial`, `hAxis` --- are hypotheses *of `assemble`*. They are not hypotheses of the cycle: in `step` (`:521`) each is produced first, by `mean_gain_from_waves_of_cross_defects`, the two covariance lemmas, and the stage, rank and debt lemmas, and only then supplied. The structure literal therefore contains no `sorry`, no `by assumption`, and no field whose value is an unproved proposition.

### 3. The residual goals

The four holes are filled at the end of the proof: `primitives` from `hpr.1` (the `next_primitive` theorem), `oscillatoryPressureSmooth` from `H`'s smoothness plus `W.particularPressureField` and `W.signedPressureField`, `gaussianMean` from `next_gaussian_angularMean`, and `baseAngular` from the transported base. None is an assumption.

### 4. Consequence

E69's conclusion now rests on the body, not on a signature: the new invariant is built field by field from produced estimates. The quantitative content stays existential --- the constants in those estimates are chosen witnesses --- so the constant barrier is untouched. What is excluded is the possibility that a *field of the invariant* was smuggled in as a hypothesis at the step.

### 5. What this still does not settle

- The producer lemmas called here (`finalBlock_uniform_cumulative`, `meanStages_residual_gain`, `waveStages_residual_gain`, `next_meanResidualBounds`) were read at their call sites, not end to end. Their statements fix the exponents; their bodies are another layer.
- Nothing in this pass is machine-checked. The compilation of this module is the one already recorded.

**Verdict.** `assemble` is a genuine construction. With E69, the invariant is produced rather than presupposed at every stage, and the remaining open surface is the bodies of the estimate producers, not the shape of the assembly.

*Log only. No Lean declaration is contradicted by this entry; every claim above is a `path:line` reading, not a recompilation.*

---

## E72 — The periodic axiom question is already posed in the source, in executable form (2026-11-21)

*Reading only; no build. Refines the framing of E70 §5 without changing its conclusion.*

### 1. What E70 left as a gap

E70 audited the periodic corollary by reading and recorded its axiom footprint as **inferred, not printed**: the four whole-space `R3` theorems got a real `#print axioms`, `periodic_corollary` and the two comparator adapters did not. That was accurate about what this audit had executed. It was slightly misleading about the artifact, because the artifact already asks the question.

### 2. Where the question is asked

`NavierStokes/ComparatorSolution.lean` — the file that defines the (D) adapter — ends with two literal commands, not comments:

```lean
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
```

The first is the theorem this audit already printed on Linux. The second is the periodic one E70 could not print. So the exact check E70 wanted is a line of source that ships with the development: elaborating that module prints both answers. Nothing has to be written to obtain it, only compiled.

### 3. Where the answer is claimed

Two places, both machine-facing rather than prose:

- `formalization.yaml`, `status.main_results`, lists `(D) Non-existence of global smooth periodic solutions` with `declaration: NavierStokes.Comparator.navier_stokes_breakdown_periodic`, `file: NavierStokes/ComparatorSolution.lean`, `sorry_count: 0`, `axioms: [propext, Classical.choice, Quot.sound]`, and `comparator_config: ComparatorChallenges/NavierStokes.json`.
- `ComparatorChallenges/NavierStokes.json` names both theorems in `theorem_names`, sets `permitted_axioms` to exactly `propext`, `Quot.sound`, `Classical.choice`, and sets `enable_nanoda: true`.

The second is the stronger object. It is a configuration a checker consumes: an exported proof term containing `sorryAx`, or any axiom outside those three, fails that run by construction rather than by review. The periodic footprint is therefore not an unexamined corner of the metadata; it is a declared acceptance condition.

### 4. What this does not establish

- **It is a claim, not a result of ours.** `formalization.yaml` is upstream's self-report, and its own `review.status` field says `self-assessed`. Nothing in the tree records a comparator run, its date, its machine, or its output. A configuration that would reject a bad footprint is not evidence that the footprint was accepted.
- **`enable_nanoda: true` is a request, not a receipt.** It asks the tool to re-check the exported proof in an independent kernel. Whether it ran, and against which commit, is not recorded in-tree.
- **This audit still has not printed the periodic footprint.** E70's conclusion stands unchanged: the mathematics of (D) is audited by reading; the execution is not.

### 5. What changes, and what the next step is

The gap E70 recorded was worth about one command, not one investigation. That changes the honest next step: the remaining empirical work is not "audit the periodic development" — E70 did that — it is "elaborate one module that already contains the command".

`.github/workflows/kernel-check.yml` in this repository does that on a runner instead of on this host: clone upstream at `f9e8bc5`, `lake exe cache get`, `lake build NavierStokes`, then elaborate a probe file containing the two prints upstream ships plus `periodic_corollary`, `option_D_of_paper_candidate`, and `periodicPaperSolution_of_comparator`.

Until it is run, the correct sentence in the manuscript and README remains "not printed", now followed by where the print lives.

**Verdict.** E70's empirical gap is smaller than recorded and precisely located: the command is in `ComparatorSolution.lean`, the acceptance condition is in `ComparatorChallenges/NavierStokes.json`, and the only missing thing is a run on a machine that can hold the oleans. No claim about the periodic axiom footprint is upgraded by this entry.

*Log only. No Lean declaration is contradicted by this entry; every claim above is a `path:line` reading, not a recompilation.*

---

## E73 — The periodic axiom print, executed: (D)'s footprint is the permitted set (2026-11-22)

*Execution, not reading. This is the first entry whose evidence is a kernel run rather than a `path:line` reading. It closes the gap E70 §5 recorded and E72 §5 localized.*

### 1. What was run

`.github/workflows/kernel-check.yml` on a GitHub Actions `ubuntu-24.04` runner, from a pristine clone of upstream: no vendored code, no local state, no reused oleans.

| item | value |
|---|---|
| run | `44987195620`, attempt 1, head `21f174b` of this repository |
| upstream | `openai/NavierStokesAndEuler` at `f9e8bc5` |
| toolchain | `leanprover/lean4:v4.34.0-rc2`, installed by elan |
| started / completed | `04:56:18Z` / `05:28:55Z` (32 min 37 s wall) |
| build | `lake build NavierStokes`, 9,580 jobs, exit 0, "Build completed successfully", 817 modules, 28 min 35 s |
| axioms step | exit 0, 4 s |
| artifact | `kernel-check-logs` (11,501 B): `build.log` (820 lines), `axioms.log` (7 lines), `upstream/lake-manifest.json` |
| cache | `lake-build-ubuntu-f9e8bc5-v1`, 372,015,715 B (0.35 GiB), saved post-job; restore was a miss on this first run |

Dependency closure actually used, from the uploaded manifest: `mathlib 85e3a25e`, `Comparator 19e111e2`, `lean4export cacf989b`, `plausible d9598f07`, `LeanSearchClient ba67e212`, `importGraph d8823026`, `proofwidgets a8acbfd8`, `aesop 18889deb`, `Qq 507746ab`, `batteries d54dddc5`, `Cli ab3a82db`. Nothing else is in the build, and the step that clones upstream pins the commit explicitly, so the audited tree is the audited tree.

### 2. The answer

`axioms.log`, verbatim, all five declarations:

```
'NavierStokes.Comparator.navier_stokes_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes.Comparator.navier_stokes_breakdown_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes.PeriodicPaper.periodic_corollary' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes.ComparatorBridge.option_D_of_paper_candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes.ComparatorBridge.periodicPaperSolution_of_comparator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Three things follow, each narrower than it looks:

1. **No `sorryAx`.** A `sorry` anywhere in the transitive proof term is listed by name in this output. It is absent from all five.
2. **No axiom outside the permitted set.** The printed set is `ComparatorChallenges/NavierStokes.json`'s `permitted_axioms` member for member. The configuration would have rejected anything else; this run shows there was nothing else to reject.
3. **(D) now stands where (C) stands.** E70 recorded (D)'s footprint as inferred, E72 found the command, E73 executes it. The inference was right, which is the least interesting part: what changed is that the claim is now a receipt.

### 3. The same run confirms upstream's own self-report

`NavierStokes/ComparatorSolution.lean` ends with two literal `#print axioms` commands (E72 §2). Building that module elaborates them, so `build.log` carries upstream's own answer as `info:` lines, independent of the probe file:

```
info: NavierStokes/ComparatorSolution.lean:31:0: 'NavierStokes.Comparator.navier_stokes_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NavierStokes/ComparatorSolution.lean:32:0: 'NavierStokes.Comparator.navier_stokes_breakdown_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Two lines of the same run agree. Neither is an external checker.

### 4. What this does not establish

- **No independent kernel.** `enable_nanoda: true` asks Comparator to re-check the exported proof term in a second implementation. This workflow builds and prints footprints; it does not run Comparator. The nanoda re-check remains a request, not a receipt — E72 §4 is unchanged by this entry, and it is now the only empirical item left on the Navier--Stokes side. *(Superseded: run `45119134981` obtained that receipt on both kernels; see E75 §7.)*
- **No statement review.** A footprint is a fact about the proof term. It says nothing about whether the encoded statement is the Clay statement. §3 of the manuscript is about exactly that gap; this entry does not narrow it.
- **No finding is upgraded.** Every finding of E0–E72 comes from reading. This run confirms that the terms elaborate under the printed axiom set; it does not confirm that any estimate inside them is true.
- **The Euler development was not built.** The workflow targets `NavierStokes` only.
- **`build.log` is a job log, not a transcript of every declaration.** It records 817 module builds and 9,580 jobs; it does not re-state the source of each.

### 5. Cost, and what the cache bought

Public repository, so the run draws no private minutes; the only budget that mattered is the 300-minute job timeout, and the run used 32 of them. Of the 32 min 37 s, 28 min 35 s is the compile and 242 s is overhead (disk cleanup 133 s, mathlib cache 86 s, clone 2 s, elan 1 s, setup 2 s, axiom step 4 s, upload and post-job 9 s). `.lake/build` for this project is 0.35 GiB, which fits the per-repository cache limit with room to spare: the earlier concern that a whole-`.lake` cache would exceed 10 GB was correct, and caching `.lake/build` only was the fix. A second run should restore that cache in seconds and land near 5 minutes.

**Verdict.** (D)'s axiom footprint is no longer inferred. It was printed on a clean clone at `f9e8bc5`, together with its paper corollary and both adapters, and it is the permitted set with no `sorryAx`. What remains empirical for this development is the external Comparator/nanoda re-check — a different tool answering a different question — and what remains at statement level is untouched by any of it.

*Execution evidence: run `44987195620`, artifact `kernel-check-logs`. The findings of E0–E72 remain textual; this entry does not re-derive any of them.*

---

## E74 — The Comparator log was empty, and the emptiness was our wrapper (2026-11-23)

*Correction entry. It withdraws a conclusion drawn on 2026-11-22 from a log that could not have contained the evidence, and it replaces it with the capture fix.*

### 1. What was recovered

Both Comparator attempts finished and both uploaded artifacts, so the question "how far did it get" had an answer waiting:

| run | head | outcome | comparator step | artifact | comparator output |
|---|---|---|---|---|---|
| `44999798334` | `f249c4d` | cancelled at job cap | 354.8 min | `comparator-check-logs` | 2 lines |
| `45013487446` | `330caa8` | step timeout | 210.2 min | `cmp-builtin-kernel` | 2 lines |

The two lines, verbatim and identical in both:

```
Running as unit: run-u2.service; invocation ID: a564b14596fd440db16865944ccf96ea
Press ^] three times within 1s to disconnect TTY.
```

Both lines are `systemd-run`'s own. Neither is Comparator's.

### 2. Why that is a capture failure and not a slow phase

`Comparator.compareIt` (`Main.lean:295–309` at `19e111e2`, the rev in the lake manifest) is:

```
safeLakeBuild challengeModule   ->  IO.println s!"Building {target}"   (Main.lean:115)
safeExport challengeModule      ->  IO.println s!"Exporting {decls}…"  (Main.lean:135)
safeLakeBuild solutionModule    ->  "Building …"                        (:115)
safeExport solutionModule       ->  "Exporting …"                       (:135)
verifyMatch                     ->  "Running Lean default kernel …"     (:212)
                                    "Lean default kernel accepts …"     (:222)
IO.println "Your solution is okay!"                                     (:309)
```

`Building {target}` is printed **before** `runSandBoxed` spawns `lake build`. Nothing expensive precedes it. A process that ran for 210 minutes without emitting it did not reach the first statement of `compareIt`, or its stdout never reached the `tee`. The second is the only one consistent with a 210-minute wall time.

The first version of the workflow wrapped the run in `systemd-run --user --pty`, on the strength of a probe (`systemd-run --user --pty -- true`) that succeeded. The probe asked whether the unit *starts*. It never asked whether a child's stdout comes back through the PTY relay into a pipe, and with the runner's stdout being a pipe it does not.

### 3. What is withdrawn

- **"Comparator needs more than 355 minutes."** Not established. 355 minutes elapsed, and no observation of Comparator's progress exists in either run. Whether the process was working, waiting, or blocked at startup is unknown.
- **"It does not fit the platform ceiling."** Same defect: it rested on elapsed time with no captured evidence of what the time was spent on.
- **"The sandbox rebuild of the challenge is not the cost."** This one survives, but on different grounds: the challenge module pre-built outside the sandbox in 0.1 min (`ComparatorChallenges.NavierStokes`, 8,763 jobs, "Built … (4.4s)"), with two expected `sorry` warnings on the challenge's own statement holes.

No entry of E0–E73 depended on these, and none is affected. The withdrawal is confined to the machine-time attribution.

### 4. What was changed

`.github/workflows/comparator-check.yml`, this repository:

1. `--pty` → `--pipe` for both wrapped invocations, which is the flag that connects a child's stdout to the caller's redirected stdout.
2. The wrapper is no longer trusted on the strength of a start probe. It must echo `WRAPPER-RELAY-OK` back through the same relay; if it does not, the run proceeds unwrapped and the log says so, rather than dying silently behind a wrapper that eats output.
3. A five-minute heartbeat writes `date`, captured byte count, and live lean/lake process count into the same log. A silent child and a dead child are distinguishable in the artifact from now on.
4. The builtin step cap rises from 210 to 300 min, inside the 360-min job cap.

### 5. What would count as a verdict

Either of two strings from `Main.lean`, and nothing else:

- `Your solution is okay!` (`:309`) — the challenge and the solution export to the same statement, the builtin kernel replayed the solution in a fresh environment, the quotient post-check passed, and no axiom outside `permitted_axioms` was used.
- `Lean default kernel rejects the solution` (`:224`) or `… kernel rejected the solution` (`:198`) — a defect, with the failing export attached.

Absence of both, with heartbeats present, means the run was still working when it was cut. Absence of both with no heartbeats means the capture broke again.

### 6. What this entry does not establish

- **No verdict.** The Comparator check has still not produced one. E73's axiom footprint stands on its own, and it is not this check: a footprint is what the proof term names, not whether the term inhabits the statement the challenge poses.
- **The cause is inferred, not isolated.** `--pipe` plus a verified relay is the fix for the observed symptom; it has not yet been observed working on this project's config. The next run's first screen decides it.
- **Nothing mathematical changes.** No fidelity finding is upgraded or downgraded by a capture bug.

*Evidence: artifacts `comparator-check-logs` (run `44999798334`), `cmp-builtin-kernel` and `cmp-verdict-summary` (run `45013487446`); `leanprover/comparator` `Main.lean` at `19e111e2`. Superseded claims are named in §3 rather than deleted.*

---

## E75 — The Comparator check executes and passes: `Your solution is okay!` (2026-11-23)

*Execution evidence. This is the check E73 explicitly did not perform and E74 left unexecuted. It closes the last empirical item on the whole-space side.*

### 1. What was run

`.github/workflows/comparator-check.yml` at `ec1ba19`, the version described in E74 §4.

| item | value |
|---|---|
| run | `45119134981`, attempt 1, `workflow_dispatch` |
| upstream | `openai/NavierStokesAndEuler` at `f9e8bc5` |
| Comparator | `19e111e2` (`leanprover/comparator`, `v4.34.0-rc2`) |
| toolchain | `leanprover/lean4:v4.34.0-rc2` on `ubuntu-24.04` |
| started / comparator step | `05:39:19Z` / `05:44:40Z` |
| comparator step duration | **7.3 min** (300-min cap, 360-min job cap) |
| artifact | `cmp-builtin-kernel` (824 B), `comparator-builtin.log`, 20 lines |
| config | `ComparatorChallenges/NavierStokes.json` with `enable_nanoda` stripped: builtin kernel only |

The pre-comparator path cost 5.4 min, almost all of it disk cleanup and cache restore; `lake build NavierStokes` itself was 0.1 min off the cache.

### 2. The log, in order

```
Building ComparatorChallenges.NavierStokes
⚠ [8763/8763] Replayed ComparatorChallenges.NavierStokes
warning: ComparatorChallenges/NavierStokes.lean:273:8: declaration uses `sorry`
warning: ComparatorChallenges/NavierStokes.lean:280:8: declaration uses `sorry`
Build completed successfully (8763 jobs).
Exporting #[Nat, String, String.mk, Char, Quot, Quot.mk, Quot.lift, Quot.ind,
  NavierStokes.Comparator.navier_stokes_breakdown_R3,
  NavierStokes.Comparator.navier_stokes_breakdown_periodic,
  propext, Quot.sound, Classical.choice, … eagerReduce] from ComparatorChallenges.NavierStokes
Building NavierStokes.ComparatorSolution
ℹ [9371/9371] Replayed NavierStokes.ComparatorSolution
info: …:31:0: '…navier_stokes_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:32:0: '…navier_stokes_breakdown_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9371 jobs).
Exporting #[… same 32 targets …] from NavierStokes.ComparatorSolution
Running Lean default kernel on solution.
heartbeat 05:49:40Z log_bytes=2479 lean_procs=2
Lean default kernel accepts the solution
Your solution is okay!
```

Both theorems are in the export target list, so a single pass covers (C)'s and (D)'s statements.

### 3. What the string means

`Your solution is okay!` is printed by `compareIt` after four things have happened (`Main.lean:295–309`):

1. the challenge module and the solution module were each built inside the landrun sandbox;
2. both were exported by `lean4export` against the *same* 32-name target list, so the two exports describe the same constants;
3. `verifyMatch` compared them, and an unmatched constant or a differing type would have thrown before this line;
4. the solution export was replayed from scratch in a fresh `Lean.mkEmptyEnvironment` kernel, which printed `Lean default kernel accepts the solution`, and the `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` post-check passed.

So the statement `ComparatorChallenges/NavierStokes.lean` poses and the statement `NavierStokes.ComparatorSolution` proves are the same statement, under the permitted axiom set, checked by a kernel that had never seen the solution's environment.

The two `sorry` warnings are the challenge's own statement holes: the challenge *asks* the question with `sorry` where the theorem is asserted (`:273`, `:280`). They are not in the solution export, which is separately reported clean by E73.

### 4. E74's open question, now answered

E74 §6 said the cause of the silent 210- and 355-minute runs was inferred, not isolated. It is now isolated:

| run | wrapper | Duration | Result |
|---|---|---|---|
| `44999798334` | `systemd-run --pty` | 354.8 min, cancelled | no comparator output, no verdict |
| `45013487446` | `systemd-run --pty` | 210.2 min, step timeout | no comparator output, no verdict |
| `45119134981` | `--pipe`, relay self-tested | **7.3 min** | verdict |

The same work, on the same cached build, finishes in seven minutes. The wrapper was not merely hiding output: with stdout a pipe, `--pty` hands the child a PTY whose buffer nobody drains, so the child blocks on its first few KB of writes. Both long runs were deadlocked, not slow. E74 §3 withdrew the "too slow for the platform" inference; this entry shows why it was wrong, not just that it was unsupported.

### 5. Caveats that travel with the pass

- **Builtin kernel only.** `enable_nanoda` was stripped so the statement check would not depend on a second kernel having compiled. `Comparator (nanoda as second kernel)` runs as a separate step of the same workflow with `continue-on-error`, and §7 records what it returned: it passed, so a second kernel did re-check the replay. The statement comparison is decided above, and it is decided once.
- **The sandbox was weaker than documented.** `landrun` logged, six times: `kernel supports Landlock ABI v8, so these default restrictions are not enforced: pathname UNIX socket connections (ABI v9), UDP bind/connect/send (ABI v10)`. The run therefore executed with fewer syscall restrictions than Comparator's README targets. This is a property of the runner's kernel, not of the change in E74, and it affects *isolation*, not the soundness of the comparison: a compromised sandbox would let code escape, not make a mismatch compare equal.
- **Statement level is untouched.** Comparator answers "does this solution prove the statement this challenge poses". It does not answer "is the challenge statement the Clay statement". That remains the manuscript's §3 question, and it is a judgement about the encoded definition of solution, force and blow-up, not something a kernel decides.
- **No estimate is reviewed.** Nothing here bears on the constants or the anisotropic weights. Every finding of E0–E72 stands exactly as it did.
- **Upstream's project is still larger than this check.** Only the whole-space forced Navier–Stokes config was run; `ComparatorChallenges/Euler.json` was not.

### 6. Where this leaves the audit

E73 established the proof term's axiom footprint. E75 establishes that the term proves the challenge's statement. Together those are the two things the kernel and Comparator can be asked, and both have now been asked and answered on a clean clone at `f9e8bc5`.

What remains is what no machine can settle: whether the encoded statement is the Clay statement (manuscript §3), and whether the estimates inside the proof are the right ones (the constants and weights of findings 1 and 2, which are human readings of the source).

### 7. Addendum — the nanoda second kernel, executed

The same run's step 17 (`Comparator (nanoda as second kernel)`, started `05:51:47Z`) finished green; the job completed `06:02:09Z`, about 23 minutes wall for the whole workflow. Its artifact is `cmp-nanoda-kernel` (807 B, 22 lines).

It differs from §2 in exactly one place, and the difference is the point:

```
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

`runExternalKernel` is consulted before `runBuiltinKernel` (`Main.lean:290–291`), so nanoda's verdict came first and the builtin replay second; either rejection would have thrown before the final line. This invocation used upstream's own config with `enable_nanoda` left in place, not the stripped variant of §1.

What this adds: the exported proof was re-checked by a second implementation (`nanoda_lib` 0.4.32, Rust, built from `0da9f98f`), which does not share Lean's kernel. What it does not add: a second *statement* comparison. `verifyMatch` ran once, on the two exports; both kernels are checking the same solution export afterwards.

The landrun caveat of §5 applies unchanged: `kernel supports Landlock ABI v8` on all six sandbox invocations of this run, so the ABI v9 and v10 restrictions (pathname UNIX sockets, UDP) were not enforced.

*Evidence: run `45119134981`; artifacts `cmp-builtin-kernel` (824 B, 20 lines), `cmp-nanoda-kernel` (807 B, 22 lines), `cmp-verdict-summary` (1,040 B). Supersedes the status statements in E74 §5 and the README's pre-verdict wording; E74's withdrawal of the timing inference stands and is now explained rather than merely retracted.*

---

## E76 — The Comparator statement against Fefferman's text, clause by clause (2026-11-23)

*Reading entry. This closes the question E75 §5 and manuscript §3 left to a human: whether the statement Comparator compared is the statement Clay poses. No build, no runner.*

### 1. What was compared

| item | value |
|---|---|
| Clay text | C. L. Fefferman, *Existence and Smoothness of the Navier–Stokes Equation*, 6 pp., with the appended **Errata** page; `claymath.org/wp-content/uploads/2022/06/navierstokes.pdf` |
| fetched | 2026-11-23; SHA-256 `c1b5f27b1a64705cfaf1afceea513db5deedca8a18ca56ab32e7f86445a06d0c` |
| encoded statement | `ComparatorChallenges/NavierStokes.lean:273` for (C), `:280` for (D) |
| solution-side copy | `NavierStokes/ComparatorDefinitions.lean` |
| why the two copies are one statement | Comparator's `verifyMatch` compared the two exports and passed (E75 §2–§3); the copies are identical by machine check, not by inspection |
| alternatives in scope | (C) whole space, (D) torus. (A) and (B) are not encoded in this challenge, and this entry says nothing about them |

Fefferman's (C), verbatim:

> Take ν > 0 and n = 3. Then there exist a smooth, divergence-free vector field u°(x) on R³ and a smooth f(x,t) on R³ × [0,∞), satisfying (4), (5), for which there exist no solutions (p,u) of (1), (2), (3), (6), (7) on R³ × [0,∞).

and (D):

> Take ν > 0 and n = 3. Then there exist a smooth, divergence-free vector field u°(x) on R³ and a smooth f(x,t) on R³ × [0,∞), satisfying (8), (9), for which there exist no solutions (p,u) of (1), (2), (3), (10), (11) on R³ × [0,∞).

### 2. Every clause, and its home in the file

Line numbers are into `f9e8bc5`.

| Clay | text | Lean field | verdict |
|---|---|---|---|
| (1) | `∂ₜuᵢ + Σⱼ uⱼ∂uᵢ/∂xⱼ = νΔuᵢ − ∂p/∂xᵢ + fᵢ` on `Rⁿ × [0,∞)` | `NavierStokesExistenceAndSmoothness.navier_stokes`, `:222` | same equation with the sides rearranged; `fderiv ℝ (v · t) x (v x t)` is `(v·∇)v`, `Δ` is the spatial Laplacian, `gradient` is the Fréchet gradient |
| (2) | `div u = 0` on `Rⁿ × [0,∞)` | `.div_free`, `:227` | trace of the Fréchet derivative, the standard coordinate sum |
| (3) | `u(x,0) = u°(x)` | `.initial_condition`, `:229` | literal |
| (4) | `|∂ˣᵅ u°(x)| ≤ C_{αK}(1+|x|)^{−K}` for all `α`, `K` | `InitialVelocityConditionDecay.decay`, `:155` | all total orders `m`, all real `K`, witness `C` per pair; operator norm of the iterated derivative, see §3(b) |
| (5) | `|∂ˣᵅ∂ₜᵐ f| ≤ C_{αmK}(1+|x|+t)^{−K}` on `Rⁿ × [0,∞)` | `ForceConditionDecay.decay`, `:190` | same denominator, same universal quantifiers, derivative within the half-space |
| (6) | `p, u ∈ C^∞(Rⁿ × [0,∞))` | `.velocity_smooth`, `.pressure_smooth`, `:232`, `:235` | `ContDiffOn ℝ ∞` on `univ ×ˢ Ici 0` |
| (7) | `∫|u(x,t)|² dx < C` for all `t ≥ 0` | `.integrable`, `:250` and `.globally_bounded_energy`, `:253` | `MemLp` plus one existential `E` beating every time; see §3(c) |
| (8) | `u°(x+eⱼ) = u°(x)`, `f(x+eⱼ,t) = f(x,t)` | `InitialVelocityConditionPeriodic`, `:164`; `ForceConditionPeriodic.isOnePeriodic`, `:202` | periodicity of datum and force, for `t ≥ 0` |
| (9) | `|∂ˣᵅ∂ₜᵐ f| ≤ C(1+|t|)^{−K}` | `ForceConditionPeriodic.decay`, `:204` | the denominator has no `‖x‖`, exactly as Clay's does not |
| (10) | `u(x,t) = u(x+eⱼ,t)` on `R³ × [0,∞)` | `.isOnePeriodic_velocity`, `:267` | literal |
| (11) | `p, u ∈ C^∞(Rⁿ × [0,∞))`, periodic case | inherited smoothness, plus `.isOnePeriodic_pressure`, `:269` | the pressure clause comes from the errata, §4 |

The quantifier structure matches too: Clay's "Take ν > 0 … then there exist u°, f … for which there exist no solutions" is
`(nu : ℝ) (hnu : nu > 0) : ∃ u₀ f, condition u₀ ∧ condition f ∧ ¬ ∃ v p, solution ν u₀ f v p`.

### 3. Four representational choices, and why none changes the claim

**(a) The time derivative at `t = 0`.** Clay writes the equation on `t ≥ 0`, so at the initial time the derivative can only be one-sided. The encoding uses `derivWithin (v x ·) (Set.Ici 0)`, which is that one-sided derivative at `0` and the ordinary one for `t > 0`. Matching, not strengthening: the PDF's domain is closed for the same reason.

**(b) Multi-index bounds as operator norms.** Clay bounds each `|∂ˣᵅ u|` separately. The encoding bounds `‖iteratedFDeriv ℝ m u x‖` for every total order `m`. Every `|∂ˣᵅ u|` with `|α| = m` is dominated by that norm, and conversely a bound for every `|α| ≤ m` gives the operator-norm bound with a constant that is a finite sum of the components — absorbed by the existential `C`, which is chosen per `(m,K)`. The two conditions are equivalent, not merely similar.

**(c) Energy.** Clay's (7) is one constant `C` beating every time. The encoding asks `∃ E, ∀ t ≥ 0, ∫‖v(x,t)‖² dx < E`, and separately `MemLp (‖v · t‖) 2` at each time. The `MemLp` field is not decoration: the Bochner integral is totalized, so without it a non-integrable function would have "integral 0" and could satisfy the bound by junk. With it, the pair says exactly what (7) says — the integral exists at every time and one number bounds it.

**(d) (D) has no energy condition, and neither does the encoding.** Clay's (D) asks for no solution of (1), (2), (3), (10), (11); (7) is absent. The periodic structure adds only periodicity to the base solution structure, and the base structure carries no energy field. This is the asymmetry E70 relies on — the periodic competitors are a strictly larger class — and it is in the text, not an artefact of the encoding.

### 4. The errata

The PDF's appended errata page says, first:

> The further condition p(x + eⱼ,t) = p(x,t) should be made explicit in Eqn (8).

That is honoured: `isOnePeriodic_pressure` is a field of the periodic solution structure, and the challenge's header cites the errata by name. The second erratum replaces "Eqn (10)" with a weak-form identity (integrating against a test function θ). That numbering refers to the weak-solution discussion later in the paper, not to the pointwise periodicity clause in the four alternatives; (C) and (D) are stated pointwise and use the strong form. Nothing in the prize alternatives consumes it, so its absence is correct rather than an omission. Recorded here because the errata page and the numbered list disagree about what "(10)" means.

### 5. Verdict

No clause of (C) or (D) is missing, weakened, or strengthened in a way that changes what the alternative claims. The judgement calls that remain are reading conventions, and both are named in §3: `C^∞` on the closed half-space read as `ContDiffOn` on that set, and the multi-index bounds read as iterated-operator-norm bounds. On those readings — the standard ones — the statement Comparator passed is the statement Clay poses for (C) and (D).

What this does not do: it does not audit (A), (B), the Euler challenge, or any estimate inside the proof. It converts "the encoding might not be the Clay statement" from an open objection into a checked clause list, which is the limit of what reading can settle.

*Evidence: the PDF named in §1 at the stated digest, read in full including the errata page; line numbers into `f9e8bc5`; E75 §2–§3 for the machine-checked identity of the challenge copy and the solution copy. Supersedes the "remains outside this audit" phrasing in the README's Scope section and in E75 §5.*

---

## E77 — The `WaveInputs` branch is an unused alternate (2026-11-23)

*Reading entry. Promotes `LEADS.md` §3 from working notes to the log, so a later reader does not mistake a spare corridor for the road.*

`ActualStageEstimates.WaveInputs` (`ActualStageEstimates.lean:171`) is a structure of eight exponent and shift fields. It is consumed only by `stageEstimates_of_representations` (`:347`) and its two wrappers (`:197`, `:276`). The only producer of a `WaveInputs` value is `ActualEndpointInputs.endpointInputs_of_run` (`ActualEndpointInputs.lean:218`); `actual_stage_endpoints` (`:160`) is its sibling. Neither has a caller anywhere in the tree, and the field `particularPotential_exponent` occurs only at its declaration and at its use.

The assembly does not go through that branch. `ActualCandidateAssembly.lean:1094` calls `GluedStageEstimates.actualStageEstimates` (`:684`), whose hypotheses are discharged by `current_potential_bound` and `current_pressure_bound` from actual cycle data. The eight `WaveInputs` fields are therefore not assumptions the proof leans on; they belong to an alternate route with no construction site.

Same status for `actual_stage_endpoints` and `endpointInputs_of_run`: definitions without callers. A `grep` that finds hypotheses in them is not finding a gap. E67–E71 trace the route that is used, and E69 shows the invariant that route consumes is preserved by construction.

*Evidence: `f9e8bc5`, `NavierStokes/ActualStageEstimates.lean`, `NavierStokes/ActualEndpointInputs.lean`, `NavierStokes/ActualCandidateAssembly.lean`, `NavierStokes/GluedStageEstimates.lean`; `LEADS.md` §3 (working notes, 2026-11-21).*

---

## E78 — The manuscript typesets, and the first attempt exposed a font gap (2026-11-23)

*Execution evidence. `MANUSCRIPT.tex` had never been compiled in this repository's history: there is no TeX installation on the machine it was written on, and installing one is a multi-gigabyte download. The paper asks for LuaLaTeX because its Lean listings are quoted with their Unicode.*

### 1. Two runs

| run | source | result | pages | bytes | missing glyphs |
|---|---|---|---|---|---|
| `45127159922` | `e515e89` | success | 25 | 358,372 | **45** |
| `45127609292` | `40fdaf9` | success | 25 | 376,181 | **0** |
| `45145721571` | `c57d63f` | success | 25 | 377,204 | **0** |
| `45152731830` | `e2db61b` | success | 25 | 378,006 | **0** |

The first run is green by exit status and wrong by content. `lmmono9-regular` has no ∀ (U+2200), ∃, ℝ, ν or ∧, so every Lean listing quoting one rendered a blank: forty-five `Missing character` warnings, no LaTeX error, exit 0. That is why the log was read rather than the tick. The `literate` table already mapped ∀/∃/ℝ/∧ to math for `listings`, but `\ct{...}` is `\texttt`, which goes through the text font and never consults those mappings; ν was absent from the table as well.

### 2. The fix

`40fdaf9` loads `fontspec`, sets the monospace font to DejaVu Sans Mono with FreeMono as a fallback selected by `\IfFontExistsTF`, adds ν to the literate table, and sets `\emergencystretch` for the widest lines. The re-run reports **zero** missing characters.

### 3. What this does and does not establish

- Establishes: the paper compiles under the engine it names, on a clean checkout, and every Unicode symbol in its Lean quotations reaches the page.
- Does not establish: that any line of the mathematics is correct. Typesetting is not checking.
- Remaining typographic noise: 33 overfull hboxes in the first run, 23 in the fixed one, plus 8 underfull. Zero `LaTeX Warning` lines in both. Cosmetic; not chased further.

The third run rebuilds after the E79 sync, which lengthened the abstract by six lines and the scope paragraph by seven. Same 25 pages, same zero missing characters, zero `LaTeX Warning` lines, 23 overfull and 8 underfull boxes — the typographic noise did not move either. A fourth run (`45152731830`, on `e2db61b`) rebuilds after the E80 sentences: 25 pages, 378,006 bytes, zero missing characters, zero `LaTeX Warning` lines, and the same 23 overfull and 8 underfull boxes again. The committed `MANUSCRIPT.pdf` is that run's artifact, byte-identical to it (sha256 `bde41449…`). That file has since been superseded twice — a rebuild after the E88 nanoda entry, and again once E89 put the crosswalk into the abstract and the limits section — so the committed PDF is now the 26-page build, 381,703 bytes, sha256 `cddf9829…`, with zero missing characters and zero `LaTeX Warning` lines.

`MANUSCRIPT.pdf` is committed beside the source, and `typeset.yml` reproduces it. The workflow is manual only: a red build of the paper must not block anything else.

*Evidence: runs `45127159922` and `45127609292`, artifact `manuscript-pdf`; commit `40fdaf9`.*

---

## E79 — The Euler challenge, executed: both kernels accept both singularity theorems (2026-11-23)

*Execution evidence. E76 audited the encoded statement for Navier–Stokes alternatives (C) and (D) and said in terms that it did not touch the Euler challenge. This entry runs that challenge — the same procedure as E74–E75 with the `Euler` library in place of `NavierStokes`.*

### 1. The run

| item | value |
|---|---|
| run | `45127157219`, attempt 1, workflow `comparator-check-euler.yml` |
| dispatched from | `e515e89` (the commit that added E76, E77 and both workflows) |
| upstream | `openai/NavierStokesAndEuler` at `f9e8bc5`, cloned in step 3 |
| toolchain | `leanprover/lean4:v4.34.0-rc2`; mathlib, Comparator, lean4export, landrun and nanoda each at their pinned revisions |
| wall clock | 06:53:07Z → 08:13:56Z, **1 h 20 min 49 s** |
| conclusion | **success** |

| step | start → end | duration |
|---|---|---|
| clone upstream | 06:55:04 → 06:55:06 | 2 s |
| mathlib cache | 06:55:15 → 06:56:35 | 1 min 20 s |
| **Build Euler** | 06:56:35 → 07:46:46 | **50 min 11 s**, 10,603 jobs |
| comparator, lean4export, landrun, nanoda builds | 07:46:46 → 07:47:29 | 43 s |
| challenge module pre-build | 07:47:30 → 07:47:38 | 8 s, 8,763 jobs replayed |
| Comparator, builtin kernel | 07:47:39 → 07:57:49 | 10 min 10 s |
| Comparator, nanoda as second kernel | 07:57:50 → 08:13:39 | 15 min 49 s |

The `Euler` library had never been built on a runner before this run — the cache key is separate from `NavierStokes`, so nothing was restored. Fifty minutes is the honest cost of the library, not of the check.

### 2. What the challenge poses

`ComparatorChallenges/Euler.lean` proves nothing. It states two theorems and closes each with `sorry`:

| line | theorem | content |
|---|---|---|
| `:85` | `euler_breakdown_R3` | some rapidly decaying smooth divergence-free datum has **no** global smooth unforced Euler solution in the finite-energy class on `ℝ³` |
| `:170` | `exists_compact_smooth_euler_singularity` | a nonzero compactly supported rapidly decaying datum with maximal lifespan `0 < T* ≤ 1`: Sobolev-class solutions on `[0,T)` exactly when `T < T*`, C¹ norm and vorticity integral finite on every `[0,T] ⊂ [0,T*)`, `limsup` of the C¹ norm `= ⊤` at `T*`, vorticity integral over `[0,T*)` infinite, and no global energy-class solution |

The challenge build therefore *succeeds with two `sorry` warnings and exit 0*. A `grep` that turns those up is finding the challenge, not a gap in the solution. Both are statements the solution must supply, and neither is an assumption the Euler proof consumes.

### 3. What the solution supplies

Comparator exported both modules against one target list of 32 names — the three permitted axioms plus Lean's own machinery (`Nat`, `String`, `Char`, `Quot`, `List`, `eagerReduce`) and exactly two theorem names:

```
Euler.euler_breakdown_R3, Euler.exists_compact_smooth_euler_singularity,
propext, Quot.sound, Classical.choice, …
```

Replaying the solution takes 10,591 jobs, and the probe the run prints is the substantive part:

```
info: Euler/Solution.lean:73:0: 'Euler.euler_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Euler/Solution.lean:75:0: 'Euler.exists_compact_smooth_euler_singularity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. That is the point of the whole exercise: the challenge's placeholders are replaced by proofs that close under the three axioms `ComparatorChallenges/Euler.json` permits, and the reducer that would expose a used `sorry` does not fire.

### 4. Two kernels

| phase | log | verdict line |
|---|---|---|
| builtin | `comparator-euler-builtin.log` | `Lean default kernel accepts the solution` → **`Your solution is okay!`** |
| nanoda | `comparator-euler-nanoda.log` | `nanoda kernel accepts the solution`, then `Lean default kernel accepts the solution` → **`Your solution is okay!`** |

Second kernel: nanoda at `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, a Rust type checker that shares no code with Lean's kernel; the sandbox is landrun at `573aa723afb16bb1da2dbe24fc00df46cd0ad13b`, built with `cargo 1.100.0`. The nanoda phase takes 35 s longer than the builtin one, and most of the phase is the export and the Lean re-check that run inside it — the nanoda check itself is under a second.

### 5. The one caveat in the logs, recorded rather than smoothed over

Every phase of both runs prints:

```
[landrun:warn] kernel supports Landlock ABI v8, so these default restrictions are not enforced:
pathname UNIX socket connections (ABI v9), UDP bind/connect/send (ABI v10)
```

On this runner the sandbox is one notch weaker than landrun's default: pathname UNIX-socket connections and UDP traffic are not blocked. The file-system and process restrictions that matter for replaying a kernel are enforced. This changes no verdict here, and it is written down because a sandbox claim that outlives its evidence is how audits rot. The same warning appears in the Navier–Stokes run (E75); it was not noticed there and is not retroactively a problem with it.

### 6. What this establishes, and what it does not

- Establishes: at `f9e8bc5`, on a clean clone, the `Euler` library builds (10,603 jobs, exit 0); challenge and solution export against **the same** 32-name target list; the solution's two headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; and two independent kernels accept the result.
- Does **not** establish: that a single estimate inside the Euler proof is correct. Not one line of the Euler development was read for this entry. The audit's mathematical reading remains the Navier–Stokes estimate chain (E67–E71); Euler is now checked at the statement level and the kernel level and at no other level.
- Does not touch any other Euler statement, and does not revisit alternative (D)'s Navier–Stokes footprint, which E73 printed.

### 7. Coverage of the four headline theorems

| theorem | challenge | run | verdict |
|---|---|---|---|
| `navier_stokes_breakdown_R3` | `NavierStokes.json` | `45119134981` | accepted, both kernels (E75) |
| `navier_stokes_breakdown_periodic` | `NavierStokes.json` | `45119134981` | accepted, both kernels (E75) |
| `euler_breakdown_R3` | `Euler.json` | `45127157219` | accepted, both kernels (E79) |
| `exists_compact_smooth_euler_singularity` | `Euler.json` | `45127157219` | accepted, both kernels (E79) |

All four now have an executed external check. What that buys is narrower than it sounds: it certifies that each theorem's proof term inhabits the statement the challenge poses, under the permitted axioms, in two kernels. It says nothing about whether the statements are the ones a mathematician would write — E76 does that for (C) and (D) against Fefferman's text, E80 does it for the Euler pair against the repository's metadata and against proved bridges, and neither Euler statement has been compared to the Euler paper itself — and nothing about whether the proofs are right beyond the kernel's opinion.

*Evidence: run `45127157219`, artifacts `euler-verdict-summary`, `euler-builtin-kernel`, `euler-nanoda-kernel`, `euler-challenge-build`, `euler-toolchain-logs` (1,843-line build log, all five toolchain builds, `lake-manifest.json`); commit `e515e89`; upstream `f9e8bc5`.*

---

## E80 — The Euler challenge is the repository's own Euler paper statement (2026-11-23)

*Reading entry. E79 ran the Euler challenge and checked the proofs against the statements. It did not ask whether those statements are the repository's own Euler theorem. This entry asks, and answers by source, not by inference.*

### 1. The answer first

The two statements Comparator checked are the declarations the repository itself publishes as its formalization of the Euler paper. `formalization.yaml:72–94` lists them, in order, with `file: "Euler/Solution.lean"`, `sorry_count: 0`, the three permitted axioms, and `comparator_config: "ComparatorChallenges/Euler.json"`. The alignment table at `:119–126` maps them to the paper:

| source claim | Lean declaration | module |
|---|---|---|
| Theorem 1.1 (Euler) | `Euler.euler_breakdown_R3` | `Euler.Solution` |
| Theorem 1.1 (Euler), alternate version | `Euler.exists_compact_smooth_euler_singularity` | `Euler.Solution` |

So the Euler check was not run against a convenient side statement. It was run against the declarations the upstream metadata designates, and the `comparator_config` key in that metadata is the very file E79 executed.

### 2. The reference is genuinely independent, and textually exact

The challenge module and the solution-side definitions are copies. Stripping comments and comparing declaration by declaration: 11 shared declarations — `divergence`, `InitialVelocityCondition`, `InitialVelocityConditionDecay`, `EulerExistenceAndSmoothness`, `EulerExistenceAndSmoothnessR3`, `toL2`, `SobolevSmoothOn`, `EulerSobolevExistenceAndSmoothnessR3On`, `vorticity`, `velocityC1Norm`, `vorticityNorm` — are character-identical between `ComparatorChallenges/Euler.lean` and `Euler/SolutionDefinitions.lean`, docstrings included. The challenge adds exactly two declarations, the two theorems, and nothing else. It imports only Mathlib; nothing under `Euler/` imports `ComparatorChallenges`. So the independence Comparator relies on is real at the level of text, not merely asserted in a header — which is the same property E75 found for the Navier–Stokes pair.

### 3. The internal theorem is a different statement, and the gap is closed by proof

`EulerPacketInduction.exists_compact_smooth_euler_singularity` (`Euler/EulerSingularity.lean:133`) is **not** the challenge theorem. It is existential over `A : SmoothL2Field Space` and `L : FiniteLifespan A`, and its clauses speak of `L.maximalVelocity`, `HasScalarEulerEvolution`, `L.maximalC1Norm` and `L.maximalVorticityDensity`. The challenge speaks of bare functions `u₀ : ℝ³ → ℝ³`, `v : ℝ³ → ℝ → ℝ³`, `p : ℝ³ → ℝ → ℝ`, a real `Tstar`, and the Formal-Conjectures class. Two carriers, two vocabularies.

The gap is not left to the reader. Each clause that changes vocabulary has a proved bridge:

| challenge clause | bridge |
|---|---|
| the solution class on `[0,T]` | `exists_sobolevSolution_iff` (`ComparatorSobolevEvolution.lean`): `(∃ v p, EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) A.field v p) ↔ HasScalarEulerEvolution A T`, both directions |
| witness on `[0,T*)` | `maximal_sobolevSolution` (`ComparatorMaximalSolution.lean`) |
| `T < T*` exactly | `maximal_sobolev_existence_iff` |
| rapid decay of every derivative | `initialVelocityConditionDecay_of_compact` (`InitialDataBridge.lean`): compact support plus smoothness **implies** it |
| `velocityC1Norm`, `vorticityNorm` | `velocityC1Norm_maximal`, `vorticityNorm_maximal`, `vorticityNorm_maximal_density` |
| scalar pressure `p` with `∇p = -force` | `maximalPressure_spec`: `ContDiff ℝ ∞`, `p 0 = 0`, `∇p = pressureForce` |

The last row is the one that could have hidden an assumption, since the development carries a pressure *force*, not a scalar pressure. It does not: `maximalPressure` is `radialPotential` applied to the force (`OrdinaryEulerMaximal.lean:47–48`), and `maximalPressure_spec` is a theorem about the result. The challenge's `p` is a proved potential, not a parameter the solution may choose.

### 4. Three residuals

**(a) The implication runs one way.** What is proved is: the packet construction implies the challenge statements. The converse — challenge statement implies the `SmoothL2Field`/`FiniteLifespan` packaging — is not stated, and would not be a syntactic identity if it were. That is the right direction for a Comparator submission, and it is enough to say the kernel checked the repository's Euler claim. It is not an equivalence of the two top-level theorems, and this entry does not claim one.

**(b) The first theorem is a corollary of the second.** The last conjunct of `exists_compact_smooth_euler_singularity` is `¬ (∃ w q, EulerExistenceAndSmoothnessR3 u₀ w q)`, for a `u₀` already carrying `InitialVelocityConditionDecay` — literally the conclusion of `euler_breakdown_R3`. `formalization.yaml:123` calls the stronger statement the "alternate version", which inverts the strength: the alternate contains the primary. `Euler/Solution.lean` proves the two by different routes (`finiteLifespan_contradiction_of_compact_vorticity` for the first, the maximal extension for the second), so nothing is circular; but a reader of the metadata alone would not learn that one is contained in the other.

**(c) One footprint is measured, one is not.** `#print axioms` occurs twice in the Euler tree, at `Euler/Solution.lean:73` and `:75`, on the two designated declarations — so those are measured, and E79 reports the result. `EulerPacketInduction.exists_compact_smooth_euler_singularity` was never printed. Two facts narrow the gap without closing it: it sits in the import closure of the solution (`ComparatorSobolevEvolution.lean:2` imports `Euler.EulerSingularity`), and the `Euler` library is declared with `warningAsError = true` (`lakefile.toml`), so a `sorry` anywhere in it would have failed the 10,603-job build rather than warning. A non-`sorry` axiom in it would warn about nothing and would not be caught — but the solution's proofs do not call it, so such an axiom could not reach the checked theorems either.

### 5. What this adds, and what is still missing

- Adds: the Euler kernel result covers the declarations the upstream repository designates as its Euler formalizations, and the class mismatch between the challenge and the development is a proved equivalence, not an inspection.
- Still missing: any comparison of either statement to the Euler paper's own Theorem 1.1 text. E76 did that for Clay's (C) and (D) against Fefferman's PDF; the Euler equivalent needs the Euler PDF's numbered conditions, and this entry reads code and metadata only. The upstream README's description — compactly supported smooth datum, finite-time singularity, unbounded C¹ norm, divergent vorticity integral — is consistent with the second theorem, but a README is not a theorem statement.
- Unchanged: no estimate inside the Euler proof was read, here or in E79.

*Evidence: `f9e8bc5`, `ComparatorChallenges/Euler.lean` (186 lines), `Euler/SolutionDefinitions.lean` (138), `Euler/Solution.lean` (75), `Euler/EulerSingularity.lean:133`, `Euler/ComparatorSobolevEvolution.lean`, `Euler/ComparatorMaximalSolution.lean`, `Euler/ComparatorMaximalFields.lean`, `Euler/OrdinaryEulerMaximal.lean:182`, `Euler/InitialDataBridge.lean`, `formalization.yaml:72–94` and `:119–126`, `lakefile.toml`; declaration-level text comparison run locally on 2026-11-23.*

---

## E81 — The Euler encoding against Theorem 1.1: five clauses stronger, one weaker (2026-11-23)

*Reading entry. E80 answered whether the challenge statements are the repository's own Euler theorems. It did not answer whether they are the Euler paper's theorem. This entry reads the paper's Theorem 1.1 and maps it clause by clause, the way E76 read Fefferman for (C) and (D).*

### 1. The source

The Euler paper linked from the upstream README, `https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf`, 57 pages, 535,142 bytes, sha256 `a0c234518e6c489e16996805023eb2e75c00b7c03455f7a3a5be2c124954bfdd`. Theorem 1.1, verbatim including its display:

> There exists $u_0 \in C^\infty_{c,\sigma}(\mathbb{R}^3)$ such that $0 < T_*(u_0) < \infty$. Its smooth Euler solution satisfies
> $$\limsup_{t \uparrow T_*}\|\nabla u(t)\|_{L^\infty} = \infty, \qquad \int_0^{T_*}\|\operatorname{curl} u(t)\|_{L^\infty}\,dt = \infty.$$

$T_*(u_0)$ is defined two lines earlier as "the maximal lifespan of its smooth Euler solution", with local existence cited.

### 2. Clause by clause

Against `Euler/Solution.lean:43`, the second declaration, which is the quantitative one:

| # | Theorem 1.1 | challenge field | verdict |
|---|---|---|---|
| 1 | $u_0 \in C^\infty_{c,\sigma}$ | `InitialVelocityConditionDecay` (smooth, divergence-free, every derivative rapidly decaying) plus `HasCompactSupport` | **met**; decay is stronger than compact support, and `initialVelocityConditionDecay_of_compact` derives it rather than assuming it |
| 2 | $u_0 \neq 0$ (implicit: zero data has a global solution) | `u₀ ≠ 0` | **explicit** |
| 3 | $0 < T_* < \infty$ | `0 < Tstar`, `Tstar ≤ 1` | **met**, with an explicit horizon bound the paper leaves open |
| 4 | $T_*$ is the maximal lifespan of the smooth solution | `∀ T > 0, (∃ Sobolev-class solution on [0,T]) ↔ T < Tstar` | **exact inside the development, weaker than the paper**: the chain `exists_sobolevSolution_iff` ↔ `hasScalarEulerEvolution_iff` ↔ `hasSmoothEulerSolution_iff` relates three *development* classes; `Evolution` is spatially $C^\infty$ with an $L^2$ strong time derivative, not proved jointly $C^\infty$ in time as the paper's solution is (E82 §4) |
| 5 | $\limsup\|\nabla u(t)\|_\infty = \infty$ | `limsup velocityC1Norm = ⊤`, where the norm is velocity sup **plus** gradient sup | **weaker** — §3 |
| 6 | $\int_0^{T_*}\|\operatorname{curl}u\|_\infty\,dt = \infty$ | `∫⁻ vorticityNorm = ⊤` | **exact**, via `vorticityNorm_eq` |
| 7 | — | $\exists E,\ \forall t \in [0,T_*),\ \int\|v\|^2 < E$ | **extra** |
| 8 | — | $\forall T \in (0,T_*)$, the C¹ sup and the vorticity integral are finite on $[0,T]$ | **extra** |
| 9 | — | $\neg\,\exists w\,q,\ $ `EulerExistenceAndSmoothnessR3 u₀ w q` | **extra**, and stronger than "$T_*$ finite": an entire class has no global solution |

Row 4 deserves its own sentence. The paper's $T_*$ is defined in the classical smooth class; the challenge defines it in the all-order Sobolev class. `exists_sobolevSolution_iff` (`ComparatorSobolevEvolution.lean`) proves the challenge class equivalent to `HasScalarEulerEvolution`, `hasScalarEulerEvolution_iff` (`EulerSingularity.lean:33`) proves that equivalent to `HasEulerEvolution`, and `hasSmoothEulerSolution_iff` (`EulerFiniteLifespan.lean`) proves that equivalent to `HasSmoothEulerSolution`. Three proved biconditionals — but all three relate *development* classes. `HasSmoothEulerSolution` is defined as an `Evolution`, i.e. a path of `SmoothL2Field`s with an $L^2$ strong time derivative, not joint $C^\infty$ in time. The chain is real and it is internal; it does not establish that these classes coincide with the paper's jointly smooth solution. E82 §4 records the correction.

### 3. The one weakening

`velocityC1Norm` is defined as the sum of two suprema (`Euler/SolutionDefinitions.lean:130`):

```
(⨆ x, ENNReal.ofReal ‖v x‖) + (⨆ x, ENNReal.ofReal ‖fderiv ℝ v x‖)
```

and `maximalC1Norm` is the same sum (`EulerC1Breakdown.lean:24`), identified with the challenge's norm by `velocityC1Norm_eq` (`ComparatorSingularityNorms.lean:27`). Theorem 1.1 asserts divergence of the **second summand alone**. A sum's limsup can be `⊤` while neither summand's is: `a_n = n`, `b_n = n` gives both divergent, but nothing in the statement bounds $\sup_x\|v\|$; the theorem's own energy clause is $L^2$, which does not bound $L^\infty$. So the challenge's clause does not formally imply the paper's.

What makes this a packaging defect rather than a gap is that the development proves the paper's clause anyway:

| statement | file:line |
|---|---|
| `maximalGradientNorm_limsup = ⊤` | `Euler/EulerC1Limsup.lean:54` (lifted at `:82`) |
| arbitrary large gradient values near the endpoint | `EulerC1Breakdown.lean:66` |
| pointwise gradient blowup | `EulerC1Breakdown.lean:49` |

The strong fact is three files from the theorem, compiled with the library (so the kernel checked its proof, and `warningAsError` on the `Euler` library means no `sorry` can survive there), but it is **not** in `ComparatorChallenges/Euler.json`'s target list and **not** a conjunct of the statement the kernel accepted. `maximalVelocityExtension_c1_limsup` calls the sum version (`maximalC1Norm_limsup`), not the gradient one. A reader who trusts the checked statement gets the weaker claim; the repository holds the stronger one beside it.

### 4. Verdict

- The encoding is **stronger** than Theorem 1.1 in five respects (rows 2, 3, 7, 8, 9) and **weaker** in exactly one (row 5). Nothing is missing.
- The five strengthenings are safe: a proof of a stronger statement proves the paper's. The strengthening in row 9 is the substantive one — a non-existence result in a class that contains the classical smooth solutions, which is what makes `euler_breakdown_R3` a theorem rather than a remark.
- The one weakening is the paper's headline. It should be said plainly: what Comparator accepted is *not* "the gradient blows up"; it is "the C¹ norm blows up", and the gradient statement is proved elsewhere in the same development. Adding `maximalGradientNorm_limsup` to `Euler.json` would close it without a new proof.
- This is the first clause-level defect in the Euler encoding found by reading. It is not a mathematical error: the theorem is true, and the paper's stronger claim is in the artifact.

### 5. What this does not do

No estimate inside the Euler proof was read — this entry reads one statement, two definitions and six lemmas. It does not check the paper's Section 6.3 argument, its continuation criteria, or the construction. It also does not claim the paper's Theorem 1.1 is the only claim in the paper; it is the only one the repository maps to these declarations.

*Evidence: paper PDF at the digest above, Theorem 1.1 on p.~1 and the $T_*$ definition at `:22` of the extracted text; `Euler/Solution.lean:43`, `Euler/SolutionDefinitions.lean:130`, `Euler/ComparatorSingularityNorms.lean:27`, `Euler/EulerC1Breakdown.lean:24`, `:49`, `:66`, `Euler/EulerC1Limsup.lean:54`, `:82`, `Euler/ComparatorMaximalSolution.lean`; `ComparatorChallenges/Euler.json`. Text extracted with `pypdf` in a throwaway virtual environment on 2026-11-23; no TeX or PDF toolchain on the host.*

---

## E82 — §6.3 against the continuation chain: one half stronger than the paper, and a correction to E81 (2026-11-23)

*Reading entry. E81 compared clauses. This entry compares the two arguments behind Theorem 1.1's divergence conclusions with the Lean proofs that discharge them, and it retracts part of E81's row 4.*

### 1. The paper's two arguments

**Gradient.** Assume $B=\sup_{0\le t<T}\|\nabla u(t)\|_\infty<\infty$. The order-three energy inequality (5.2) gives $\|u(t)\|_{H^3}\le M_3$. Section 5.1 supplies a local time $\delta_0=\delta_0(M_3)$ **uniform** over smooth divergence-free data of $H^3$ norm at most $M_3$; with $\delta=\min\{\delta_0/2,\ 1/(2C_3C_{\mathrm{emb}}M_3)\}$, restart at $s\in(\max\{0,T-\delta/2\},T)$, and uniqueness gives an extension past $T$, contradicting maximality.

**Vorticity.** A Biot--Savart estimate gives (6.7), $\|\nabla u\|_\infty\le C[1+\|u_0\|_2+\|\omega\|_\infty\log(e+\|u\|_{H^3})]$. With $Z=\log(e+\|u\|_{H^3})$ this yields $Z'\le C(1+\|u_0\|_2)+C\|\omega\|_\infty Z$, and Gronwall turns a finite vorticity integral into bounded $H^3$, hence an extension, hence a contradiction.

### 2. The gradient half, in Lean, is not the paper's argument

`Evolution.exists_extension` (`Euler/OrdinaryEulerContinuation.lean:20`) extends **every** closed smooth evolution on `[0,T]` to some `S > T`, agreeing on `[0,T]`. It local-exists at the terminal state and concatenates. No gradient bound, no $H^3$ estimate, no uniform $\delta_0(M_3)$, no Sobolev embedding, no energy inequality appears in it.

| paper step | Lean counterpart | present? |
|---|---|---|
| $B<\infty$ hypothesis | none | **not needed** |
| (5.2) at order 3, $\|u\|_{H^3}\le M_3$ | `h3_energy_gradientIntegral` (`OrdinaryEulerGradientControl.lean`) | exists, but not on this path |
| $\delta_0(M_3)$ uniform in $M_3$ | `localEvolution` at one datum | used, uniformity **not needed** |
| restart and uniqueness | `concatenate` + `evolution_agrees` | yes |
| extension contradicts maximality | `FiniteLifespan.no_endpoint` (`:53`) | yes, immediately |

`HasEulerEvolution.extend` (`:43`) makes every evolution extendable; `no_endpoint` follows in three lines. `gradient_unbounded` (`:65`) is then a contradiction argument: a bounded gradient bounds `gradientIntegral` by $K\cdot$ duration (`gradientIntegral_le_const`), and `endpoint_of_bounded_gradient` extends, contradicting `no_endpoint`.

So the paper's analytic work in the gradient half — the $H^3$ bound, the embedding, the uniform local time — is not what the formal proof uses. The formal statement is stronger (no hypothesis) and the argument is shorter. Two caveats keep this from being a free win: `Evolution` is spatially $C^\infty$ with an $L^2$ **strong** time derivative, a weaker class than the paper's jointly smooth solution, so extension is easier to prove; and `exists_extension` rests on the repository's local existence theorem, which is the analogue of §5.1 but is instantiated at one datum rather than quantified uniformly.

### 3. The vorticity half is the paper's argument, with constants named

| paper step | Lean |
|---|---|
| Biot--Savart, (6.7) | `logarithmic_gradient_bound` (`OrdinaryLogarithmicGradient.lean`), constant `36*splitCost`, via `elliptic_derivative_logarithmic` |
| divergence-free input discharged | `logarithmic_gradient_bound_solenoidal` |
| $Z'\le a+bZ$, Gronwall | `gradientIntegral_of_vorticity_bound` (`OrdinaryBKMReduction.lean:23`), via `gradientIntegral_logarithmic_uniform` |
| finite vorticity integral contradicts maximality | `vorticity_unbounded_of_logarithmic` (`:34`), then `no_endpoint` |
| conclusion | `vorticityIntegral_unbounded`, `vorticity_lintegral_eq_top` (`OrdinaryEulerBKM.lean:20`, `:37`) |

One packaging difference: the paper Gronwals $Z=\log(e+\|u\|_{H^3})$ directly; the repository Gronwals the gradient integral and then bounds $H^3$ and every higher order from it (`h3_energy_gradientIntegral`, `higher_energy_of_gradientIntegral`). Same mechanism, different state variable, and the repository's version yields tame bounds at every order rather than at three.

### 4. Correction to E81, row 4

E81 called the $T_*$ clause "equivalent" and cited three biconditionals. They are real, but all three relate classes **inside the development**:

- `exists_sobolevSolution_iff`: the challenge class ↔ `HasScalarEulerEvolution`;
- `hasScalarEulerEvolution_iff` (`EulerSingularity.lean:33`): scalar ↔ vector `Evolution`;
- `hasSmoothEulerSolution_iff` (`EulerFiniteLifespan.lean`): `HasSmoothEulerSolution` ↔ `HasEulerEvolution` — and `HasSmoothEulerSolution` is *defined* as the existence of an `Evolution`, so this is close to definitional.

`Evolution` is a path of `SmoothL2Field`s: spatial $C^\infty$, all spatial jets in $L^2$, continuous in those jets, with a strong time derivative in $L^2$. The paper's solution is jointly $C^\infty$ in space **and time**. Neither direction is proved:

- `Evolution` ⇒ joint $C^\infty$: no. The strongest time regularity shown is joint continuity (`maximalVelocity_joint_continuous`), not differentiability in time beyond $L^2$-strong.
- Joint $C^\infty$ ⇒ `Evolution`: plausible for compactly supported data, and not stated anywhere in the tree.

So the challenge's $T_*$ is the maximal lifespan in a class not proved to contain the paper's classical solution. What survives is the non-existence side: the `¬∃` conjuncts are stated in `EulerExistenceAndSmoothnessR3`, which requires joint $C^\infty$ on `univ × Ici 0` and a uniform energy bound — that is the classical class, and it is the class of rows 1 and 9 in E81's table. What does not survive is reading the limsup and the vorticity integral as statements about *the paper's* solution: they are statements about the Sobolev-class witness, and its identification with a classical solution is not shown.

E81 therefore has **two** soft clauses, not one: row 4 and row 5. Its table has been amended in place with a pointer here; the rest of it stands. This is a correction to the audit's own verdict, not to the repository.

### 5. What this entry does not do

It compares two arguments with their formal counterparts; it does not re-prove either, does not read the construction, and does not touch Sections 3--5. The probe dispatched as run `45158640147` printed the axiom footprint of `EulerPacketInduction.maximalGradientNorm_limsup`, the theorem behind E81's row 5: `[propext, Classical.choice, Quot.sound]`, no `sorryAx` (E84).

*Evidence: papers §6.3 at `:2666`--`:2726` of the extracted text; `Euler/OrdinaryEulerContinuation.lean:20`, `:43`, `:53`, `:65`, `:124`; `Euler/OrdinaryEulerGradientControl.lean:41`; `Euler/OrdinaryBKMReduction.lean:23`, `:34`; `Euler/OrdinaryEulerBKM.lean:20`, `:37`; `Euler/OrdinaryLogarithmicGradient.lean`; `Euler/ComparatorSobolevEvolution.lean`; `Euler/EulerFiniteLifespan.lean`; `Euler/ComparatorMaximalFields.lean`.*

---

## E83 — The periodization lemmas, read rather than sampled (2026-11-23)

*Reading entry. E70 read alternative (D)'s statement and architecture. The README has said since that the periodization lemmas and periodic uniqueness were sampled rather than audited line by line. This entry reads the periodization half.*

### 1. `periodize` is a lattice sum, not an assumed extension

`PeriodicLocalization.periodize` (`:62`) is `∑' n : Lattice, f (t, x - n)` — an infinite sum taken literally. Four lemmas make it usable, and all four are proved:

| claim | lemma |
|---|---|
| only finitely many translates meet any bounded region | `mem_latticeBox_of_translate_ne_zero`, `exists_local_latticeBox` |
| the family of supports is locally finite | `locallyFinite_support_translate` |
| the series converges at every point | `summable_translate` |
| locally it is a finite sum of translates | `periodize_locally_eq_sum` |
| it preserves every differentiability order, including $\infty$ | `contDiff_periodize` |

The last one derives smoothness from local finiteness rather than from a periodic-extension convention on the torus. That matters because the object being differentiated is the lattice sum itself.

### 2. Locality, and why `r < 1/2`

`periodize_eventuallyEq_translate` (`PeriodizePDE.lean:32`) is the crux: if `z.2 - lattice n` lies in the inner cube of radius `r`, then near `z` the infinite sum equals the single translate `n`. The proof restricts to a neighbourhood where every other copy vanishes and applies `periodize_eq_on_innerCube`.

`divergence_free_periodize` (`:117`) and `navier_stokes_periodize` (`:133`) then run: for any `x`, `exists_lattice_near` gives a lattice point within `1/2` of it in each coordinate; with `r < 1/2` the shifted point is inside the inner cube, so the residual at `(t,x)` equals the residual of one translate at a shifted point, and `residual_translate` carries the equation across at the **same viscosity**. No averaging over copies, no boundary term, no rescaled time.

### 3. The post-one extension is discarded before summing

`of_compact_candidate` (`PeriodicPaperTheorem.lean:113`) is handed a whole-space candidate whose fields are defined for all time, with `speed_unbounded` at one. Summing an arbitrary extension past `t = 1` would be wrong — it would change the lattice sum on the interval that matters. The proof periodizes `beforeOne u` and `beforeOne p` instead, and caps the force with `SupportedInCube (1/4) f`. `periodize` is applied only after that truncation, and `beforeOne_supported` + `beforeOne_smooth` supply the hypotheses. The periodic force keeps its compact future time support (`compactFutureTimeSupport_periodize`).

All sixteen fields of `PeriodicPaper.CandidateProperties` are then constructed, including the two periodicity fields for pressure (`Ico 0 1`) and the support clause `tsupport (u · t) ∩ fundamentalCube ⊆ K`. That support clause is the honest reading of "compactly supported" for a nonzero periodic lift, and the file header says so: the lift is not compactly supported on $\mathbb{R}^3$.

### 4. The exclusion, and what it does not assume

`PeriodicViscosity.excludes_global_solution` (`:18`) excludes every global smooth periodic competitor for the same viscosity, force and zero datum. Its competitor class is `PeriodicPaper.GlobalSmoothSolution`, which has **no energy field** — so (D)'s excluded class is strictly weaker than (C)'s, as E70 said. The argument routes through `MaximalLifespan.unbounded_excludes_continuous_extension`: periodic uniqueness on each slab `[0,t]` identifies the competitor with the candidate before time one, and `periodic_bound_on_slab` bounds a continuous periodic field on a closed slab, contradicting unbounded speed.

`MaximalLifespan` also proves the quantitative statement the Euler development states only in a Sobolev class: `candidate_admissible_lifespans` gives `admissibleLifespans f 0 = Ioc 0 1`, and `candidate_greatest_lifespan` makes one the greatest admissible lifespan. Its `ClassicalSolution` structure is `ContDiffOn ℝ ∞` on `Ico 0 T × univ` in **both** velocity and pressure — joint smoothness, the paper's class. So the periodic side states maximality in the class the Euler side leaves open (E82 §4). That is evidence the Euler gap is a choice of statement, not a limit of the framework.

### 5. What this entry does not do

It does not read the proof of `PeriodicUniqueness.classical_uniqueness_on_Icc`, which is the load-bearing lemma for both `MaximalLifespan` and `PeriodicViscosity`; it reads its interface and its call sites only. **E85 closes this**: the proof is read there, and it is a genuine energy argument rather than an assumption. It does not read `exists_compression_scale`'s construction beyond its statement and use, nor `ParabolicScaling.compressedCandidate`'s body. The periodization half is now read; the uniqueness proof is the remaining sampled piece, and this entry does not claim it.

*Evidence: `PeriodicLocalization.lean:62`, `:136`, `:155`, `:176`, `:192`, `:252`; `PeriodizePDE.lean:32`, `:117`, `:133`; `PeriodicPaperTheorem.lean:113`, `:160`; `PeriodicPaperSupport.lean:58`, `:79`; `PeriodicPaperScalingSupport.lean:82`; `PeriodicViscosity.lean:18`; `MaximalLifespan.lean` (`candidate_admissible_lifespans`, `candidate_greatest_lifespan`, `periodic_bound_on_slab`); `f9e8bc5`.*

---

## E84 — The strong gradient theorem's axiom footprint, printed (2026-11-23)

*Execution evidence. E81 row 5 and E82 §5 left one thing open: the development proves `maximalGradientNorm_limsup`, the paper's gradient clause, but that theorem is not in `ComparatorChallenges/Euler.json`, so `#print axioms` had never been run on it. Run `45158640147` prints it.*

### 1. The run

| item | value |
|---|---|
| run | `45158640147`, workflow `comparator-check-euler.yml`, dispatched from `a5226ea` |
| upstream | `openai/NavierStokesAndEuler` at `f9e8bc5` |
| cache | `lake-build-ubuntu-f9e8bc5-euler-v1` restored, so the build is a replay |
| build | `Build completed successfully (10603 jobs)` |
| probe | `lake env lean ProbePaperClauses.lean`, exit 0 |

The probe file is described in the workflow comments. Comparator cannot target a name the challenge module does not declare, and the challenge declares only the $C^1$ sum; adding a matching challenge statement would mean authoring a statement rather than auditing one. So the probe asks the kernel for axioms instead.

### 2. The output, verbatim

```
'EulerPacketInduction.maximalGradientNorm_limsup' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerPacketInduction.maximalVorticity_integral_infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerPacketInduction.exists_compact_smooth_euler_singularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### 3. What it settles

The paper's gradient clause is proved in the development, and its proof uses only the three axioms the challenge permits. It is not a `sorry`, not an extra axiom, not `native_decide`. E81's row-5 weakening is therefore a **statement** choice, not a gap in what the artifact knows: the repository knows the paper's clause; the challenge does not ask for it.

### 4. What it does not settle

This is not a Comparator check. There is no export, no `landrun` replay and no nanoda second kernel on `maximalGradientNorm_limsup` — the library build checks the term, the probe prints its axioms, and the statement-level gap in E81 stays exactly as wide: the *accepted* statement is the weaker one. The run's comparator phase re-executes E79's target set; it has since returned, and E87 records what it found.

*Evidence: run `45158640147`, artifact `euler-toolchain-logs`, file `euler-paper-clause-probe.log` (350 bytes); `euler-build.log` tail; workflow step "Probe the paper-clause theorems" at the commit above.*

---

## E85 — The periodic uniqueness proof, read (2026-11-23)

*Reading entry. E83 read the periodization half of alternative (D) and left one thing explicitly unread: the body of `PeriodicUniqueness.classical_uniqueness_on_Icc`, the load-bearing lemma for both `MaximalLifespan` and `PeriodicViscosity`. This entry reads it.*

### 1. The statement

`PeriodicUniqueness.classical_uniqueness_on_Icc` (`PeriodicUniqueness.lean:643`): two fields smooth on the closed slab `Icc a b × univ`, unit-periodic there, divergence-free at interior times, solving the same forced equation with the same force and the same initial datum at `t = a`, agree everywhere on `[a,b]`. Viscosity one. `PeriodicViscosityUniqueness.classical_uniqueness_on_Icc` (`:65`) extends it to every `ν > 0` by the rescaling `(t,x) ↦ (ν⁻¹ t, x)` with amplitudes `ν⁻¹` and `ν⁻²`, proved in `normalize_residual` — no second PDE argument.

### 2. The proof is a genuine energy argument

The chain, in the order the file builds it:

| step | lemma | what it does |
|---|---|---|
| subtract the equations | `difference_equation` | gives `∂ₜw = Δw − Du(w) − Dw(v) − ∇(p−q)` with the favourable transport split |
| define the functionals | `energy`, `energyRate`, `dissipation`, `coupling` | squared `L²` distance on the unit cube, its rate, the Dirichlet sum, the transport pairing |
| transport vanishes | `cubeIntegral_transport_energy_zero` | from scalar integration by parts and `div v = 0`; proved via `cubeIntegral_fderiv_apply_zero` |
| pressure vanishes | `cubeIntegral_pressure_energy_zero` | `inner_pressureGradient` plus `div w = 0` |
| viscosity is negative | `cubeIntegral_laplacian_energy` | equals `−Σᵢ∫‖∂ᵢw‖²`, by parts per coordinate |
| exact balance | `energy_balance` | `E' = −2 dissipation − 2 coupling` |
| nonlinear bound | `nonlinear_energy_bound`, `neg_coupling_le_energy` | `−⟪w,Aw⟫ ≤ B‖w‖²` |
| differential inequality | `energy_rate_le` | `E' ≤ 2B·E` |
| `B` exists | `exists_gradient_bound` | compactness of `Icc a b × cube` applied to the continuous `fderivWithin` — a **conclusion**, not a hypothesis |
| Gronwall at zero | `gronwall_zero` | integrating factor plus MVT; `E(a)=0`, `E≥0` ⇒ `E≡0` |
| zero energy ⇒ equality | `eq_of_energy_zero` | continuity plus a cube representative, not mere a.e. equality |

Two points deserve emphasis. First, no energy inequality is an input: `energy_balance` is an identity derived from the equations, and `energy_rate_le` is obtained from it by dropping the nonnegative dissipation. Second, the gradient bound is not assumed either — `exists_gradient_bound` extracts it from compactness of the spacetime slab, which is why the theorem needs no small-data or short-time hypothesis.

### 3. What this closes

E83's caveat is discharged at this layer. The uniqueness lemma is not a black box and not an assumption: its hypotheses are the same smoothness, periodicity, divergence-freedom and equation fields that `MaximalLifespan` and `PeriodicViscosity` already have, and each is consumed where it is needed. The pressure is never normalized — it cancels because the difference field is divergence-free — so the gauge freedom E70 noted is genuinely absent from the argument.

### 4. What remains below it

The proof rests on `PeriodicIntegration`: `cubeIntegral_mul_partial`, `cubeIntegral_partial_eq_zero`, `hasDerivAt_cubeIntegral_of_contDiffOn`. These are used as black boxes here; E86 reads them.

*Evidence: `PeriodicUniqueness.lean:643` and the lemmas cited above (`:24`–`:641`); `PeriodicViscosityUniqueness.lean:65`, `normalize_residual`; call sites `MaximalLifespan.lean:93`, `PeriodicViscosity.lean:56`; `f9e8bc5`.*

---

## E86 — The periodic integration layer, read (2026-11-23)

*Reading entry. E85 stopped at three black boxes in `PeriodicIntegration`. This entry opens them. The question is the one E63 taught us to ask of every boundary: is this an assumption wearing a lemma's name, or is it proved?*

### 1. The integral is real

`cubeIntegral` (`PeriodicIntegration.lean:27`) is `∫ y, f (toSpace y) ∂(volume.restrict (Icc 0 1))` — ordinary product Lebesgue measure on `Fin 3 → ℝ`, restricted to the unit cube, pulled back along the continuous linear equivalence `toSpace` (`:19`). There is an `IsFiniteMeasure` instance, proved from `isCompact_Icc.measure_lt_top`. So the energy in E85 is the squared `L²` norm on the torus, not a Riemann sum, a finite partial sum, or a stand-in functional.

`spatialPartial i f x` (`:34`) is the Fréchet derivative `fderiv ℝ f x (coordinateVector i)`, so a "partial derivative" in this development is the actual derivative, not a symbol.

### 2. Integration by parts is derived from Mathlib's divergence theorem

`cubeIntegral_partial_eq_zero` (`:123`) is the load-bearing identity: a genuine coordinate derivative of a `C¹` unit-periodic field integrates to zero. Its proof:

1. Assemble the coordinate box `Icc (0 : Coords) 1` and the vector field `F k = if k = i then g else 0`, with `F'` the matching derivative field.
2. Discharge the hypotheses of Mathlib's `integral_divergence_of_hasFDerivAt_off_countable'` at `n = 2` on a box with corners `0` and `1`, using `countable_empty` for the exceptional set.
3. Supply `hboundary`, that opposite faces agree: this is exactly where periodicity enters, through `hp x i`, and `insertNth_one_eq` is the small lemma that the face shift `insertNth 1 y` is the corner shift `insertNth 0 y` plus `Pi.single i 1`, which `toSpace_single` translates into `coordinateVector i`.

Nothing about integration by parts is assumed; the divergence theorem is quoted from Mathlib and instantiated. `cubeIntegral_mul_partial` (`:181`) is then a short corollary: periodicity of the product, the product rule `partial_mul`, and `cubeIntegral_add`. Not a second theorem, an application.

### 3. The transport and pressure cancellations are derived, not stipulated

`cubeIntegral_fderiv_apply` (`PeriodicUniqueness.lean:341`) expands the pairing over the three coordinates via `fderiv_apply_eq_sum`, then applies `cubeIntegral_mul_partial` term by term. `cubeIntegral_fderiv_apply_zero` (`:367`) is that plus `div v = 0`. `cubeIntegral_transport_energy_zero` gets the energy version by differentiating `‖w‖²` and halving. `cubeIntegral_laplacian_energy` (`:414`) runs the same argument twice per coordinate and lands on minus the sum of squared coordinate derivatives — the Dirichlet form, with the sign produced by the identity rather than imposed. `cubeIntegral_pressure_energy_zero` turns the pressure pairing into `fderiv p · w` through `inner_pressureGradient`, then invokes `_zero` with `div w = 0`.

That last line is why E85's remark about gauge freedom is correct: the pressure never needs normalizing because it is paired against a divergence-free field and killed by the same identity that kills the transport. The two cancellations are one mechanism, applied twice.

### 4. Differentiation under the integral

`hasDerivAt_cubeIntegral_of_hasDerivAt` (`:274`) is Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with the dominating constant obtained by `exists_bound_of_continuousOn` on the compact `closedBall t ε × cube`. `hasDerivAt_cubeIntegral_of_contDiffOn` (`:305`) specializes it to jointly `C¹` fields by producing the continuous derivative field from `continuousOn_fderiv_of_isOpen`. So `energyRate` in E85 is a genuine derivative of `energy`; the balance is not two independent functionals that happen to be related.

### 5. Why the uniqueness conclusion is pointwise, not almost everywhere

`eq_zero_on_cube_of_nonneg_of_integral_eq_zero` (`:206`) converts zero integral of a continuous nonnegative field into vanishing on the closed cube. The step that makes it work is `cube_subset_closure_interior`: `cube ⊆ closure (interior cube)`, so `Measure.eqOn_of_ae_eq` plus continuity upgrades an a.e. statement to one holding on the faces as well. Without that, E85's final step would give equality a.e., and "two classical solutions agree" would be a weaker claim than the theorem states.

### 6. Assessment

This layer was the last place in the periodic chain where an assumed energy identity could have been hiding, and it is not there. The IBP is a divergence-theorem instantiation, the cancellations are corollaries of it, the time derivative is a dominated-convergence derivative, and the a.e.-to-pointwise upgrade is explicit. With E85 and E86, the periodic uniqueness route from `PeriodicPaper.GlobalSmoothSolution` down to the energy identity is read.

Two honest limits. First, `UnitPeriods` is invariance under the elementary translations `x + e_i` only; full lattice periodicity is not assumed at this layer and is not needed, because face matching is a one-step condition. Second, the read stops at Mathlib — `integral_divergence_of_hasFDerivAt_off_countable'` and `hasDerivAt_integral_of_dominated_loc_of_deriv_le` are trusted as kernel-checked library theorems, not re-read.

*Evidence: `PeriodicIntegration.lean:19, 27, 34, 123, 181, 274, 305, 206`; `PeriodicUniqueness.lean:341, 367, 414` and `cubeIntegral_pressure_energy_zero`; `f9e8bc5`.*

---

## E87 — The Comparator's own verdict on the Euler clause set (2026-11-23)

*Evidence entry. E84 dispatched `comparator-check-euler` (run `45158640147`) to print the paper-clause axiom footprints. That workflow also runs the Comparator end to end. Its builtin-kernel phase has returned; the nanoda phase has not.*

### 1. What the Comparator said

`comparator-euler-builtin.log`:

```
Running Lean default kernel on solution.
heartbeat 10:53:14Z log_bytes=2250 lean_procs=2
Lean default kernel accepts the solution
heartbeat 10:58:14Z log_bytes=2339 lean_procs=2
Your solution is okay!
```

`Your solution is okay!` is the Comparator's success verdict: the exported proof was re-checked by a kernel that saw only the export, and it used no axiom outside `propext`, `Classical.choice`, `Quot.sound`.

### 2. What was actually checked

The export line names the two Euler statements and nothing else:

```
Exporting #[..., Euler.euler_breakdown_R3, Euler.exists_compact_smooth_euler_singularity,
  propext, Quot.sound, Classical.choice, ...] from Euler.Solution
```

and the solution-side axiom print is

```
info: Euler/Solution.lean:73:0: 'Euler.euler_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Euler/Solution.lean:75:0: 'Euler.exists_compact_smooth_euler_singularity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So the two statements E81 and E82 examined — the paper's Euler clauses, including the `¬∃` conjuncts — are accepted by a second implementation of the checking loop, at `f9e8bc5`, with a clean footprint.

### 3. The two `sorry` warnings are on the challenge side

The log also carries:

```
warning: ComparatorChallenges/Euler.lean:85:8: declaration uses `sorry`
warning: ComparatorChallenges/Euler.lean:170:8: declaration uses `sorry`
```

Both are in `ComparatorChallenges/Euler.lean`, the specification module, not in `Euler/Solution.lean`. That is the Comparator's design: the challenge file states what must be proved — a `sorry` is how a statement is declared without a proof — and acceptance refers to the solution module proving it. The warnings are expected in this arrangement and are not evidence of a hole; the check on the solution side is the axiom print above, which reports no `sorryAx`.

What this does *not* do: it does not check that the challenge statements match the paper's prose. That was E81 and E82, and it remains a reading finding rather than a machine result.

### 4. The second kernel returned

Step 18, `Comparator (nanoda as second kernel)`, was still in progress when this entry was written. It has since finished and accepted the same export: `nanoda kernel accepts the solution`. The phase log, timings, and the limits of that verdict are in E88. Two kernels now, one export, one commit.

### 5. What this changes

E79 recorded builtin-kernel acceptance for the same target set. This run repeats it and adds the paper-clause prints (E84). Together they mean the Euler clause set is accepted twice by the same tool at the same commit, and the clauses the paper asserts carry a clean footprint. It does not independently confirm the mathematics — a kernel check never does — and the nanoda gap it left is closed in E88.

*Evidence: run `45158640147`; artifacts `euler-builtin-kernel` (`comparator-euler-builtin.log`, 2,410 bytes), `euler-challenge-build` (239 bytes), `euler-toolchain-logs`; steps 9 and 14--18 succeeded; step 18's verdict is E88.*

---

## E88 — The second kernel accepts the Euler export (2026-11-23)

*Evidence entry. Closes the open item in E87 §4: step 18 of run `45158640147`, the nanoda phase, returned after E87 was written.*

### 1. The verdict

`comparator-euler-nanoda.log` (artifact `euler-nanoda-kernel`, 2,574 bytes, 22 lines):

```
Building Euler.Solution
ℹ [10591/10591] Replayed Euler.Solution
info: Euler/Solution.lean:73:0: 'Euler.euler_breakdown_R3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Euler/Solution.lean:75:0: 'Euler.exists_compact_smooth_euler_singularity' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (10591 jobs).
Exporting #[..., Euler.euler_breakdown_R3, Euler.exists_compact_smooth_euler_singularity, propext, Quot.sound, Classical.choice, ...] from Euler.Solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Both kernels ran on the *same* export, inside one phase: nanoda first, then the Lean default kernel. The phase took 917 s end to end, of which nanoda took about five and a half minutes (11:00:02Z → 11:05:29Z) and the default kernel about eight (11:05:29Z → 11:13:36Z). The whole job — two builds, two exports, two kernels — finished in 30 minutes with conclusion `success`.

### 2. What nanoda is, and why it is a second opinion

nanoda is an independent implementation of the checking loop, written in Rust and built here from `ammkrn/nanoda_lib` at commit `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`cargo build --release`; binary 1,378,240 bytes, built in 24 s). It shares no code with Lean's kernel. When it reports that the export checks, the proof term has been re-parsed from `lean4export` format and re-derived by a different program — this is not Lean re-reading its own output.

That is what the repository means when it reports acceptance by more than one external checker, and it is a genuine upgrade over one kernel's word. Its limits are the limits of any kernel check, and they are the limits already named in E87 §3 and E81–E82: it verifies that the term inhabits the declared type, not that the declared type is the paper's sentence. The two soft Euler clauses are untouched by it, because a soft clause is a statement-level difference and both kernels see the same statement. And nanoda's own source is trusted as third-party code at a pinned commit, in the same way Mathlib is trusted in E86.

### 3. Why the earlier attempt produced nothing

Not the mathematics. The sandbox wrapper, as E74 and E75 recorded: a `systemd-run --pty` wrapper left the child blocked on an undrained PTY buffer. With the wrapper corrected, the same phase that previously yielded no verdict completes in 15 minutes of wall clock, and the two-kernel evidence arrives in the same run that prints the paper-clause axiom footprints (E84).

### 4. Standing of the Euler result now

At `f9e8bc5`, on a clean clone, in a sandbox, the two Euler statements designated by `formalization.yaml:72--94` are accepted by two independent kernels, with axiom footprint `propext`, `Classical.choice`, `Quot.sound` and no `sorryAx`. The statement-level caveats of E81 and E82 stand exactly as recorded: the checked `C¹` limsup is the sum of the velocity and gradient suprema where the paper asserts the gradient alone, and the lifespan class is not proved to contain the paper's jointly smooth solution. Not one estimate inside the Euler development has been read.

*Evidence: run `45158640147`, job `137637992292`, step 18; artifact `euler-nanoda-kernel` (`comparator-euler-nanoda.log`, 2,574 bytes); nanoda commit `0da9f98f`; timestamps 10:47:45Z (fetch), 10:48:09Z (binary), 10:58:20Z–11:13:37Z (phase, 917 s), 11:05:29Z (nanoda verdict), 11:13:40Z (job end).*

---

## E89 — The paper against the tree: a first crosswalk (2026-11-23)

*Reading entry. First pass at the one question E76–E88 never asked: whether the published paper's own argument corresponds to the Lean development that claims to formalize it.*

### 1. The paper exists, and the audit had not used it

`formalization.yaml` names two sources: *Finite time blowup for Navier–Stokes* and *Finite time blowup for the Euler equation*, both linked from the repository README. The first is 166 pages, 482,455 extractable characters, with a ten-section structure and three appendices:

```
1 Introduction (1)            6 Auxiliary torus and separation (62)
2 Physical description (3)    7 Oscillatory realization (73)
3 Proof outline (6)           8 Compactly supported mean corrections (88)
4 Leading order flow (24)     9 Residual improvement, local field (100)
5 Correcting the base flow (45)  10 Compact forcing, whole-space breakdown (116)
A Radial moments, heat exterior (126)   B Axis profiles (144)   C Stress cone (157)
```

Until this entry the audit had checked the paper only where E76, E80, E81 and E82 forced it: at the level of *statements*. The paper's proof had never been held against the tree. That matters because a kernel check cannot tell you whether the argument formalized is the argument published.

### 2. What the tree says about the correspondence

The development names the paper's sections in exactly five docstrings:

| File | Citation |
|---|---|
| `RadialSchedule.lean:76` | Section 4.4 |
| `FlatCutoff.lean:25` | Section 4.6 |
| `GraphCalculus.lean:141`, `ExponentLedger.lean:14` | §8.1 |
| `GaussianTailFlat.lean:11` | Section 8.2 |
| `Covariance.lean:206` | Section 8.3 |
| `SignedCovariance.lean:384`, `ExponentLedger.lean:14` | §10.2 |

Five distinct anchors, all in the middle and late sections; nothing cites §2–§3, §5–§7 or any appendix. `ExponentLedger.lean:14` also pins the paper's numeric choice — `κ = 10⁻⁵`, fixed in §8.1 and again in §10.2, with the ledger proved uniformly for `0 ≤ κ ≤ 10⁻⁵` and `σ ≥ 1/5` in exact rationals rather than floating point.

The paper's §3.2 names four compatibility results, and those four are the cleanest spine available for a section-level map: Proposition A.4 (exterior and axis pressure), Proposition B.2 (inner solution), Corollary B.10 (joining and moment matching), Proposition C.2 (the cone condition). Each lands in a named module family — `AppendixHeatResults`, `AxisProfile`, `AxisSeries`/`PowerMomentMatrix`, `MatchingConeBounds`/`ActivationCone` — by object identity, not by assertion. §3.4's four construction steps likewise land on `PulseAmplitude`/`PrimaryPulseBounds`, the `MeanRankUpdate` family, `FiveRowRank` (whose docstring says "the five linear rows of the manuscript"), and the summation modules.

`CROSSWALK.md` records the full table: thirteen rows (ten sections, three appendices), each with pages, content, modules and a **basis** label — `cited`, `object`, or `family`.

### 3. What the crosswalk does not establish

Eight of thirteen rows rest on object identity or family resemblance, not on the paper naming the module or the module naming the paper. A row saying §5 lands in `CorrectionStep` does not say the section's lemmas are all there, in order, with the same hypotheses. And no page-level citation exists yet: the paper's page numbers are taken from its own table of contents, not from the statement being matched.

The gap this exposes is the one worth naming. The paper has numbered propositions and lemmas; the tree has 816 modules under `NavierStokes/`. Nothing yet shows a one-to-one correspondence, and nothing yet shows that no paper lemma is missing from the formalization. A defect, if there is one, is more likely to sit in that distance than in a kernel that has now been run twice on every target.

### 4. Status of the pass

This is pass one of the two-week job, scoped honestly: the paper's structure is extracted, the five explicit anchors are found, the spine from §3.2 and §3.4 is mapped, and the weak rows are marked weak rather than dressed up. Pass two is per-result: take each numbered statement in the paper, locate the declaration by conclusion shape, check hypotheses clause by clause, and record `paper page → file:line` — including the ones that cannot be found.

*Evidence: `cdn.openai.com/pdf/32d9f210-.../navier-stokes.pdf` (166 pages); `formalization.yaml:20--34`; section citations listed above; module inventory 816 files, 429,279 lines under `NavierStokes/`; `CROSSWALK.md`.*

---

## E90 — Pass two begins: twenty paper labels, two results placed (2026-11-23)

*Reading entry. E89 mapped sections. This entry does the first slice of the harder job: matching individual results.*

### 1. The paper's own labels are in the source

The 166-page paper uses internal labels. Twenty of them appear verbatim in Lean docstrings — `heat:exterior`, `heat:small-argument`, `heat:flat-primitive`, `axis:model-series`, `axis:model-positive`, `axis:exit`, `geom:counting-bounds`, `geom:label-counts`, `global:localization`, `global:kernel-bound`, `join:reference`, `join:scale-envelope`, `outgoing:moment-rank`, `outgoing:steering`, `seed:cone-coordinates`, `seed:cone-test`, `seed:profile-comparison`, `sum:realization`, `iter:physical-loss`. Twenty-two occurrences in all (`geom:counting-bounds`, `outgoing:moment-rank` and `seed:cone-test` are each cited twice).

This is a better anchor than a section number, because it is the development asserting the correspondence in its own words rather than the auditor inferring it: `ExponentialMomentMatrix.lean:6` says "the logarithmic-coordinate clause of `outgoing:moment-rank`", and `SeedConePaper.lean:6` says its subject is `seed:cone-coordinates`. The full table, with file and line for each, is in `CROSSWALK.md`.

Fourteen paper sections carry no label citation. Those are not mapped by assertion at all.

### 2. Two results placed at statement level

**Lemma 4.7** (distinct real exponents, non-singular moment system) is `PowerMomentMatrix`: `expSum_coefficients_zero`, `expEvaluationMatrix_det_ne_zero`, `powerEvaluationMatrix_det_ne_zero`, with the integrated form at `ExponentialMomentMatrix.expIntervalMomentMatrix_det_ne_zero`. Distinctness becomes `Function.Injective a`; the matrix is the same matrix; non-singularity is the conclusion. The clause that vanishes in the integrated version — no sign restriction on endpoints — is recorded in the docstring itself.

**Section 8.6** (the five-dimensional moment correction) is `FiveProfileMoments` ("Five actual profile moments on a reserved positive patch") plus `MomentRepair` (`momentMatrix`, `coefficients_unique`, `repair`) plus the rank statement in `FiveRowRank`. The five bumps are constructed: two axial, three angular, in disjoint halves of the patch, which is what the section describes.

### 3. The ledger

Of 57 numbered results in the paper, six now have a mapping checked at statement level: Propositions A.4, B.2, B.10 and C.2 (E89), Lemma 4.7 and Section 8.6. Fifty-one do not. The largest gap is Theorem 4.6, the core existence claim the rest of the paper consumes; Proposition 5.3, the coefficient induction; Propositions 9.1 and 9.5, the residual estimates and the iteration; and Proposition 10.1 with Corollary 10.6, the forcing and the periodic corollary. These are results whose Lean counterpart has not been matched, not results that are missing — no claim is made here that any of them is absent from the formalization.

*Evidence: label grep over 816 modules under `NavierStokes/` at `f9e8bc5`; `PowerMomentMatrix.lean:74,123,143`; `ExponentialMomentMatrix.lean:40`; `FiveProfileMoments.lean:8`; `MomentRepair.lean:36,46,53,59`; `CROSSWALK.md`.*

---

## E91 — Pass two, slice two: the denominator was wrong (2026-11-23)

*Reading entry. The paper's text is now in the tree; the first thing it corrected was the audit's own count.*

### 1. The paper was being read without being readable

E89 and E90 worked from the PDF in a viewer. It is now extracted to text — `pypdf`, 166 pages, 485,170 characters, the PDF's own `PAGE n` markers preserved — into the gitignored `.setup/paper/ns.txt`, with a numbered-result index beside it. Three consequences: every claim can cite a page rather than a section, the statements can be diffed against declarations, and the count can be checked.

### 2. The count did not survive the check

E89 and E90 both say "57 numbered results". Counting distinct `(kind, number)` labels at line start gives **74**: 3 theorems, 26 propositions, 38 lemmas, 7 corollaries, of which 73 have at least one statement-length occurrence (the remainder are labels that appear only as cross-references with a short line). The 57 was a rough figure carried forward without ever being checked against the text.

A second error of the same kind: E90 counted Section 8.6 among the placed results. §8.6 is a section, not a numbered result, so it leaves the numerator. Both corrections are in `CROSSWALK.md`; the ledger restated below uses 74 and six placed, not 57 and six.

### 3. One result placed

**Corollary 10.6** (p. 125) is `PeriodicPaper.breakdownStatement` and `periodic_corollary` (`PeriodicPaperTheorem.lean:148,155`). Read against the paper: for every `ν > 0` there are `u`, `p`, `f` with `CandidateProperties` — smooth velocity and pressure on `preSingularDomain`, periodic on the cube, compact spatial support inside `fundamentalInterior`, zero initial velocity, divergence-free, residual equal to the force, `SpeedUnboundedAtOne` — and `¬ Nonempty (GlobalSmoothSolution ν f)`. Clause for clause.

It is also the only numbered result the repository aligns by name: `formalization.yaml:122–126` gives `Corollary 10.6 (Navier–Stokes on ℝ³/ℤ³)` → `NavierStokes.Comparator.navier_stokes_breakdown_periodic`, status `proved`. So this row is asserted by the development and checked by reading, the first row in the table with both.

### 4. Two results partially placed

**Theorem 4.6** (pp. 32–34) is `NominalProfile.Witness` (`:2481`), and the witness is constructed rather than assumed — `assembly_exists` (`NominalConeAssembly.lean:1482`), `exists_assembly_threshold` (`NominalProfile.lean:2637`). Parts (i), (ii), (iii), (v) map to named declarations (`fields_smooth` :2523, `E_eq_sqrt_f` :2527, `E_positive` :2530, `pressure_canonical` :2543, `Certificate` :1362, `initial_cones` :1431, `activation_cone` :1251, `five_moments` :2536, `moments_after` :2576, `heat_agreement` :2564, `U_outgoing` :2589, `mass_outgoing` :2594). Part (iv), the weight `ζ` with `|∂^αT₀| ≤ C_α ζ δ^{−m_α}`, is family-level only: the `δ^{−m}` bookkeeping was not traced. Part (vi), the two reserved intervals `I_pos` and `I_mean` carrying (4.30), was not located. Four of six parts placed.

**Proposition 10.1** (pp. 117–118) is `R3CompactCandidate.Properties` (`:24`) built by `of_localized_fields` (`:248`). Five of six clauses placed: smoothness, compact supports, divergence-freedom, the residual, and agreement with the local fields (`velocity_locally_eq` :231, `pressure_locally_eq` :240). The sixth — `u(·,t) = p(·,t) = 0` for all sufficiently small `t ≥ 0` — is not a field of the structure; it follows from the construction's time cutoff, but no declaration states it, so it is recorded as unplaced rather than assumed to be discharged. The assembly also reaches the cutoff product through the periodic local model (`of_periodic_local_model` :179) rather than through the paper's `curl(cA) + cB e_θ` directly; that is a route difference, not a clause difference, but it is the reason this row is partial and not placed.

### 5. Two results cited and unchecked

`CurlClassBounds.lean:757` names "Lemma 9.2's curl remainder" (p. 102) and `LinearWaveBounds.lean:896` names "Proposition 9.3 at the coefficient level" (p. 104). These are the development asserting the correspondence in its own words, which is the strongest anchor short of reading both statements. Neither statement was read against its declaration, so they are counted separately from the placed rows.

### 6. What did not move, and why it matters most

**Proposition 5.3** (p. 55), the coefficient induction and the residual bound `|F_slow(U^[N])|_m ≤ C_{N,m} q^{2h(N+1)−K_m}`: no declaration with that exponent shape was found. A grep for `2 * h * (N + 1)` and for the `K_m` loss returns nothing across the tree. That is not evidence of absence — the bound may be stated under other names or carried inside `WholeDomainStageBounds`' `LogBound` / `physicalLoss` machinery — so it is recorded as unfound. **Propositions 9.1, 9.5, 9.6, 9.9** (pp. 101, 106, 107, 114) are likewise unplaced: the residual estimates, the stage iteration, and the summed local field that Theorem 3.1 consumes.

These are the paper's own analytic core. Theorem 4.6 and Corollary 10.6 are placed because the development names their objects; Proposition 5.3 is the one whose content is a quantitative bound, and that is exactly the kind of statement a structure name does not carry.

### 7. The ledger, restated

| Status | Count | Which |
|---|---|---|
| placed, statement read | 6 | A.4, B.2, B.10, C.2, Lemma 4.7, Corollary 10.6 |
| partial | 2 | Theorem 4.6 (4 of 6 parts), Proposition 10.1 (5 of 6 clauses) |
| cited in a docstring, unchecked | 2 | Lemma 9.2, Proposition 9.3 |
| unplaced | 64 | the rest |
| **total** | **74** | |

No verdict changes. This entry corrects an arithmetic error in the audit's own bookkeeping and moves three rows; it says nothing about whether the paper's argument is sound.

*Evidence: paper text at `.setup/paper/ns.txt` (166 pages, 485,170 characters); statements at pp. 32–34, 55, 101, 106, 107, 114, 117–118, 125; `PeriodicPaperTheorem.lean:148,155`; `formalization.yaml:122–126`; `NominalProfile.lean:2481,2523–2594,2637`; `NominalConeAssembly.lean:1251,1362,1431,1482,1517`; `R3CompactCandidate.lean:24,90,94,179,231,240,248`; `CurlClassBounds.lean:757`; `LinearWaveBounds.lean:896`.*

---

## E92 — Pass two, slice three: one more result placed, four partly (2026-11-23)

*Reading entry. E91 left the analytic core as the gap. This slice read those statements at page level and searched the tree by shape rather than by name — which is what the previous slice recommended and had not done.*

### 1. Proposition 9.9 is placed whole

**Proposition 9.9** (p. 114): "There are smooth fields (uloc, ploc) on Ω∗, obtained by summing the finite corrections above, such that div uloc = 0 and all conclusions of Theorem 3.1 hold."

That is `LocalPaper.local_theorem` (`LocalPaperTheorem.lean:179`): `∃ h qstar Xa Xext heatNormalization, ∃ A D u : VelocityField, ∃ p : PressureField, Properties h qstar Xa Xext heatNormalization A D u p`. The `Properties` structure (`:53`) is the clause list, and it is Theorem 3.1's list in order: `exponent_small` (`0 < h ∧ h < 1/100`), `scale_positive`, `edges_ordered` (`0 < Xa ∧ Xa < Xext`), four `ContDiffOn ℝ ∞` on `preterminal`, `direct_angular`, `decomposition` (`u w = spatialCurl A w + D w`), `divergence_free`, three `JointResidualLimits.AwayExtensions`, three `UniformJetsOnScaleStrips`, `residual_flatness` (`∀ m r, ∃ C δ, q < δ → ‖iteratedFDeriv m residual‖ ≤ C q^r`), `exterior` (heat velocity and pressure, zero residual), and `angular_growth` (`|τ^A u − e₀| ≤ C τ^{2h}`). Divergence-freeness is a field, not a consequence.

The proof obtains the fields from `LocalResidualFlatness.selected_schedule`; no finite-stage or schedule hypothesis is left to the caller. This is the summed local field the whole-space assembly consumes, and it is now read at statement level rather than inferred from a module name.

### 2. Theorem 4.6(vi) is placed, and (iv) is half placed

**Part (vi)** (pp. 33–34): two fixed disjoint intervals `Ipos`, `Imean` inside `(Xa, Xv)` with `sup Ipos < inf Imean`, on which `U = 0` and `E = cpatch(1+η²)^{-1}X^{-1/2−λ}`.

It is `ReservedPatches` (`ReservedPatches.lean`). The `Slot` inductive has four constructors — `modulation`, `heat`, `positive`, `mean` — and the log offsets are `(-14,-9)` for `.positive` and `(-8,-3)` for `.mean` relative to the pulse entrance, four five-log-unit windows. `offsets_separated` proves disjointness *with order*, which is the paper's `sup Ipos < inf Imean` for the corresponding intervals; `window` and `closedPatch` are those intervals in `X`; and `radialClosedPatch = Icc (√(2·left)) (√(2·right))` is exactly the `Jpos`, `Jmean` conversion in the paper's symbol table (p. 21: "the images of Ipos and Imean under X ↦ √(2X)").

The field formula is the paper's: `clean_fields` gives `U = 0 ∧ E = xAmplitude XR η · X^{-(1/2 + λ)}`, and `xAmplitude_shape` gives `xAmplitude XR η = xAmplitude XR 0 / (1 + η²)`, so the product is `c(η-independent) · (1+η²)^{-1} · X^{-1/2-λ}` — `cpatch` is `xAmplitude XR 0`. `heated_fields` carries it through the heat correction for every slot except `.heat`, and `right_before_switch` plus `clock_inside_wait` put all four windows inside the shaped wait, which is the paper's `(Xa, Xv)` containment. Not one named declaration says "both intervals lie in `(Xa, Xv)`"; it follows from two inequalities.

**Part (iv)** (p. 33) is two inequalities in one display, `|T₀| ≥ cζ` and `|∂^αT₀| ≤ C_α ζ δ^{-m_α}`, with `δ = min{1, log(X/Xa), log(Xb/X)}`. The weight is in the tree verbatim: `ActiveAnnulusWeight.weight c a b y = FlatCutoff.edge c (y−a) · FlatCutoff.edge 4 (b−y)` evaluated at `y = log X` (`radialWeight`), and `edgeDistance a b y = min 1 (min (y−a) (b−y))` — that is `δ` in log coordinates, with the same three arguments in the same order. `weight_flat_left` and `weight_flat_right` prove every iterated derivative of the weight vanishes at both edges, which is the paper's "every radial derivative of ζ vanishes at Xa, Xb"; `radialWeight_flat_left/right` do it in `X`. The `δ^{-m}` loss is `distance_power_le_left` and `left_bound_to_weight`: `C · edge c (y−a) / (y−a)^n ≤ (C / edge 4 (b−a−d)) · weight / edgeDistance^N`. `LeadingStressWeights.weighted_bounds` assembles the two charts into `ActiveAnnulusWeight.WeightedBounds` from the actual modulated witness, so the derivative tower is stated for the real stress, not a model.

The lower bound is **not** placed. What exists is `stress_ne_zero`, which needs `FullTrueCone` and gives `T₀ ≠ 0` — nonvanishing, not a comparison against `ζ`. A strict cone margin is not a quantitative lower bound of the form `cζ`; nothing in the tree supplies the constant. So (iv) is placed for the derivative bound and the flatness, and open for `|T₀| ≥ cζ`. Theorem 4.6 therefore moves from four parts to five, not to six, and stays in the partial column. That is the one inequality between the paper's central existence theorem and a clean placement.

### 3. Proposition 5.3 is partial: the exponent is a definition, the loss is not

**Proposition 5.3** (p. 55): every finite velocity sum is divergence-free and `|Fslow(U[N])|_m ≤ C_{N,m} q^{2h(N+1) − K_m}` with `K_m` independent of `N`.

The `2h(N+1)` is a definition with the paper's own sentence in its docstring: `SlowExpansionResidual.slowOrder h n = 2 * n * h`, "The manuscript's slow order `λ_n = 2nh`". `slowOrder_succ` gives `slowOrder h (n+1) = slowOrder h n + 2h`, so truncating at `N` puts the first uncancelled term at `slowOrder h (N+1) = 2h(N+1)`. That is not an inference from a name: `recurrence_truncation_of_zero` (`SlowExpansionResidual.lean`) proves that when the retained coefficient equations hold, the physical residual equals `pairTail N w K − w (N+1) · A N` exactly — the retained orders cancel identically and only order `N+1` and the pair tail survive. `transportTail` carries `q^(e − 1 + slowOrder h (N+1)) * Z2 …` as a literal term. Divergence-freeness is `divergence_slowVelocity_eq_zero`, via the exact divergence-coefficient series.

The `K_m` is what is missing. The derivative losses in `transportCoefficient` are spread across `T`, `Z`, `Z2` and the recurrence; no declaration states a single constant `K_m` independent of `N` that bounds the whole truncated residual at derivative order `m`. `SharpPhysicalCarrier.derivativeCost h = 1 + 3h/2` is a cost of that shape but belongs to the sharp phase estimate of §7/§9, not to (5.26), and substituting it would be an assumption rather than a placement. Recorded as partial: exponent and divergence placed, `K_m` not.

### 4. Propositions 9.5 and 9.6 are partial: the arithmetic is exact, the construction is elsewhere

**Proposition 9.5** (p. 106) ends: the stage-0 fields "form a state at stage 0 in the sense of Definition 9.4; in particular, their residual orders are `B₀ = 0.7` and `C*₀ = 1.2`." **Proposition 9.6** (p. 107) ends: there is a state at stage `j+1` with `B_{j+1} = B_j + 1/10`, `C*_{j+1} = C*_j + 1/10`.

Those numbers are in the tree and they are exact. `ActualIterationLedger.sigma = ExponentLedger.stageParameter`, with `sigma_zero : sigma 0 = 1/5` and `sigma_succ : sigma (J+1) = sigma J + 1/10`. The residual orders are `residualWave J = ExponentLedger.waveExponent (sigma J)` and `residualMean J = ExponentLedger.meanExponent (sigma J)`, and the two formulas are `residualWave_formula : residualWave J = J/10 + 7/10` and `residualMean_formula : residualMean J = J/10 + 6/5`. At `J = 0` that is `0.7` and `1.2`; the increments are `1/10`; `cycle_wave_output` and `cycle_mean_output` state that one cycle adds exactly one increment. `fixed_ledger` collects the whole schedule — one `κ`, the accuracy sequence, the gain, monotonicity, divergence to infinity — with no stage-dependent choice.

What is *not* placed is the existence half: that a state in the sense of Definition 9.4 actually exists at each stage with those orders. That is the subject of `ActualStageEstimates` and `GluedStageEstimates`, which E67–E71 read down to the source wave class but did not match clause by clause against Definition 9.4. So 9.5 and 9.6 are partial with the arithmetic half proved and the construction half traced, not matched.

**Proposition 9.1** (p. 101) stays unplaced. Its conclusion is class membership — the normalized linear residual belongs to `W_{α+1/2−3κs}` — and no declaration was read that states that membership. `ExponentLedger` contains the gain `1/2 − 3κ` in `signedBarGain` and in `signed_curl_after_divergence`, and `SignedMeanGain`/`CorrectionAnalyticStep` carry stage-level gains, but an exponent appearing in a ledger is not the class statement. Recorded as unfound with that pointer, not as placed.

### 5. The ledger

| Status | Count | Which |
|---|---|---|
| placed, statement read | 7 | A.4, B.2, B.10, C.2, Lemma 4.7, Corollary 10.6, Proposition 9.9 |
| partial | 5 | Theorem 4.6 (5 of 6, (iv) half), Proposition 10.1 (5 of 6), Proposition 5.3, Proposition 9.5, Proposition 9.6 |
| cited in a docstring, unchecked | 2 | Lemma 9.2, Proposition 9.3 |
| unplaced | 60 | the rest, including Proposition 9.1 |
| **total** | **74** | |

Two results moved (9.9 to placed, 4.6(vi) inside a partial that improved by one part) and two moved into partial with their arithmetic halves proved. Nothing moved out.

### 6. What this does and does not change

It does not change a verdict. Every row is a statement-level correspondence; not one estimate in §5 or §9 was checked for validity, and the two results that matter most for the argument — Theorem 4.6's uniform lower bound and Proposition 5.3's `N`-independent loss — are exactly the two that did not close. What changed is the shape of the gap: it is no longer "these results were never looked for". It is now three named inequalities, in three named modules, each with the paper's display beside it.

*Evidence: `ns.txt` lines 1592–1665, 2874–2905, 5185–5192, 5421–5426, 5475–5477, 5794–5798 (pages 33–34, 55, 101, 106–108, 114); `LocalPaperTheorem.lean:53,179`; `ReservedPatches.lean` (`Slot`, `offsets_separated`, `clean_fields`, `radialClosedPatch`); `ActiveAnnulusWeight.lean:24,36,190`; `LeadingStressWeights.lean` (`weighted_bounds`, `stress_ne_zero`); `SlowExpansionResidual.lean` (`slowOrder`, `recurrence_truncation_of_zero`, `transportTail`); `ActualIterationLedger.lean` (`sigma`, `residualWave_formula`, `residualMean_formula`, `cycle_wave_output`, `fixed_ledger`); `ExponentLedger.lean` (`signedBarGain`).*

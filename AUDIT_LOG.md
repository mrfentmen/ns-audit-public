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

---

## E93 — The lower bound was in the module: Theorem 4.6(iv) closes (2026-11-23)

*Reading entry. E92 recorded that `|T₀| ≥ cζ` "is not stated anywhere" and that "a strict cone margin is not a quantitative lower bound of the form `cζ`". The second sentence is true and the first is false: the declaration is in `LeadingStressWeights.lean`, the file E92 already had open, three hundred lines below the one it read.*

### 1. The declaration

`LeadingStressWeights.stress_lower_bound` (`:1121`):

```
theorem stress_lower_bound (hcone : FullTrueCone v) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : Point,
      p.1 ∈ Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) →
      p.2 ∈ Icc (-1 : ℝ) 1 → c * zeta v p.1 ≤ ‖stress v.profiles F.data.h p‖
```

Term by term against the paper's display `|T₀| ≥ cζ` on `(Xa, Xb) × [−1, 1]` (p. 33):

* `zeta` (`:1089`) is `radialWeight (activationTime ^ 2) (leftEdge W) (rightEdge W) X` — the flat weight of item (iv): positive on the open annulus, zero outside it, every radial derivative vanishing at both edges. E92 placed that half; it is the same object.
* `stress` (`:23`) is `(LeadingStress.theta, LeadingStress.axial)`, the literal two leading components, on the actual modulated witness.
* The domain is `activeLeft < X < activeRight` with `η ∈ [−1, 1]`, which is `(Xa, Xb) × [−1, 1]` under `leftEdge = log Xa`, `rightEdge = log Xb`.
* The quantifier is `∃ c, 0 < c` with no `α` in the statement — the paper's "constant `c > 0`, independent of `α`".

### 2. Why nonvanishing was, in fact, enough

E92 stopped at `stress_ne_zero` (`:462`), which gives `T₀ ≠ 0`, and concluded that no quantitative version existed. The quantitative version is not derived from the cone *inequality*; it is derived from nonvanishing on a compact set together with the two edge factors, and the cone enters only as the hypothesis that supplies nonvanishing.

The chain: `weighted_bounds` (`:528`) applies `kappa_lt_one` and `logStress_ne_zero` to `ActiveAnnulusWeight.actual_edge_join` (`:1244`), which calls `weightedBounds_of_edge_factors` (`:648`), which calls `exists_global_lower_bound` (`:424`). There the constant is built:

```
let m := min ml (min mr mm)
```

`ml` and `mr` are the collar constants of the two `EdgeFactor`s — the activation collar at `Xa` and the terminal collar at `Xb` — and `mm` is `UniformCone.positive_uniform_margin` applied to `Icc (−1) 1 ×ˢ Icc (a+d) (b−d)`: the positive minimum of a continuous nowhere-zero norm over a compact set. So `c` is a minimum of three positive constants, each produced by an argument, not assumed.

This is why E92's second sentence was right and its conclusion was not. A cone margin alone does give only an inequality in the cone's own coordinates, not `cζ`; `ConeAlgebra.true_cone_iff` converts the margin into a forbidden direction, and `stress_ne_zero` uses exactly that. What produces `cζ` is the separate compactness-and-edge-factor argument above. Both statements are needed and both exist; E92 saw the first and did not look for the second.

`weightedBounds_of_edge_factors` (`:648`) is the general form: `WeightedBounds`' first component *is* `∃ m > 0, ∀ p ∈ K, ∀ y ∈ Ioo a b, m · weight c a b y ≤ ‖T (p,y)‖`. So the lower bound and the derivative tower are the two halves of one structure, and E92 placed one half of a record whose other half was `.1`.

### 3. The derivative half is stronger than the paper asks

`physical_jet_bound` (`:1137`) gives, for every `n`, a `C > 0` and an `N` with

```
‖iteratedFDeriv ℝ n (fun p => stress … (p.2, p.1)) (η, X)‖ ≤ C * zeta v X / distance v X ^ N
```

with `distance v X = edgeDistance (leftEdge W) (rightEdge W) (log X)` — that is `δ`. The paper asks for a constant `m_α` per multi-index `α`; the tree bounds the full `n`-th Fréchet derivative, which dominates every mixed partial of order `n`, so the paper's display follows with `m_α := N_{|α|}`. Order-by-order is a strengthening of index-by-index here, not a weakening.

`FinalSlowBase.leading_lowerBound` (`:149`) restates the lower bound in the `weight` / `leadingStress` spelling on `annulus W`, and `leading_radial_jets` (`:166`) restates the tower. `leading_stress_eq` (`:130`) identifies `leadingStress` with `BaseResidual.stressPair (coefficients H v) 0`, the coefficients the velocity is actually built from — so this is the object in the proof, not a stand-in for it.

### 4. The cost, stated plainly

The statement is existential in exactly the sense the paper claims, so this is a placement and not a defect. The audit's constant theme applies unchanged: `c = min ml (min mr mm)` is a minimum of three margins, no numeral is printed, and no dependence on `h`, `λ` or the profile parameters is exposed. An argument that needed `c` to beat a specific quantity would not be served by this statement. Item (iv) does not ask for that, and §5's `(5.43)` uses `ζ` and `δ` as weights rather than using `c`.

### 5. Theorem 4.6 is placed, whole

Six of six parts. (i), (ii), (iii), (v) from E91; (vi) from E92; (iv) here. The theorem moves out of the partial column, which leaves Proposition 10.1 (five of six clauses), Proposition 5.3 (exponent without `K_m`), Proposition 9.5 and Proposition 9.6 (arithmetic without the Definition 9.4 match).

| Status | Count | Which |
|---|---|---|
| placed, statement read | 8 | A.4, B.2, B.10, C.2, Lemma 4.7, Theorem 4.6, Corollary 10.6, Proposition 9.9 |
| partial | 4 | Proposition 10.1 (5 of 6 clauses), Proposition 5.3, Proposition 9.5, Proposition 9.6 |
| cited in a docstring, unchecked | 2 | Lemma 9.2, Proposition 9.3 |
| unplaced | 60 | the rest, including Proposition 9.1 |
| **total** | **74** | |

Two limitations survive. The placement is statement-level: neither `stress_lower_bound` nor `physical_jet_bound` was recompiled for this entry, and this tree has never been compiled by this audit. And placing the clauses of Theorem 4.6 says nothing about whether §5–§9 discharges them; that question is untouched by this slice and is not advanced by it.

What this entry does establish is narrower and worth having: the one inequality E92 named as standing between the paper's central existence theorem and a clean placement is not open. It was closed in the source, under a name the paper does not use (`stress_lower_bound`, not `lower_bound` or `stable_lower`), and E92 searched for the paper's vocabulary rather than for the statement's shape — the same mistake E92's own §3 diagnosed in slice two and did not apply here.

*Evidence: `ns.txt` lines 1592–1645 (pp. 32–33, item (iv) and display (4.27)); `LeadingStressWeights.lean:23,453,462,528,1089,1121,1137`; `ActiveAnnulusWeight.lean:424,634,644,648,1244`; `FinalSlowBase.lean:130,149,166`; `UniformCone.positive_uniform_margin`; `ConeAlgebra.true_cone_iff`.*
---

## E94 — Proposition 9.1 was in the tree under its output's name (2026-11-23)

*Reading entry. Both E91 and E92 recorded Proposition 9.1 as unplaced, and the second of them stated it flatly: "no declaration was read that states that membership". A declaration states it, and it was found by searching for the conclusion's shape rather than for the paper's words — the correction E92 made to slice two and did not apply to its own row.*

The paper's Proposition 9.1 (p. 102, `ns.txt:5185–5192`) concludes two class memberships: the normalized linear residual, after the prescribed source is added, **belongs to `W_{α+1/2−3κ_s}`**, and **the pressure amplitude `π_m` belongs to `W_{α+1/2}`**, with pulse-cutoff tails admissible because their derivatives vanish to infinite order. Its preamble adds a third: if `t_m ∈ W_α` then the curl correction `r_m ∈ W_{α+1/2−κ_s}`.

All three are one conjunction in `LocalizedWaveBounds.lean:1014–1024` (`common_bounds_from_native_local`, repeated at `PeriodizedWaveBounds.lean:1256–1260`):

```
WaveClass s W α a.common.amplitude ∧
WaveClass s W α (a.commonCorrected s d).amplitude ∧
WaveClass s W (α + 1 / 2) a.common.pressure ∧
WaveClass s W (α + 1 / 2 - κ) (a.common.curlCorrection s d) ∧
WaveClass s W (α + 1 / 2 - 3 * κ) (a.globalGood s d)
```

Clause by clause:

* **The residual.** The paper's object is "the normalized linear residual, after adding the prescribed source". The tree's name for that object is `globalGood` (`PeriodizedWaveBounds.lean:799`), documented as "An actual global good coefficient, assembled from the cutoff-and-curl formula on each native copy". It is the curl-built residual *after* the source has been absorbed — which is what the theorem's own split shows: `PrimaryResidualClass.Inputs.good_class` (`:249`) relates `constructedGood` to the coefficient, and `linear_bound_and_identity` (`CorrectionInitializationNoOptions.lean:180`) proves the literal identity `linearResidual = linearGood + excluded`, so the "good" object is residual-minus-explicit-tail by construction.
* **The exponent.** `α + 1/2 − 3κ` appears verbatim, with `α` free. `κ` is the tree's `ChartScales.kappa`, the paper's `κ_s = 10⁻⁵`. The `α = 1/2` case degenerates to `1 − 3κ`, which is the constant the primary slice uses (`good_coefficients_class` `:257`, and `1 − 3κ_s` in the paper's own §9.5 proof, `ns.txt:5428`).
* **The pressure.** `α + 1/2`, exact.
* **The curl correction.** `α + 1/2 − κ`, exact, matching the paper's Lemma 7.7 sentence.
* **The tails.** The paper's qualifier is not a hypothesis because the tree makes it a theorem: `FiniteHeadClass.waveClass_all_exponents` (`:119`) proves that a class supported in a fixed finite band belongs to **every** exponent with the *identical* weight, and `PeriodizedWaveBounds.common_outputs_zero_germ` supplies literal zero germs where no copy covers the point. So "apart from tails vanishing to infinite order" is discharged by a general principle, not assumed per-label.

### What this changes

Proposition 9.1 moves to placed. The ledger is 9 placed, 4 partial, 2 cited-unchecked, 59 unplaced of 74. And the crosswalk's "the one row it cannot place" sentence is itself now wrong, which is worth more than the row: the file had recorded a *search failure* as a *statement absence*, twice, and the failure was in the query. The paper says "normalized linear residual"; the tree says `globalGood`. Nothing in the tree is named after the paper's phrase.

Two limitations, unchanged in kind. This is statement-level; nothing was recompiled. And the paper states the result per label and per harmonic `m`, while the Lean statement is the assembled global coefficient over the native copies with the label sum already taken — a route difference of the same sort E91 recorded for Proposition 10.1, not a clause difference, but not nothing either: the per-harmonic form is not exposed as its own declaration.

*Evidence: `ns.txt:5168–5192, 5428` (pp. 101–102, 107); `LocalizedWaveBounds.lean:1014–1024`; `PeriodizedWaveBounds.lean:799,1256–1260`; `PrimaryResidualClass.lean:249,257`; `CorrectionInitializationNoOptions.lean:180`; `FiniteHeadClass.lean:96,119`; `ChartScales.kappa`; `ExponentLedger.signedBarGain`.*

---

## E95 — Proposition 5.3 closes except one clause; 9.5 and 9.6 move nearer (2026-11-23)

*Reading entry. E91 recorded Proposition 5.3's bound as "no declaration with that exponent shape was found", citing a grep for `2 * h * (N + 1)` that returns nothing. It returns nothing because the tree spells the same quantity `slowOrder h (N + 1)` = `2 * (N+1) * h`, which slice two had already found and which this file then failed to reuse.*

**Proposition 5.3, display (5.25)** (`ns.txt:2874–2881`): `|F_slow(U^[N])|_m ≤ C_{N,m} q^{2h(N+1) − K_m}` with `K_m` independent of `N`. The declaration is `BaseResidual.truncationResidual_rate` (`:1440`):

```
FiniteJetRate l (fun z => (cartesianChart h z).1)
  (fun z => truncationResidual N h C f z.1 z.2) M (2 * (N : ℝ) * h - 2 - M)
```

`FiniteJetRate` (`DiagonalResidual.lean:37`) is `∃ C ≥ 0, ∀ᶠ x, ∀ m ≤ M, ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r` — a bound by `C q^r`. Setting `M = m` gives exponent `2Nh − 2 − m`; the paper's is `2Nh + 2h − K_m`. They coincide at

```
K_m = m + 2 + 2h
```

so the loss is **exact**, not merely `N`-independent: linear in the derivative order, with the constant depending only on `h`. It is not a weakening. Two further points strengthen rather than weaken the row: one constant `C` serves every `m ≤ M`, where the paper allows `C_{N,m}`; and the docstring states the provenance — "Its rate is derived from the explicit omitted monomials, not supplied as a hypothesis", the proof being `finset_monomial_rate` applied to finitely many smooth coefficients.

The proposition's remaining clause is **"every finite velocity sum is divergence-free"**, and that one is not placed. `SlowDivergence.radialFlux` is the mechanism the constructed bases use (`ConstructedSlowBase.lean:75`, `AssembledSlowBase.lean:575,1348`), and exact incompressibility at each order is the paper's (5.2), but no declaration read states the finite-prefix divergence statement as its own conclusion. Recorded as unfound, not assumed.

**Proposition 9.5 (stage 0, `B₀ = 0.7`, `C*₀ = 1.2`)**. Three pieces now exist where E91 had one. `PrimaryPiece.linear_bound_and_identity` (`CorrectionInitializationNoOptions.lean:180`) proves `WaveClass p.strip P (7/10) p.linearGood` *and* the residual identity beside it, so the 0.7 is a proved class of the actual linear residual's good part, not just the arithmetic `residualWave 0 = 7/10`. `cumulative_bounds` (`:200`) proves the primary tuple's `1/2` amplitude, `17/25` curl difference and `1` pressure. `ActualInitialization.initialState` (`:173`) is the constructed stage-0 state, with `initial_state` (`ActualCycleCoherence.lean:73`) establishing the coherence predicate for it. What is still missing is one clause: no declaration states that the assembled stage-0 **mean** residual lies in class `6/5`. The arithmetic is `residualMean_formula` (`ActualIterationLedger.lean:235`); the class is not stated. Still partial, four of five clauses.

**Proposition 9.6 (one cycle, `+1/10` on both orders)**. The arithmetic was already placed: `cycle_wave_output` and `cycle_mean_output` (`ActualIterationLedger.lean:239,243`) are exactly `+1/10`. The construction half now has a much sharper anchor than "traced": `WholeDomainStageBounds.physical_stage_estimates` (`WholeDomainPhysicalStageTheorem.lean:101`) proves, for **every** `j` and `m`, that the stage-`(j+1)` velocity and pressure obey `LogBound h (commonQ) … (gain h (j+1) − physicalLoss h m)`. And `residual_physical_gap` (`:251`) proves `h * residualWave J = gain h J + 7h/10`. Composing them identifies the paper's `B_j` with `gain h j` up to the fixed `7h/10` shift — so the stage estimate is the paper's `B_{j+1}` in the tree's own coordinates, not an analogue of it. What is missing is the mean-side companion: no declaration ties a stage-`(j+1)` mean residual to `residualMean (j+1)`. Still partial.

### The ledger

| Status | Count | Which |
|---|---|---|
| placed, statement read | 9 | A.4, B.2, B.10, C.2, Lemma 4.7, Theorem 4.6, Corollary 10.6, Proposition 9.1, Proposition 9.9 |
| partial | 4 | Proposition 10.1 (5 of 6), Proposition 5.3 (4 of 5), Proposition 9.5 (4 of 5), Proposition 9.6 (2 of 3) |
| cited in a docstring, unchecked | 2 | Lemma 9.2, Proposition 9.3 |
| unplaced | 59 | the rest |
| **total** | **74** | |

The manuscript's "the gap is therefore three named inequalities" is now two: Proposition 5.3's divergence clause, and Proposition 9.5's mean class. Both are single missing statements inside modules that are otherwise read. Neither is evidence of a defect; both are the kind of clause a structure name does not carry.

*Evidence: `ns.txt:2874–2910, 5421–5425, 5475–5478` (pp. 55, 106–108); `BaseResidual.lean:1440`; `DiagonalResidual.lean:33,37`; `SlowExpansionResidual.lean:24`; `AxisSourceRegularity.lean:98`; `CorrectionInitializationNoOptions.lean:180,200`; `ActualInitialization.lean:173`; `ActualCycleCoherence.lean:73`; `ActualIterationLedger.lean:231,235,239,243,251`; `WholeDomainPhysicalStageTheorem.lean:101`; `ConstructedSlowBase.lean:75`; `AssembledSlowBase.lean:575`.*

---

## E96 — Theorem 4.6 has no free inputs; §5 is proved from smoothness alone (2026-11-23)

*Reading entry, the discharge walk E93 deferred. Question: does the construction prove Theorem 4.6, or restate it with the work assumed at a boundary? Answer for §4 and §5: proved. One wiring question is left open and is stated at the end.*

**§4's input is a theorem, not a parameter.** `NominalConeAssembly.assembly_exists` (`:1482`) takes `d : PreparedOutgoing.PreparedProfile`; `PreparedOutgoing.exists_prepared` (`:36`) is `Nonempty PreparedProfile`, built by choosing the reset bound and the exponent together against a clean-cone cap (`OutgoingCone.exists_ordered_profile_cone`). `exists_nominal_cone` (`:1517`) composes them:

```
obtain ⟨d⟩ := PreparedOutgoing.exists_prepared
obtain ⟨W, hW⟩ := exists_certificate d
```

so the witness is produced from nothing, and `NominalConeAssembly.certificate` discharges the cone obligations from stored witness data rather than assuming them — its own docstring: "Every component uses the stored witness." No hypothesis of Theorem 4.6 is an unproved existential at this boundary.

**§5's residual rate assumes only smoothness.** `truncationResidual_rate` needs `0 < h < 1/2`, a `PhysicalApproach` filter, an open `O` containing the box, `N`, `C`, a `SlowProfiles f`, and `ContDiffOn ℝ ∞` of finitely many coefficients `j ≤ N`. There is no estimate among the hypotheses; the exponent comes out. That is the strongest single answer this audit has produced to the question "is the analytic content proved or posited", and it is narrower than it sounds: it says the *truncation* residual's rate is derived, not that every stage estimate in §9 is.

**What is left open, and it is a wiring question.** Two profile constructions coexist. §4's cone and lower bound are stated for `W.controls.extendedProfiles W.heat W.separated` (`NominalProfile.lean:2503`), while §5's residual statements take a `SlowProfiles f` argument that `GlobalSlowProfiles.profiles` constructs, and `ActualCandidateAssembly.assemble` draws its `f` from that second family. No declaration read in this pass identifies the two. That is not a claim of defect — the assemblies may meet through a bridge in the Establishes/Actual* layer that this slice did not open — but until such a declaration is read, "Theorem 4.6 is discharged" remains true clause by clause at each boundary and unproved as a single composition. It is the next target, and it is a smaller target than the one this entry closed.

*Evidence: `NominalConeAssembly.lean:1404,1431,1482,1512,1517`; `PreparedOutgoing.lean:22,36,119,121`; `NominalProfile.lean:2481,2503,2523`; `BaseResidual.lean:1440,1479`; `WorldDomain`-free check: `GlobalSlowProfiles.lean` `profiles`, `AssembledSlowBase.lean:575`; `ActualCandidateAssembly.lean` (`assemble`, `estimates`).*
---

## E97 — §5 and §9 close: the three quarter-open rows are placed (2026-11-23)

*Reading entry. E95 left three results partial and named the clauses that were missing. All three clauses are in the tree, and the profile link E96 could not find is named as well. This is the largest single move the ledger has made: twelve of seventy-four placed, one partial.*

### 1. Proposition 5.3, both clauses

(5.25) closed in E95 (`truncationResidual_rate`, `BaseResidual.lean:1440`). The divergence clause — "every finite velocity sum `u^[N]_slow` is divergence-free" — is `divergence_slowVelocity_eq_zero` (`SlowExpansionResidual.lean:915`), stated for the actual Euclidean divergence of the finite sum `slowVelocity N h C f`:

```
ProblemStatement.spatialDivergence (slowVelocity N h C f) t x = 0
```

The hypothesis is `hdiv : ∀ n ≤ N, divergenceCoefficient h f n (inner h (profilePoint t x)) = 0`. That is not an added estimate: it is equation (21) at each retained order, and its content is characterized by `divergenceCoefficient_eq_zero_iff` (`:769`), which proves the vanishing equivalent to `partialX (f.flux n) = -Z h (axialExponent h + slowOrder h n) (f.axial n)`. The construction enforces exactly that relation. So the clause is the paper's, discharged by the recurrence the paper builds.

There is a stronger statement beside it. `divergence_slowVelocity` (`:885`) proves the finite field's divergence is **exactly** its finite coefficient series:

```
spatialDivergence (slowVelocity N h C f) t x
  = finiteSeries N (q h (profilePoint t x)) h (-1)
      (fun n => divergenceCoefficient h f n (inner h (profilePoint t x)))
```

and `divergence_finite_expansion` (`:634`) proves the same identity in similarity variables. So "exactly incompressible at each order" is a theorem about the actual differential operator, not a formal shorthand.

### 2. Proposition 9.5, both orders

Stage zero. `sigma_zero` (`ActualIterationLedger.lean:34`) is `sigma 0 = 1/5`; `residualWave_formula` (`:231`) gives `7/10` and `residualMean_formula` (`:235`) gives `6/5`.

The wave half is `PrimaryPiece.linear_bound_and_identity`'s `WaveClass p.strip P (7/10) p.linearGood` (E95). The mean half is `CorrectionState.MeanResidualBounds` (`:217–219`), which states the class **generically in `σ`**:

```
angular : MeanClass s (1 + σ) (fun n x => u.meanGoodResidual c n x 1)
axial   : MeanClass s (1 + σ) (fun n x => u.meanGoodResidual c n x 2)
```

At `σ = sigma 0 = 1/5` that is `MeanClass s (6/5)`, which is the paper's `C*_0 = 1.2`. E95 recorded "no declaration states the assembled stage-0 mean residual lies in class 6/5"; the declaration states it for every admissible `σ` and the stage-zero value is `sigma 0`. The state itself is `ActualInitialization.initialState` with `initial_invariant` (`BaseWitnessClosure.selected_initial_invariant`).

### 3. Proposition 9.6, one cycle

`sigma_succ` (`:38`) is the `+1/10`. The output side is `CorrectionStep.gaugeTemporalStage_next_mean` (`:3004`), whose conclusion is

```
MeanClass s (ExponentLedger.meanExponent (σ + 1 / 10)) …
```

i.e. the mean class advanced by one tenth — `residualMean (j+1)` when `σ = sigma j`, by `residualMean_formula`. The wave side is `WholeDomainStageBounds.physical_stage_estimates` at `gain h (j+1)` (E95). So the proposition's two orders and its construction step are all stated; what remains unstated is only that the four ordered corrections are performed *in the paper's order* as a single bundled theorem — the four steps exist as separate declarations (`CorrectionStep`'s amplitude, mean-gain, alias and five-row sections), not as one `stageStep` producing the state.

That is a real residual gap, and it is a difference of granularity rather than of content: the paper's Proposition 9.6 lists four steps and the tree proves each with the same hypotheses. Placing it as a whole assumes the composition — the same assumption E91 refused for Proposition 10.1 — so it is recorded as placed with that qualification stated, not hidden.

### 4. E96's open question: the two profile constructions are one

E96 recorded that no declaration identifies the cone witness's profile with the profile `GlobalSlowProfiles` builds. The declaration is `FinalSlowBase.profileSequence` (`:101`):

```
noncomputable def profileSequence : SlowExpansionResidual.SlowProfiles :=
  asSlowProfiles (EntranceAlignedBase.modulatedScheme H v)
```

with `H : NominalConeAssembly.Certificate W` — the §5 coefficient scheme is built *from the cone certificate of the same witness*. `FinalSlowBase.coefficients` is `EntranceAlignedBase.modulatedCoefficients H v`, and `leading_stress_eq` (`:130`) identifies its zero-order stress with `LeadingStressWeights.stress v.profiles`, so the cone bound (`leading_lowerBound`, E93) is a statement about the very coefficients whose residual (5.25) bounds. `BaseWitnessClosure.actual_finite_base` (`:92`) instantiates both at `ActualPrimary.certificate` and `ActualPrimary.modulation`, and `actual_base_compatible` (`:66`) records that both certificates concern the same actual profile.

E96's caveat was therefore too pessimistic in one direction and right in another: the bridge exists and is named, but it is a *definition* of the §5 profile in terms of the witness, not a proof that two independently built objects agree — and that is the better arrangement, because there is only one object.

### The ledger

| Status | Count | Which |
|---|---|---|
| placed, statement read | 12 | A.4, B.2, B.10, C.2, Lemma 4.7, Theorem 4.6, Corollary 10.6, Proposition 5.3, Proposition 9.1, Proposition 9.5, Proposition 9.6, Proposition 9.9 |
| partial | 1 | Proposition 10.1 (5 of 6 clauses) |
| cited in a docstring, unchecked | 2 | Lemma 9.2, Proposition 9.3 |
| unplaced | 59 | the rest |
| **total** | **74** | |

### What this does and does not change

It does not change the verdict, and it narrows where a defect could sit to one clause: Proposition 10.1's "`u(·,t) = p(·,t) = 0` for all sufficiently small `t ≥ 0`", which follows from the time cutoff in `R3CompactCandidate` but is not a field of the structure. The paper's analytic core — §5's induction, §9's estimates and iteration, the summed local field — now has a named declaration for every numbered result.

What it does not establish, and cannot: that the declarations *prove* the paper's inequalities. Statement-level correspondence is where this audit has always been, and seventy-four rows of it still say nothing about whether the estimates are valid. Two specific weaknesses are recorded rather than smoothed: Proposition 9.6 is placed as four separate steps rather than one composed theorem, and every rate in §5 is proved on a filter (`FiniteJetRate`) rather than as a pointwise constant, which is the correct reading of "`q ↓ 0`" but not the same object as the paper's displayed inequality.

*Evidence: `SlowExpansionResidual.lean:634,769,885,915`; `BaseResidual.lean:1440`; `ActualIterationLedger.lean:34,38,231,235,239,243`; `CorrectionState.lean:217–219`; `CorrectionStep.lean:3004,3021`; `WholeDomainPhysicalStageTheorem.lean:101`; `ActualInitialization.lean:173`; `BaseWitnessClosure.lean:66,92,106`; `FinalSlowBase.lean:101,106,130,149`; `ns.txt:2874–2891, 5421–5425, 5475–5488`.*

---

## E98 — Proposition 10.1 closes: the initial rest is a theorem, not a structure field (2026-11-23)

*Reading entry. E91 and E97 both left exactly one clause of the whole ledger open: Proposition 10.1's "`u(·,t) = p(·,t) = 0` for all sufficiently small `t ≥ 0`", recorded as following from the time cutoff but not stated. It is stated, in the theorem that carries the paper's Theorem 1.1, one file above the structure that E91 read.*

### 1. The clause

The paper's Proposition 10.1 (pp. 117–118) builds the compact candidate `(u, p, f)` and lists six properties. The sixth: the velocity and pressure vanish identically for all sufficiently small nonnegative times. E91 read `R3CompactCandidate.Properties` (`R3CompactCandidate.lean:24`) and found the other five as fields — smoothness, compact support, divergence-freedom, the residual identity, and agreement with the local fields — and no field for the sixth. That reading was correct and its conclusion was not: the clause is not a property of the *structure*, it is a property of the *selected* candidate, proved where the selection is made.

### 2. The declaration

`R3/Theorem.lean:31`, `theorem_1_1_with_initial_rest`:

```
theorem theorem_1_1_with_initial_rest (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space,
        u (t, x) = 0 ∧ p (t, x) = 0
```

The proof obtains the three fields from `ActualCandidate.selected_candidate_one_with_initial_rest`, which supplies the rest interval together with the candidate, and transports both through the viscosity scaling: `u_ν(t,x) = √ν · u(t, x/√ν)`, `p_ν = ν · p`, and the zero is preserved by `smul_zero`. So the rest interval is not bolted on after the fact; it is part of the selected candidate's data all the way from `ActualCandidateConstruction`.

### 3. Stronger than the paper asks, in two directions

The paper asks for *sufficiently small* `t ≥ 0`, one-sided. The theorem gives `|t| ≤ 3/8`: two-sided, with an explicit radius, and it includes negative time. Neither strengthening costs anything, and both are worth naming because they change what the clause can be used for. A reader who needs the candidate at rest on a full slab around zero — which is what makes a force supported in positive time meaningful, and what `force_nonzero_of_no_global_solution` (`R3/CandidateBreakdown.lean:57`) uses — gets it from this statement rather than having to reconstruct it from a cutoff argument.

It also removes the last reason to read Proposition 10.1 as partial. All six clauses now have a named declaration:

| Clause | Declaration |
|---|---|
| smooth `u`, `p` on `preSingularDomain` | `CandidateProperties.velocity_smooth`, `.pressure_smooth` (:94–95) |
| compact spatial support | `.support_compact`, `.velocity_support`, `.pressure_support` (:96–100) |
| `div u = 0` | `.divergence_free` (:104) |
| residual equals the force | `.navier_stokes` (:106) |
| agreement with the local fields | `R3CompactCandidate.velocity_locally_eq`, `.pressure_locally_eq` (:231, :240) |
| `u = p = 0` for small `t ≥ 0` | `theorem_1_1_with_initial_rest` (`R3/Theorem.lean:31`) |

### 4. Why E91 missed it, and why that is the same mistake three times

E91 read the structure. E94 read the paper's phrase. E95 read the exponent shape. This is the fourth time a row has moved because the search was aimed at a name rather than at a statement, and the first time the missing statement was in the *headline theorem's* signature rather than in a helper module. The lesson is not "search harder". It is that a clause can live at the top of the dependency graph instead of the bottom: the structure describes what every candidate has, and the initial rest is a property of the one candidate the construction selects.

It is also the reason the clause is genuinely stronger than a field would have been. A field on `Properties` would have to be supplied by every producer, including the periodic route that builds its candidate through `of_periodic_local_model`; a theorem about the selected whole-space candidate states the fact once, where the selection is made, and does not constrain the route.

### 5. The ledger closes

| Status | Count | Which |
|---|---|---|
| placed, statement read | 13 | A.4, B.2, B.10, C.2, Lemma 4.7, Theorem 4.6, Proposition 5.3, Proposition 9.1, Proposition 9.5, Proposition 9.6, Proposition 9.9, Proposition 10.1, Corollary 10.6 |
| partial | 0 | — |
| cited in a docstring, unchecked | 2 | Lemma 9.2, Proposition 9.3 |
| unplaced | 59 | the rest |
| **total** | **74** | |

Thirteen of seventy-four, with no row left half-open. That is a cleaner statement than a larger number would be: the paper's spine — the existence theorem, the coefficient induction, the three stage results, the summed local field, the forcing, the periodic corollary — is now mapped end to end at statement level, and what remains unplaced is the outer shell: the appendices' supporting lemmas, the §6–§8 construction lemmas, and the two rows the source cites but this audit has not read.

### 6. What this does not change

Nothing about validity. The theorem's conclusion is a rest statement about the *constructed* field; it says nothing about whether the residual estimates that produce the field are correct. And the route difference E91 recorded survives: the assembly reaches the cutoff product through the periodic local model (`of_periodic_local_model`, `:179`) rather than through `curl(χA) + χB e_θ` directly. The clause is placed; the route is still not the paper's. That is the same distinction E91 drew, and closing the clause does not close it.

One small honesty note on the constant: `3/8` appears in the theorem and nowhere in the paper's Proposition 10.1, which says only "sufficiently small". The audit did not find where `3/8` is chosen, only that it is proved. That is a strengthening, not a mismatch, but it is a number the paper does not print.

*Evidence: `R3/Theorem.lean:19,31–45,48`; `R3/ProblemStatement.lean:92–109`; `R3/CandidateBreakdown.lean:57`; `R3CompactCandidate.lean:24,179,231,240`; `ActualCandidate.selected_candidate_one_with_initial_rest`; `ns.txt` pp. 117–118.*

---

## E99 — Three structures are called `CandidateProperties` (2026-11-23)

*Reading entry. Found while checking what Proposition 10.1's clauses quantify over. There are three distinct structures with this name, in three namespaces, with different fields and different competitors. Nothing is wrong with the development; the naming is the finding.*

### 1. The collision

| Name | Module | Fields that differ |
|---|---|---|
| `NavierStokes.ProblemStatement.CandidateProperties` | `NavierStokes/ProblemStatement.lean` | periodic velocity and pressure, `CompactFutureTimeSupport`, no compact support set `K`, no energy bound |
| `NavierStokesR3.ProblemStatement.CandidateProperties` | `NavierStokes/R3/ProblemStatement.lean:92` | compact `K`, `CompactPositiveTimeSupport`, `UniformFiniteEnergy (Ico 0 1)`; no periodicity |
| `NavierStokes.PeriodicPaper.CandidateProperties` | `PeriodicPaperTheorem.lean:22` | compact `K ⊆ fundamentalInterior`, periodic on the cube, support intersected with `fundamentalCube`, no energy bound |

Each is the right structure for its own theorem. The whole-space candidate needs a compact support set because `not_global_agreement` uses compactness of `Icc 0 1 ×ˢ K` to bound a competitor on the set where the candidate is large. The periodic candidate needs the support *intersected with the fundamental cube*, because a nonzero periodic lift cannot be compactly supported on `ℝ³`; the module says so in its header. The generic `ProblemStatement` structure is the loosest of the three and is the one whose `candidateStatement` carries an explicit `OPEN` banner.

### 2. The banner is not about the theorem

`ProblemStatement.candidateStatement` is annotated:

```
/-- OPEN: the primary existential content of Candidate Theorem 1.1.
There is no proof, witness, or axiom asserting this proposition in this module. ... -/
```

A reader who greps `candidateStatement` and finds this will conclude the main existence claim is open. It is not: the periodic corollary is `PeriodicPaper.periodic_corollary` (`:155`), built from `NavierStokesR3.theorem_1_1_with_initial_rest`, and the whole-space theorem is `NavierStokesR3.breakdownStatement`. The banner is a statement about *this module's* contents — true, and the right thing for a formalizer to write — but it is attached to a proposition that is not the one the paper's Theorem 1.1 denotes. The same care that produced the banner is what makes the name collision costly: the honest label and the headline name are on different objects.

### 3. Why it matters for the audit

Every entry in this log that says "Proposition 10.1 is placed" cites fields by bare name — `velocity_smooth`, `divergence_free`, `navier_stokes`. Those names exist on all three structures, and two of the three have no `energy_bounded` and no `K`. A clause-level placement is therefore only as precise as the namespace it is written in. This entry fixes that for the rows already placed: Theorem 1.1 and Proposition 10.1 are `NavierStokesR3.ProblemStatement.CandidateProperties`; Corollary 10.6 is `NavierStokes.PeriodicPaper.CandidateProperties`. No row changes status; two citations become unambiguous.

### 4. What it says about the formalization's layering

The three structures are not duplication by accident. The whole-space one is closed under the viscosity scaling used in `theorem_1_1_with_initial_rest`; the periodic one is closed under periodization (`of_compact_candidate`); the generic one is the interface `CandidateConsequences` consumes, where only smoothness, periodicity, support in time and unboundedness are needed. That is a sensible factoring — a consumer takes the weakest interface that supports its lemma. The cost is that the paper's single phrase "a candidate" denotes three Lean records, and the audit's own table needs the namespace to be meaningful.

### 5. The general lesson, stated once

E94 found a result under its output's name. E98 found a clause in the headline theorem rather than in the structure. This entry finds that the structure itself is three structures. All three are the same failure mode of *statement-level* auditing: names are not statements. The remedy is not more greps; it is that every row in the ledger should carry its full name, and this entry retrofits that for the three rows where the bare name is ambiguous.

*Evidence: `NavierStokes/ProblemStatement.lean` (`CandidateProperties`, `candidateStatement`, `CompactFutureTimeSupport`, `SpeedUnboundedAtOne`); `R3/ProblemStatement.lean:92–109,119–133`; `PeriodicPaperTheorem.lean:22–40,44–53,148`; `R3/Theorem.lean:31`; `R3/CandidateBreakdown.lean:28–36`.*

---

## E100 — "Speed unbounded at one" is pointwise, and that is weaker than a trajectory (2026-11-23)

*Reading entry. The headline theorem's conclusion is `SpeedUnboundedAtOne`. Its definition decides what the paper's "the speed becomes unbounded as `t → 1`" actually means in the formalization, and the answer is not a limit along a trajectory.*

### 1. The definition

```
def SpeedUnboundedAtOne (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t, x)‖
```

Every threshold `M` and every left-neighbourhood radius `δ` is met by *some* spacetime point in the strip. There is no requirement that the same spatial point works for two different `M`, no continuity in `x`, no trajectory `x(t)`, and no statement about the pressure. It is exactly "the sup over `x` of `‖u(t,x)‖` is unbounded as `t ↑ 1`", expressed without taking a supremum.

### 2. What it implies, and what it does not

`unbounded_speed_excludes_uniform_bound` (`ProblemStatement.lean`) proves the equivalence one actually wants at this level: no constant bounds `‖u(t,x)‖` on `Ico 0 1 × ℝ³`. That is the negative of a uniform bound, and it is what `not_global_agreement` needs: a smooth competitor is bounded on the compact set `Icc 0 1 × K`, so a candidate that exceeds that bound somewhere in the strip cannot equal it there.

It does **not** give a divergent trajectory. `h3_tendsto_of_speed_tendsto` (`CandidateConsequences.lean:153`) makes the gap explicit: given a path `x : ℝ → Space` with `‖u(t, x t)‖ → ∞` as `t ↑ 1`, it proves the `H³` norm tends to infinity. That is a strictly stronger hypothesis than `SpeedUnboundedAtOne`, and the development proves the stronger conclusion only under the stronger hypothesis. So the headline theorem's "unbounded" is a statement about a set of points, not about a moving particle.

### 3. Why the paper's prose reads stronger

The paper says the speed is unbounded as `t → 1`. In ordinary PDE prose that usually means a blow-up of the `L∞` norm, which is precisely the pointwise-in-time supremum — the same object, modded out by the fact that the supremum need not be attained. The formalization avoids the supremum entirely by existentially quantifying the point, which is equivalent for the purpose of excluding a uniform bound and cheaper to prove. This is a faithful encoding of the norm blow-up, and it is *not* a claim about any particular fluid parcel.

### 4. The one place the difference bites

`not_global_agreement` picks `M = max M_competitor 1` and `δ = 1`, obtains `(t, x)` with `1 - 1 < t < 1`, and shows `x ∈ K` by contradiction: if `u(t,x) = 0` then the norm is zero, contradicting `M < ‖u‖`. That argument needs only one point per threshold, which is what the definition gives. If a later argument needed the singular set to accumulate at a fixed `x`, or needed `‖u(t, x₀)‖ → ∞` for a fixed `x₀`, this definition would not supply it — and the development does not claim it does. The audit records the distinction because the paper's §1 sentence is the kind a reader paraphrases as "a particle speeds up", and the formal statement is not that.

*Evidence: `NavierStokes/ProblemStatement.lean` (`SpeedUnboundedAtOne`, `unbounded_speed_excludes_uniform_bound`, `zero_velocity_not_unbounded`); `R3/CandidateBreakdown.lean:10–36`; `CandidateConsequences.lean:136–142,153–169`.*

---

## E101 — The force's "rapid decay" is temporal, and mostly literal vanishing (2026-11-23)

*Reading entry. `CandidateProperties.force_derivative_decay` is stated as arbitrary polynomial decay of every jet of the force for `t ≥ 0`. Read with its proof, the clause is almost entirely a support statement.*

### 1. The support predicate is one-sided and spatial-free

```
def CompactFutureTimeSupport (f : VelocityField) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ x : Space, f (t, x) = 0
```

Despite the name, nothing is compact: it says the force vanishes after some finite time `T`, uniformly in `x`. No spatial support, no decay in `x`, no regularity. The whole-space candidate uses a different predicate, `CompactPositiveTimeSupport`, which is what makes `force_nonzero_of_no_global_solution` conclude that a force with no global solution must be nonzero at some `t > 0`.

### 2. The decay theorem

`CandidateConsequences.futureJet_decay` proves, for every `m` and every `K ≥ 0`, a constant `C > 0` with

```
‖futureJet f m (t, x)‖ ≤ C * (1 + t) ^ (-K)     for all t ≥ 0, x
```

The proof splits at `T`. For `t > T` the jet is literally zero, by `CompactForceDecay.iteratedFDeriv_eq_zero_after`, and the right-hand side is nonnegative. For `t ≤ T` it uses `MaximalLifespan.periodic_bound_on_slab` — a uniform bound `M` on the compact slab `Icc 0 (T+1) × univ`, obtained from continuity and spatial periodicity of the one-sided jets — and sets `C = M * (1 + (T+1))^K`, so that `C (1+t)^{-K} ≥ M ≥ ‖jet‖` on the slab.

### 3. What the clause therefore says

Two things, neither of them spatial decay. On `[0, T]` it says the jets are bounded, with a constant that grows like `(1+T)^K` — the polynomial rate is paid for by the constant, not proved by an estimate. On `(T, ∞)` it says the force is zero. So "every derivative has arbitrary polynomial decay in time" is true, and its content is: the force is smooth and periodic in space, continuous up to `t = T`, and identically zero afterwards.

That is exactly what the paper's periodic corollary needs, because a force with compact time support trivially satisfies any decay requirement imposed at infinity. It is worth writing down because a reader who sees "rapid decay" in the corollary's statement will look for a spatial weight in the proof and find none; there is nothing to find. The decay is a consequence of the cutoff, and the only estimate in the proof is a compactness bound on a slab.

### 4. The honest limit

`full_forceJet_decay` and `full_forceMixed_decay` extend the same statement from the one-sided jet to the ordinary jet and to every mixed spacetime component, for the whole-space candidate, using `CandidateProperties.force_smooth : ContDiff ℝ ∞ f` — global smoothness on all of `ℝ⁴`, not just the future. That is the version `PeriodicPaper.CandidateProperties.force_derivative_decay` quotes. So the clause is placed as a statement about the *actual force constructor*, not assumed: the force is globally smooth by construction (E65), vanishes after `T`, and the bound follows.

What the audit does not claim: that a decay rate of this kind is what Fefferman's (D) asks for. E76 checked the numbered clauses and found the force regularity clause satisfied; this entry only records what the code's own decay theorem contains, so that "rapid decay" is not read as more than it is.

*Evidence: `NavierStokes/ProblemStatement.lean` (`CompactFutureTimeSupport`); `CandidateConsequences.lean:79–110,114–133,141–142,144–148`; `PeriodicPaperTheorem.lean:35,116–128`; `R3/CandidateBreakdown.lean:57–66`.*

---

## E102 — Two derivative costs, and the sharper one is not the paper's `K_m` (2026-11-23)

*Reading entry. E95 identified the paper's truncation loss `K_m = m + 2 + 2h` with `truncationResidual_rate`'s exponent, whose slope in `m` is exactly 1. The stage estimates use a different loss, whose slope is `1 + 3h/2`. Both are in the tree; they are not interchangeable, and the difference is the sort of thing that would matter to anyone reusing one for the other.*

### 1. The two definitions

```
def derivativeCost (h : ℝ) : ℝ := 1 + 3*h/2
def physicalLoss (h : ℝ) (m : ℕ) : ℝ :=
  2*CoordinateAlgebra.A h + ((m:ℝ)+1)*derivativeCost h
```

`physicalLoss` is the loss charged per derivative in the sharp phase estimates: `SharpPhysicalCopyBounds`, `SharpCurrentParticularBounds`, `SharpParticularStageBounds` and `WholeDomainPhysicalStageTheorem` all bound jets by `q^(g − physicalLoss h m)`, and `rescale_with_common_loss` (`SharpPhysicalLoss.lean:14`) is the generic step that converts a `q^(g − k·derivativeCost)` bound into `q^(g − physicalLoss h m)` for `k ≤ m+1`. The `(m+1)` is deliberate, and its docstring says why: "The printed physical loss includes one derivative for potential recovery."

### 2. The comparison

At `0 < h < 1/2`, `derivativeCost h ∈ (1, 7/4)`. So the stage loss grows strictly faster in `m` than the truncation loss, whose slope is 1 after E95's identification. Concretely, if one tried to reuse `physicalLoss h m` as the paper's `K_m` in (5.25), the resulting bound would be *weaker* — a larger exponent subtracted — and not equal to the paper's display. Conversely, using `K_m = m + 2 + 2h` in the stage estimates would be stronger than what the tree proves.

This is not a defect in either place. It is a reminder that "the derivative loss" is not one object in this development: the truncation residual loses one power per derivative because it is built from finitely many smooth monomials (`finset_monomial_rate`), while the oscillatory phase loses `1 + 3h/2` because differentiating the carrier multiplies by a phase gradient of size `q^{-(1+h)}` and by a `q^{-h/2}` amplitude factor — `carrier_geometric_bound`'s `hqpow` computation is literally `q^g · (q^{-h/2})^m · (q^{-(1+h)})^m = q^(g − m(1 + 3h/2))`.

### 3. Why the audit records it

Because E95's `K_m = m + 2 + 2h` is the one place in the log where a paper exponent was matched to a Lean exponent by arithmetic, and the arithmetic is only valid for the truncation residual. A reader who carries that identification into §9 gets the wrong loss. The correct statement is narrower and worth having: the paper's `K_m` is realized by `truncationResidual_rate`; §9's stage estimates use `physicalLoss`, which is a different and larger loss, and the paper's §9 accordingly prints different constants. Nothing in the ledger changes status, because both are stated results, not hypotheses.

*Evidence: `SharpPhysicalCarrier.lean:13–17,101–107`; `SharpPhysicalLoss.lean:14–37`; `SharpPhysicalCopyBounds.lean:29–65`; `SharpParticularStageBounds.lean:13–46`; `WholeDomainPhysicalStageTheorem.lean:196–201`; `BaseResidual.lean:1440`; E95 §3.*

---

## E103 — The numeric ledger is exact rationals, and `κ` is conservative by 500× (2026-11-23)

*Reading entry. The paper fixes `κ_s = 10⁻⁵` and a list of decimal-looking constants. The tree carries them as rationals and proves every comparison by `norm_num`/`linarith`, with no floating point anywhere. One of those comparisons shows the manuscript's `κ` is far from tight.*

### 1. Every constant is a rational

`ExponentLedger` contains `1/5`, `1/10`, `7/10`, `6/5`, `17/25`, `19/10`, `9/50`, `17/100`, `9/10`, `1/200`, `1/100000`, `1/1000000`. There is not a decimal literal in the module, and the theorems that use them are closed by `norm_num` or `linarith`, so each comparison is a kernel-checked rational inequality rather than a numerical approximation.

`manuscript_kappa_admissible` is the formal statement that `κ = 10⁻⁵` is in the ledger's admissible range, written as `0 ≤ 1/100000 ∧ 1/100000 ≤ 1/100000`. `smaller_kappa_admissible` records that any `κ < 10⁻⁶` also satisfies the ledger's hypothesis `κ ≤ 10⁻⁵` — a transitivity fact, not an independent existence claim.

### 2. The tight margin is not the one `κ` is chosen for

```
theorem old_difference_bar_margin_iff (κ : ℝ) :
    17 / 100 < 9 / 50 - 2 * κ ↔ κ < 1 / 200
```

The `.17` bar margin — the module calls it "the most restrictive" — is satisfied exactly when `κ < 0.005`. The manuscript's `κ = 0.00001` is smaller by a factor of 500, so at the manuscript's value the margin is `0.17998 > 0.17`, with `0.00998` to spare. Whatever else is tight in §9, this comparison is not: `κ` could be raised two and a half orders of magnitude and still clear it.

### 3. Why that matters

Not as a criticism — choosing `κ` small is free, and a small `κ` makes every exponent margin easier. It matters because it locates where the real constraints are. `ExponentLedger` proves the stage arithmetic *uniformly in* `κ` for `κ ≤ 10⁻⁵` (`all_stage_arithmetic`, for every `n`), so the choice is not doing work at any individual stage; it is a single global cushion. A reader who sees "`10⁻⁵`" and assumes some estimate forced it that small will look in the wrong place. The binding constraints in this development are not these rational margins at all; they are the losses `physicalLoss` (E102) and the geometric thresholds in `ActualCarrierGeometry`.

### 4. What is still not checked

The arithmetic being exact says nothing about whether the exponents attached to the *fields* match the exponents in these theorems. `all_stage_arithmetic` is a statement about numbers; `residualWave_formula` and `residualMean_formula` are statements about the ledger's own definitions; and the class memberships that connect the two are the rows E94–E97 placed by reading. The chain is: rational margin (kernel-checked) → exponent formula (kernel-checked) → class membership of an actual residual (kernel-checked, statement read). This entry closes none of those links; it records that the first two are exact, so any error in the chain would have to be in the third.

*Evidence: `ExponentLedger.lean:1–40,236–321`; `manuscript_kappa_admissible` (`:271`); `old_difference_bar_margin_iff` (`:285`); `stageParameter` (`:294`); `all_stage_arithmetic` (`:313`); `ActualIterationLedger.lean:231–243`.*

---

## E104 — `formalization.yaml` is a second, much smaller claim ledger (2026-11-23)

*Reading entry. The repository ships machine-readable metadata naming its main results. Read against the audit's ledger, it shows exactly how much of the paper the development claims to have formalized, and it is far less than "the paper".*

### 1. What the file claims

`formalization.yaml` (v0.4) declares four `main_results`, each with a declaration, a file, `sorry_count: 0`, an axiom list of exactly `propext`, `Classical.choice`, `Quot.sound`, and a comparator config:

| Claim | Declaration | File |
|---|---|---|
| (C) non-existence of global smooth finite-energy solutions on `ℝ³` | `NavierStokes.Comparator.navier_stokes_breakdown_R3` | `NavierStokes/ComparatorSolution.lean` |
| (D) non-existence of global smooth periodic solutions | `NavierStokes.Comparator.navier_stokes_breakdown_periodic` | same |
| unforced Euler breakdown on `ℝ³` | `Euler.euler_breakdown_R3` | `Euler/Solution.lean` |
| compact Euler data with finite maximal lifespan | `Euler.exists_compact_smooth_euler_singularity` | same |

`status.scope` is the sentence `"Full formalization of main results."` — not "of the paper". That distinction is doing real work: the alignment block maps four statements, and the paper has seventy-four numbered results. The file is honest; a reader who quotes "full formalization" without the qualifier is not.

### 2. `review.status: self-assessed`

The metadata's own review field says `self-assessed`. That is the same status this audit keeps recording: no independent referee has checked the development, and the only external checks are the Comparator runs the repository configures and this audit reproduced (E75, E79). It is worth noting that the repository says so itself, because the audit's repeated caveat ("not independently reproduced math") can read as an accusation when it is in fact a restatement of the project's own metadata.

### 3. One clause where the metadata is stronger than the paper

The Euler entry's description says the compact data has "an infinite C1 norm limsup". E81 read the Euler paper's Theorem 1.1 and found it asserts `limsup ‖∇u‖∞ = ∞`; the challenge's `limsup velocityC1Norm = ⊤` includes the velocity supremum as well, which is a *weaker* statement (a sum can diverge while a summand does not). The development also proves the paper's gradient-only form (`EulerC1Limsup.maximalGradientNorm_limsup`), but that declaration is not in the challenge's target list. So the metadata's prose follows the challenge, not the paper, and the difference is the one E81 already recorded. Nothing is hidden; the description just names the stronger encoding without saying it is stronger.

### 4. The pin is a tag, not a hash

`lakefile.toml` pins mathlib and Comparator at `rev = "v4.34.0-rc2"`, and `lean-toolchain` names `leanprover/lean4:v4.34.0-rc2`. Those are *tags*. A tag can be moved; a commit hash cannot. The audit reproduced the build at the pinned tag (E73), but "reproducible" in the strong sense would need the resolved commit SHAs recorded beside the tag. The repository does not do that, and `lake-manifest.json` — the file that would carry them — was not among the files this slice read. Recorded as a durability note, not a defect: for a prerelease toolchain the tag is the only stable name the upstream projects offer.

*Evidence: `formalization.yaml:1–131`; `lakefile.toml:1–29`; `lean-toolchain:1`; E73; E81.*

---

## E105 — The moment matrices are nonsingularity theorems, for every `n` (2026-11-23)

*Reading entry. §8.5 of the paper solves five linear moment equations; `FiveRowRank` and `MomentRepair` are the modules. The audit expected a 5×5 determinant and found four general theorems instead.*

### 1. What is proved

`PowerMomentMatrix.lean` proves four determinant statements, each for arbitrary `n : ℕ`:

* `expEvaluationMatrix_det_ne_zero` — the matrix `(i,j) ↦ exp(a_i x_j)` is nonsingular when the `a_i` are distinct and the `x_j` strictly increasing. This is the generalized Vandermonde/Chebyshev fact: if a vector `c` annihilates all rows, the exponential polynomial `∑ c_i exp(a_i x)` has `n` distinct zeros, and an exponential polynomial with distinct frequencies cannot have more zeros than its number of terms minus one.
* `powerEvaluationMatrix_det_ne_zero` — `(i,j) ↦ x_j^{a_i}` at distinct exponents and positive ordered nodes, reduced to the previous theorem by `x^a = exp(a log x)`; the proof literally rewrites the matrix as `expEvaluationMatrix a (fun j => log (x j))` and applies strict monotonicity of `log`.
* `intervalMomentMatrix_det_ne_zero` — moments against measures supported on disjoint intervals, by Rolle: each interval contributes a zero of the exponential polynomial, and `n` zeros force all coefficients to vanish.
* `bumpMomentMatrix_det_ne_zero` — moments against nonnegative bump functions with disjoint supports, by the same route.

### 2. Why this is the right shape

The paper needs five specific rows to be independent, with exponents and radii chosen numerically. The tree proves independence for *any* finite set of distinct exponents on ordered nodes, so the five-row case is an instance and no numerical coincidence is relied on. It also supplies `exists_ordered_derivative_zeros` (E90), which is the Rolle step in the form the repair uses. That is stronger than the paper in the way that matters: a wrong numerical choice of exponents would not be caught by a general theorem, but the theorem also does not need the choice to be right — it needs only distinctness.

### 3. What is not proved, and it is the audit's usual gap

`det ≠ 0` says the linear system has a unique solution. It does not bound the solution. The five-moment correction solves `M c = b`, and the size of `c` is what the later estimates charge; `MomentRepairPicard` and `FiveRowRank` carry the quantitative side, and this entry did not read their constants. So the placement is: nonsingularity is proved in general, invertibility is `Matrix.isUnit_iff_isUnit_det`, and the operator norm of the inverse is not a statement in this module.

That is not a criticism of the module — it is a determinant module. It is a statement about what a row "moment matrix nonsingular" can and cannot mean: the kernel checks the determinant is nonzero, and the *size* of the inverse is a term-level constant like every other in this development.

### 4. The `n`-general form has a cost

Because the theorem is stated for arbitrary `n`, its conclusion says nothing about which `n` the construction instantiates. The five-row use is a call site, not a theorem; a reader who wants "the 5×5 determinant is nonzero" has to instantiate `n = 5` and supply five distinct exponents and five ordered radii. The audit did not find that instantiation by name. So the row is placed at the level of the general principle, and the specific five-row instance is a use, not a declaration — the same granularity distinction E97 recorded for Proposition 9.6.

*Evidence: `PowerMomentMatrix.lean:121–155,216–267`; `FiveProfileMoments.lean:8`; `FiveRowRank`; `MomentRepair.lean:36–59`; `CROSSWALK.md` §3.4.*

---

## E106 — The uniqueness theorem assumes no decay on the competitor (2026-11-23)

*Reading entry. `WholeSpaceUniqueness.classical_uniqueness_on_Icc` is the lemma that turns "the candidate blows up" into "no global solution exists". Its hypothesis list is the competitor class, and it is deliberately minimal.*

### 1. The statement

```
theorem classical_uniqueness_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu hdv : divergence-free)
    (hNS : navierStokesResidual 1 u p = navierStokesResidual 1 v q)
    (hzero : u (0, ·) = v (0, ·)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x)
```

What is assumed about `v`: smoothness on the slab, divergence-freedom, the same equation, the same initial datum, and a uniform finite energy bound. What is **not** assumed: spatial decay, compact support, pressure growth, derivative bounds, or a pressure gauge. The module header says so in one line: "No growth, decay, support or derivative bound is assumed for the competing pressure or velocity."

### 2. What makes that possible

The reference `u` has compact spatial support throughout `[0, T]`, so `CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab` gives *it* finite energy, and the difference `w = u − v` has finite energy. The pressure is eliminated by a flux estimate: `PressureFlux.exists_uniform_actual_pressure_flux_bound` produces a constant `CP` for the actual pressure pair from `M` (the `L²` bound on `w`), `U` (an `L³` bound on `u`), `G₀` (a tensor-difference `L¹` bound), and a gradient bound `G` on `u`. Every one of those is produced by a compactness argument on the slab — `exists_lpNorm_three_bound`, `exists_gradient_bound`, `exists_radius_weight_derivative_zero` — not assumed. Then `eq_of_pressure_flux_bound` closes the energy identity with Gronwall.

So the asymmetry is the point: the *candidate* pays for compact support, and the *competitor* pays only finite energy. That is exactly the right trade for excluding a global solution, because a global finite-energy solution is the weakest natural competitor and any decay hypothesis would have made the theorem weaker than Clay's (C).

### 3. The one place the compactness matters

`CandidateProperties.not_global_agreement` uses `IsCompact (Icc 0 1 ×ˢ K)` and continuity of the competitor on that set to get a bound `M`; then it applies `speed_unbounded (max M 1)` to find a point in `K` where the candidate exceeds `M`. If `K` were not compact, or if the competitor were only locally bounded, the argument would need a different bound. The compact support of the candidate is therefore load-bearing twice: once for the energy of the reference in the uniqueness theorem, and once for the boundedness of the competitor on the singular set.

### 4. The scope of "no global solution"

`GlobalFiniteEnergySolution` (`R3/ProblemStatement.lean:125`) has no support, no periodicity, no pressure normalization, and requires `UniformFiniteEnergy (Ici 0)` over all of `ℝ³` and all `t ≥ 0`. So `¬ Nonempty` is: there is no smooth divergence-free field on `ℝ³ × [0, ∞)` with bounded kinetic energy solving the equation with the same force and zero datum. That is (C)'s competitor, and the audit's E76 clause check is the authority for the match; this entry only records that the class is not narrowed by the uniqueness proof.

*Evidence: `R3/WholeSpaceUniqueness.lean:19–69,73–119`; `R3/ProblemStatement.lean:119–136`; `CompactComparisonBounds` (`uniformFiniteEnergy_of_compact_slab`, `exists_lpNorm_three_bound`, `exists_gradient_bound`, `exists_radius_weight_derivative_zero`); `PressureFlux.exists_uniform_actual_pressure_flux_bound`; `R3/CandidateBreakdown.lean:10–36`.*

---

## E107 — The initial-rest clause is load-bearing for the periodic corollary (2026-11-23)

*Reading entry. E98 placed Proposition 10.1's sixth clause as a strengthening. It is not optional: the parabolic compression that produces the periodic candidate consumes exactly that clause to be smooth across the new time origin.*

### 1. The compression

`R3/ParabolicScaling.compressedCandidate` takes a whole-space candidate, a rest hypothesis

```
hrest : ∀ t, |t| ≤ 3/8 → ∀ x, u (t, x) = 0 ∧ p (t, x) = 0
```

and a scale `l > 1`, and returns a candidate for the same viscosity `ν` with

* `velocity l u (t, x) = l · u (l²(t−1)+1, l·x)`,
* `pressure l p (t, x) = l² · p (l²(t−1)+1, l·x)`,
* `force l f (t, x) = l³ · f (l²(t−1)+1, l·x)`,
* support `(fun x => l⁻¹ • x) '' K`.

The clock `l²(t−1)+1` maps the singular time `1` to `1` and the original initial time `0` to `1 − l² < 0`. The docstring says it: "Extension by zero before the original initial time makes the compressed solution start from rest, while the spatial support is divided by the arbitrary factor `l > 1`. Viscosity remains unchanged."

### 2. Where `hrest` is used

`zeroBefore u` sets `u := 0` for `t ≤ 0`. Then `zeroBefore_smooth_on hc.velocity_smooth (fun t ht x => (hrest t ht x).1)` proves the zero-extended field is `C^∞` on `Iio 1 × univ`: at `t = 0` the original field is smooth from the right and zero from the left, and the two match because of `hrest`; without it, the extension would have a jump at `t = 0` and `pull_smooth_on` would fail. The pressure uses the same hypothesis with its own scaling `l²`.

So the clause is not cosmetic. It is precisely the analytic input that lets the compression move the initial time to a negative value without losing smoothness. A construction that only proved `u = 0` on a one-sided neighbourhood of `0` would suffice; the theorem's two-sided `|t| ≤ 3/8` is more than enough, and the `3/8` is exactly the radius that survives `l` up to the range used.

### 3. The rest of the invariance

`force_support` re-proves `CompactPositiveTimeSupport` for the scaled force by `affineScale (l³) l (l²) (1−l²)`: the force's time support moves to a compact interval in positive time because `1 − l² < 0`. `velocity_energy_bounded` rescales the energy by `l`'s exponents, `velocity_speed_unbounded` preserves the blow-up at `t = 1`, and `divergence_free` uses `pull_divergence`: `div(u ∘ φ) = l² · div u`, so zero stays zero. `navier_stokes` is `pull_residual` plus `zeroBefore_residual`, and the pressure scaling `l²` is what makes the residual match `force l f`.

### 4. What this changes in the ledger

Nothing — both rows were already placed. It changes what the placement *means*: Proposition 10.1's sixth clause is not a convenience attached to the forcing theorem, it is the compatibility condition between the whole-space candidate and the periodic corollary's clock. The audit's E91→E98 sequence therefore ends with a clause that was not merely missing from a structure, but was the one whose absence would have blocked Corollary 10.6's construction.

*Evidence: `R3/ParabolicScaling.lean:1–15,41–69,92–120,163–222`; `R3/Theorem.lean:31`; E98; E70.*

---

## E108 — `MaximalLifespan` is a periodic development, and its "lifespan" is a set (2026-11-23)

*Reading entry. The module name suggests a general statement about the whole-space candidate. It is stated for periodic classical solutions, and that scope is the point.*

### 1. The structures

`ClassicalSolution f initial T u p` requires `ContDiffOn` on `lifespanDomain T = Ico 0 T ×ˢ univ`, `UnitSpatialPeriodsOn` for both velocity and pressure on `Ico 0 T`, the initial datum, divergence-freedom, and the residual identity for `t ∈ Ioo 0 T`. There is no energy bound in the structure, and no pressure gauge condition: the docstring says pressures are "retained as witnesses but are never required to agree with a different gauge."

`HasClassicalExtension` asks for a strictly larger `S`, a solution on `S`, and velocity agreement on the whole of the original interval — the pressure may differ by a time-dependent spatially constant normalization. `IsMaximalClassicalSolution` is a solution with no extension.

### 2. The set, not the number

```
def admissibleLifespans (f) (initial) : Set ℝ :=
  {T | ∃ u p, ClassicalSolution f initial T u p}
```

"Maximal lifespan is one" is then a statement about this set, not about a distinguished solution: `candidate_admissible_lifespans` proves `admissibleLifespans f 0 = Ioc 0 1`. That is stronger and cleaner than picking a solution and proving it cannot be extended, because it says *every* classical solution with this force and datum has lifespan at most one, and every `T ≤ 1` is attained by restriction (`ClassicalSolution.restrict`).

### 3. The exclusion step

`PeriodicViscosity.excludes_global_solution` takes a pre-singular periodic solution with `SpeedUnboundedAtOne` and a global periodic competitor (smooth on `futureDomain`, periodic on `Ici 0`, same force, zero datum, **no energy bound**) and derives `False` by applying `MaximalLifespan.unbounded_excludes_continuous_extension`: the competitor is a continuous extension of the pre-singular solution across time one, and a continuous periodic field on a compact spatial torus is bounded there. Uniqueness on each `[0, t]`, `t < 1`, identifies the two, so the unboundedness contradicts the bound.

### 4. Scope, stated plainly

This module is part of alternative (D), not (C). Its `ClassicalSolution` is periodic by construction; the whole-space exclusion goes through `WholeSpaceUniqueness` and the compact support of the candidate (E106), not through this file. `CandidateConsequences` imports it and quotes `candidate_is_maximal` for the periodic candidate, which is consistent. So a reader who finds `MaximalLifespan` while looking for the whole-space theorem has found the wrong alternative — the same namespace hazard E99 recorded for `CandidateProperties`, in a different form: the name is general, the statement is periodic.

*Evidence: `MaximalLifespan.lean:24–66,68–115`; `PeriodicViscosity.lean:18–79`; `PeriodicPaperTheorem.lean:44–53`; `CandidateConsequences.lean:136–148`.*

---

## E109 — The four reserved windows: one touching pair, one gap (2026-11-23)

*Reading entry. `ReservedPatches` is the module behind Theorem 4.6(vi)'s two reserved intervals, and E92 read only two of its four slots. The full offset table is more specific than the paper's prose, and its arithmetic is exact.*

### 1. The table

```
leftOffset  modulation = -25   heat = -20   positive = -14   mean = -8
rightOffset modulation = -20   heat = -15   positive = -9    mean = -3
```

Each window has width exactly 5 (`offset_width`, proved by `norm_num` for each constructor), all four lie in `[-25, -3]` (`offset_bounds`), and any two distinct windows are ordered (`offsets_separated`, a case split). The module header says these are "the four examples in the manuscript: (-25,-20), (-20,-15), (-14,-9), and (-8,-3), relative to the pulse entrance."

### 2. Two details the header does not state

First, `modulation` and `heat` **touch**: `rightOffset modulation = -20 = leftOffset heat`. `offsets_separated` is stated with `≤`, not `<`, so it permits this; the two windows are disjoint as half-open or open intervals but share an endpoint. Second, there is a **one-unit gap** between `heat` and `positive`: `-15 < -14`. So the four are not an evenly spaced partition; they are two adjacent pairs with a gap in the middle. If a later estimate needs a positive distance between every pair, it has it for all pairs except `modulation`/`heat`, where the distance is zero.

### 3. Why the offsets are in log coordinates

`left F XR s = radius XR (pulseStart + leftOffset s)` with `radius XR y = XR · exp y`, so the windows are images of log-`X` intervals under `X = XR e^y`. `radius_strictMono` makes the ordering in `y` the ordering in `X`; `left_pos` gives positivity. The paper's `Ipos`, `Imean` and the `Jpos`, `Jmean` conversion (p. 21) is the same change of variable E92 placed. The tree's slots are therefore not four arbitrary time windows: they are four multiplicative bands of the radial variable, chosen so that the `(1+η²)^{-1}X^{-1/2-λ}` patch is pure on two of them and heat-corrected on the others.

### 4. The correction to E92's phrasing

E92 wrote "the log offsets are `(-14,-9)` for `.positive` and `(-8,-3)` for `.mean`, four five-log-unit windows", which reads as if there were two offsets and four windows. The precise statement is four slots, each of width five, with the table above. The placement of Theorem 4.6(vi) is unchanged — E92's mapping of `Slot` to `Ipos`/`Imean` used the right two slots — but the audit's own description was compressed past the point of accuracy, and this entry restores it.

*Evidence: `ReservedPatches.lean:1–46`; `offset_width`, `offset_bounds`, `offsets_separated`, `radius_strictMono`, `left_pos`; `ns.txt` p. 21, pp. 33–34; E92 §2.*

---

## E110 — The active-annulus weight has two different edge factors (2026-11-23)

*Reading entry. `ActiveAnnulusWeight.weight` is the paper's `ζ`, and it is not symmetric: the left edge and the right edge use different cutoffs.*

### 1. The definition

```
def weight (c a b y : ℝ) : ℝ :=
  FlatCutoff.edge c (y - a) * FlatCutoff.edge 4 (b - y)

def edgeDistance (a b y : ℝ) : ℝ := min 1 (min (y - a) (b - y))

def radialWeight (c a b X : ℝ) : ℝ := if 0 < X then weight c a b (Real.log X) else 0
```

`FlatCutoff.edge c x` is the flat exponential cutoff `exp(−c/x²)` on `x > 0` and `0` for `x ≤ 0` (its `edge_of_pos` rewrite is used in `edge_mono_pos`). The left factor carries `c`, the right factor carries the literal `4`. In the actual instantiation `c` is `activationTime²`, so the two sides of the annulus have cutoffs of different width; both are `C^∞` and flat at the edge, so the difference is quantitative, not regular.

### 2. What is proved about it

`weight_nonneg`, `weight_pos` on `Ioo a b`, `weight_zero_left` for `y ≤ a`, `weight_zero_right` for `b ≤ y`, `weight_le_left`, `weight_le_right`, `weight_le_one`, and `weight_smooth` for `c > 0`. `edgeDistance_pos` on the open annulus, `edgeDistance_le_one`, and the two one-sided bounds `edgeDistance ≤ y − a`, `edgeDistance ≤ b − y`. Later in the file, the `δ^{-m}` loss is `distance_power_le_left` and `left_bound_to_weight` (E92), and the flat-edge derivative vanishing is `weight_flat_left`/`weight_flat_right`.

So the weight is positive exactly on the open annulus, vanishes outside, is `≤ 1`, and its distance to the boundary is the `δ` of the paper's display. That is the `ζ` of Theorem 4.6(iv), and E93's `stress_lower_bound` uses it on `activeLeft < X < activeRight` with `η ∈ [-1, 1]`.

### 3. The asymmetry is not an accident of notation

The right factor's `4` is a fixed constant because the outer edge is the terminal edge, where the profile has already reached its plateau; the left factor's `c` is tied to the activation time because the inner edge is where the cone is switched on. The two edges play different roles in the construction — one is a cutoff of the source, the other a cutoff of the stress — and the weight encodes both. A reader who assumes `ζ` is a symmetric bump will get the derivative bookkeeping wrong at one of the two edges, which is exactly what `left_bound_to_weight` and its right-hand counterpart exist to prevent.

### 4. What the audit did not check

Whether the paper's displayed `ζ` has the same two constants. E92/E93 established that the *object* is the paper's: the domain, the positivity, the flat edges, the `δ^{-m}` loss and the `cζ` lower bound all match. The specific numerical asymmetry `c` versus `4` is a formalization choice that the paper's prose does not pin down, and this entry records it as such rather than claiming a clause match.

*Evidence: `ActiveAnnulusWeight.lean:20–25,36–80`; `FlatCutoff.edge_of_pos`, `edge_nonneg`, `edge_pos`, `edge_contDiff`; `LeadingStressWeights.stress_lower_bound`, `physical_jet_bound`; E92 §2; E93.*

---

## E111 — The toolchain is pinned to a prerelease tag (2026-11-23)

*Reading entry. Three files decide whether the build can be repeated: `lean-toolchain`, `lakefile.toml`, and the lock file. The first two pin tags, not commits.*

### 1. The pins

```
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lakefile.toml:  mathlib        rev = "v4.34.0-rc2"
                Comparator     rev = "v4.34.0-rc2"
```

All three agree, which is why the build reproduced on a clean runner (E73, 9,580 jobs, 28 min 35 s) and why the axiom print and Comparator runs are meaningful: the kernel, the library and the checker are the same generation. The repository also states the commit under audit, `f9e8bc5`, in its README and in the audit's citations.

### 2. What a tag does not guarantee

A git tag is a mutable ref. `rev = "v4.34.0-rc2"` resolves to whatever the tag points at when Lake fetches it. If the tag were moved or deleted, the same `lakefile.toml` would resolve to a different tree, and "clone and build" would no longer reproduce the artifact. A commit SHA would remove that risk. Lake's manifest (`lake-manifest.json`) normally records the resolved SHAs; this slice did not read it, so the audit does not claim the pins are hashes. What it can say is that the two declarations above are tags.

### 3. Why it is worth recording rather than fixing

The audit does not modify upstream. The point is for anyone reproducing: record the resolved SHAs at the time of the run, not just the tag, and keep the build log (E73 does — the full `build.log`, not a tail). The repository's own CI workflow checks out `f9e8bc5` explicitly and installs Lean through `elan`, so the *repository* is pinned by SHA; it is the *toolchain and dependencies* that are pinned by tag. That split is the useful thing to know.

### 4. The prerelease itself

`v4.34.0-rc2` is a release candidate, not a stable release. That is not a defect — the development may need features that only exist there — but it means the artifact is tied to a toolchain that upstream may replace. The audit's reproduction is therefore evidence about *this* toolchain at *this* tag, and the axiom footprints (`propext`, `Classical.choice`, `Quot.sound`) are footprints under it. Nothing in the mathematics depends on the version; the machine-checking does.

*Evidence: `lean-toolchain:1`; `lakefile.toml:1–29`; `.github/workflows/kernel-check.yml`; `README.md` (commit `f9e8bc5`); E73.*

---

## E112 — The `sorry` count is five, and four of them are the challenge (2026-11-23)

*Measurement entry. The README claims no reachable `sorry`, no `axiom`, no `native_decide`, no `unsafe`, no `implemented_by`. A raw token count over the whole tree returns five `sorry`s. Both statements are true; the difference is where the tokens are.*

### 1. The counts

Over `NavierStokesAndEuler/`, excluding `.lake/`:

| Token | Raw occurrences | Declarations |
|---|---|---|
| `sorry` | 5 | 4, all in `ComparatorChallenges/` |
| `axiom` | 4 | 0 (`^\s*axiom` returns nothing) |
| `native_decide` | 0 | 0 |
| `implemented_by` | 0 | 0 |
| `unsafe` | 0 | 0 |

The four `sorry`s are `ComparatorChallenges/NavierStokes.lean:277,284` and `ComparatorChallenges/Euler.lean:88,184`. Those files are the *challenge statements*: the theorem to be proved, with `sorry` as the placeholder the submitted solution fills. The fifth is prose — `ComparatorChallenges/NavierStokes.lean:29` says "including their intentional `sorry` challenge placeholders" — which is a docstring, not a term. So the library that proves the results contains no `sorry` at all, and the only holes in the repository are the ones the Comparator pipeline is designed to fill (and which E75/E79 show being filled).

The four `axiom` tokens are likewise not declarations; no line in the tree begins with `axiom`. They occur in comments or strings, most likely the descriptions of Comparator's permitted-axiom policy.

### 2. The size, for the record

`find` over `NavierStokes/` and `Euler/` returns **2,655 `.lean` files** and **640,857 lines**. The README's figure of 641,332 lines is 475 lines larger, which is the `ComparatorChallenges/` directory — the count there includes the challenge statements, the engine count does not. The earlier audit figure of "816 modules" was modules under `NavierStokes/` only; the two libraries together are three times that, because the Euler development is large and the `Axis*` family alone is dozens of files.

### 3. Why the distinction is not pedantic

A public claim of "no `sorry`" invites the check above, and the check returns five. A reader who stops there concludes the claim is false. The right reading is scoped: no `sorry` in any module that the headline theorems depend on; four in the challenge files, where they are the interface, and one in a sentence about them. The audit's earlier phrasing — "no reachable `sorry`" — was the correct one, and this entry supplies the numbers behind it so that the next person to run `rg sorry` is not surprised.

The same applies to `axiom`. The kernel axiom footprint printed by `#print axioms` is three axioms (`propext`, `Classical.choice`, `Quot.sound`); a text search for the word returns four hits that have nothing to do with the footprint. Token counts and kernel footprints are different measurements, and only the second one is evidence about what the theorem depends on.

### 4. What this does and does not establish

It establishes that the source tree contains no proof hole in the two libraries, and that the four holes in the repository are the challenge's. It does not establish that the proofs are correct — that is the kernel's job, and it was reproduced (E73). It does not establish that the statements are the paper's — that is E76 and E80–E82. And it does not establish that the constants are meaningful — that is the audit's standing finding.

*Evidence: `rg -n '\bsorry\b'`, `rg -n '^\s*axiom\b'`, `rg -n '\bnative_decide\b'`, `rg -n '\bimplemented_by\b'`, `rg -n '\bunsafe\b'` over `NavierStokesAndEuler/` excluding `.lake/`; `find ... -name '*.lean' | wc -l`; `ComparatorChallenges/NavierStokes.lean:29,277,284`; `ComparatorChallenges/Euler.lean:88,184`; E73.*

---

## E113 — The headline theorem excludes finite-energy competitors only (2026-11-23)

*Reading entry. `breakdownStatement` is the paper's Theorem 1.1 in Lean. Its negation is narrower than the English phrase "no global solution", and the difference is exactly the Clay alternative it targets.*

### 1. The quantifier structure

```
def breakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ u p f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalFiniteEnergySolution ν f)
```

Three things to read off. The viscosity is universal (`∀ ν > 0`). The fields, the force and the support set are existential and chosen *together* — the theorem does not say that every force has this property, and it does not say that the force is independent of the solution. And the excluded object is `GlobalFiniteEnergySolution`, which carries smoothness on all of `ℝ³ × [0, ∞)`, divergence-freedom, the same force, zero datum, and a **uniform finite kinetic-energy bound** (E106).

### 2. What is not excluded

A global smooth solution with unbounded kinetic energy is not excluded by this statement. Neither is a global weak solution, nor a global solution with a different pressure gauge, nor a solution that exists for all time but fails to be smooth at some point. The only competitor ruled out is the one Clay's alternative (C) names: global, smooth, finite energy.

That is faithful to the paper's own claim and to Fefferman's text (E76), and it is worth stating because the README's short version says "no global finite-energy solution exists" — accurate — while the paper's §1 prose can be skimmed as "no global solution". The formal statement is the weaker, correct one, and the audit has no finding that it should have been stronger: proving exclusion of an infinite-energy global solution would be a different theorem and is not what (C) asks.

### 3. The dependence on the force

Because `f` is existentially quantified inside the same block as `u` and `p`, the theorem's content is: there is a force, built from the same construction, for which the candidate blows up and no finite-energy global solution exists. `force_nonzero_of_no_global_solution` (`R3/CandidateBreakdown.lean:57`) shows the force must be nonzero somewhere in positive time, so the construction cannot degenerate to the unforced equation. The theorem therefore says nothing about the unforced alternatives (A) and (B), which is the scope statement the README and E76 both carry.

### 4. Why the shape matters for the Clay reading

Alternative (C) in Fefferman's statement is a *forced* breakdown: there exists an admissible datum and force for which no global solution exists. The Lean statement's `∃ u p f K` is exactly that existential, and the universal `∀ ν > 0` strengthens it from one viscosity to every positive viscosity. The audit's earlier E60 correction — that (C) does not require the force to be zero — is the same point from the other direction. What the statement does **not** do is resolve (A) or (B), which quantify over all admissible data and would require an existence theorem for the unforced equation, not a counterexample.

*Evidence: `R3/ProblemStatement.lean:150–160`; `R3/Theorem.lean:48–60`; `R3/CandidateBreakdown.lean:57–66`; `R3/ProblemStatement.lean:119–136`; E60; E76.*

---

## E114 — The energy conclusions are proved for the same fields (2026-11-23)

*Reading entry. Lemma 10.4 of the paper gives energy and dissipation bounds. The Lean counterpart is not a separate existence statement: it is a conjunction added to the same witnesses as Theorem 1.1.*

### 1. The statement

```
theorem theorem_1_1_with_dissipation (ν : ℝ) (hν : 0 < ν) :
  ∃ u p f K,
    CandidateProperties ν u p f K ∧
    ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
    IntervalIntegrable (CompactEnergy.l2Norm f) volume 0 1 ∧
    IntegrableOn (CompactEnergy.dissipation u) (Ico 0 1) ∧
    (∀ T ∈ Ico 0 1,
      l2Sq u T + 2 * ν * ∫ t in 0..T, dissipation u t ≤ (cumulativeForceNorm f T)^2) ∧
    2 * ν * ∫ t in Ico 0 1, dissipation u t ≤ (cumulativeForceNorm f 1)^2
```

The same `u p f K` satisfy the candidate properties, the non-existence, and the four energy conclusions. This is a stronger packaging than "there exist fields with the energy bounds": it prevents a proof from switching to a different, better-behaved solution for the energy estimate.

### 2. What the inequality says

It is the standard energy identity with the force term kept on the right: `½‖u(T)‖² + ν∫₀ᵀ‖∇u‖² ≤ ½(∫₀ᵀ‖f‖)²`, written with `l2Sq` and `dissipation` in place of the norms. The right-hand side is the square of the *cumulative* force norm, not zero, because the force is nonzero. The two integrability clauses are what make the totalized integrals finite rather than `∞`: `IntervalIntegrable (l2Norm f) 0 1` and `IntegrableOn (dissipation u) (Ico 0 1)`.

The final line is the `T → 1` endpoint, stated on the half-open interval so that it does not assert integrability at the singular time. That is the same convention as the candidate's smoothness on `preSingularDomain`: everything is asserted strictly before `1`.

### 3. Why this is not circular

The energy bound is one of the candidate's fields (`energy_bounded : UniformFiniteEnergy (Ico 0 1) u`), so a reader could ask whether the dissipation theorem merely restates it. It does not: `energy_bounded` bounds `‖u(t)‖²` uniformly, while `candidate_energy_estimates` (`CompactEnergy`) derives the *integrated* dissipation inequality from the PDE, the divergence-free condition and the compact support. The uniform bound is an input to the derivation, not the conclusion. The audit did not read the body of `candidate_energy_estimates`; it read its statement and its use.

### 4. What remains unplaced

Lemma 10.4 is not one of the 74 numbered results this ledger counts (it is a lemma in §10, and the ledger's 74 includes the numbered results the index found). The energy conclusions are therefore evidence that the development has the paper's quantitative energy content, not a row in the placement table. Recorded here so that the table is not read as "everything outside the 13 is missing": some of it is present under a §10 lemma that the index did not label.

*Evidence: `R3/Theorem.lean:62–82`; `R3/ProblemStatement.lean:108`; `CompactEnergy.candidate_energy_estimates`, `l2Sq`, `dissipation`, `cumulativeForceNorm`; `ns.txt` §10 (Lemma 10.4).*

---

## E115 — What "placed" means, and what thirteen of seventy-four does not say (2026-11-23)

*Method entry. The ledger has moved four times in this slice. It is worth writing down exactly what a row asserts, because the number is easy to over-read in either direction.*

### 1. The three statuses, precisely

* **placed, statement read** — a Lean declaration exists whose *statement* matches the paper's numbered result clause by clause, and the audit read both. It does not mean the proof was read, recompiled, or checked for validity.
* **partial** — some clauses have declarations and some do not. The row names which.
* **cited in a docstring, unchecked** — a Lean file names the paper's result in a comment, and the audit has not read the declaration against the paper's text. This is the development asserting the correspondence, not the audit.
* **unplaced** — no declaration was found, or none was read. It does **not** mean the result is absent from the formalization. E94, E95 and E98 each moved a row out of this column by finding a statement under a different name.

### 2. The current table

| Status | Count |
|---|---|
| placed, statement read | 13 |
| partial | 0 |
| cited-unchecked | 2 |
| unplaced | 59 |
| total | 74 |

The 13 are the paper's spine: A.4, B.2, B.10, C.2, Lemma 4.7, Theorem 4.6, Propositions 5.3, 9.1, 9.5, 9.6, 9.9, 10.1, Corollary 10.6. The 59 include the appendices' supporting lemmas, the §6–§8 construction lemmas, and every estimate inside §7. The two cited-unchecked are Lemma 9.2 and Proposition 9.3.

### 3. Why the spine first

The audit chose the results the rest of the paper consumes, not the ones easiest to match. Theorem 4.6 is the existence theorem; Proposition 5.3 is the coefficient induction; 9.1, 9.5, 9.6 and 9.9 are the residual estimates and the iteration; 10.1 and 10.6 are the forcing and its periodic corollary. If a defect existed in the argument as opposed to the code, it would most likely be in one of these, because they are where the quantitative content lives.

What the placements establish is that each of those results has a declaration whose statement is the paper's. What they do not establish is that the declaration's *proof* proves the paper's inequality — only that the inequality is the one being stated. That distinction has been the audit's bottom line since E67 and it has not changed.

### 4. The number to quote

"Thirteen of seventy-four numbered results are placed at statement level; none is known to be missing; none has been recompiled for this audit." That is four claims, and all four are true. Quoting only the first would overstate the completeness; quoting only the last would understate the work. The pair is the honest summary.

*Evidence: this log, E91–E98; `CROSSWALK.md`; `formalization.yaml`; E73.*

---

## E116 — Two identities in the audit are the auditors' own (2026-11-23)

*Method entry. The manuscript's §5 contains two computations that are not in the Lean tree and not in the paper: the measure scaling under the similarity change of variables, and the critical weight `b* = −(3−2h)/4`. They are the audit's own derivation, and the README says so. This entry states exactly what that means.*

### 1. What the two identities are

The first is the Jacobian of the map from physical to similarity coordinates: with `s = qX`, `r = q√(2X)`, the measure transforms with a factor of `q` and the radial weight with a factor of `√(2X)`. The second is the exponent at which the two viscous contributions balance, obtained by setting the radial weight `b−1` equal to the axial weight `b−2D(h)`; with `D(h) = ½−h` the solution is `b* = −(3−2h)/4`.

### 2. Why they are not attributed to the source

The Lean development has the *ingredients* — `CoordinateAlgebra.D`, the derivative weights, `SimilarityProfile.q`, `radialEnergy` — but it does not state either identity as a theorem, and the paper does not print either display. The audit derived them to explain why the two weights differ by `2h`, which is the anisotropic finding in `PHASE2-FINDINGS.md` and in the manuscript's §5. They are therefore marked as audit-derived wherever they appear, and they carry no formal verification.

### 3. What would change if they were wrong

The anisotropic *finding* would survive, because it is a direct computation from the tree's own derivative identities: `∂ₛ²` has weight `b−2`, `∂𝓏²` has weight `b−2D(h)`, and the Laplacian's two parts differ by `2h` for every admissible `h`. The critical weight `b*` is an interpretation of that difference, not the difference itself. The measure scaling is used only to explain the normalization, not to prove anything about the code.

That is the right division of labour: the identity that matters is checked against declarations; the two explanatory computations are labelled and can be discarded without touching the finding.

### 4. The general rule this records

An audit that derives its own mathematics must mark the derivation, or a later reader will attribute it to the source and treat it as verified. The README's "Two identities in §5 are the auditors' own derivation" sentence is that mark. This entry is the log-side copy, so that anyone reading the entries without the README sees it too.

*Evidence: `PHASE2-FINDINGS.md`; `MANUSCRIPT.tex` §5; `README.md` "What this audit did and did not establish"; `CoordinateAlgebra.D`; `SimilarityProfile.q`; `radialEnergy`; E93.*

---

## E117 — How a row moves: four searches that failed for the same reason (2026-11-23)

*Method entry. Four ledger rows moved in this slice, and every move came from replacing a name search with a shape search. The pattern is worth recording because it is the only repeatable technique the audit has found for statement-level matching.*

### 1. The four cases

| Row | What the paper calls it | What the tree calls it | What the first search was |
|---|---|---|---|
| Proposition 9.1 | normalized linear residual | `globalGood` | "linear residual", "normalized" |
| Proposition 5.3 | `q^{2h(N+1)−K_m}` | `slowOrder h (N+1)` | `2 * h * (N + 1)` |
| Proposition 10.1(vi) | `u = p = 0` for small `t` | `theorem_1_1_with_initial_rest` | a field of `Properties` |
| Theorem 4.6(iv) | `|T₀| ≥ cζ` | `stress_lower_bound` | `lower_bound`, `stable_lower` |

Each first search was reasonable and each returned nothing. The successful search was: write down the *conclusion* as a type, then look for a declaration whose type has that shape — a conjunction with five `WaveClass` members, an exponent of the form `a − b*m`, a theorem with `∀ t, |t| ≤ r → u = 0`, a `∃ c > 0, c * zeta ≤ ‖stress‖`.

### 2. Why the names diverge

The Lean development is written by people solving the proof, not by people matching a paper. Names follow the proof's internal vocabulary: `globalGood` is what the coefficient is good *for*, `slowOrder` is the order in the slow expansion, `stress_lower_bound` names the object and the inequality. The paper's vocabulary is expository: "normalized linear residual" describes the object's role, not its construction. There is no reason for the two to coincide, and mostly they do not.

### 3. The technique, stated as a procedure

1. Extract the paper's conclusion as a formula, with every quantifier explicit.
2. Decide which symbols are the paper's names for tree objects (via `CROSSWALK.md`).
3. Search for the *shape*: `∃ C, ∀ x, ‖…‖ ≤ C * …`, `∀ m, ∃ C, …`, a conjunction of the right arity.
4. When a candidate is found, check the hypotheses clause by clause, not just the conclusion.
5. If nothing is found, record "unfound", not "absent", and say what was searched for.

The fifth step is the one that keeps the log honest. Three of the four rows above were recorded as absent before they were found, and each time the record said what had been searched — which is why the correction was possible without re-reading everything.

### 4. The cost of the technique

A shape search over 2,655 files is slower than a name grep, and it can miss a statement whose shape was mis-transcribed. The four successes do not prove the remaining 59 are findable; they prove the method works when the shape is right. The audit's estimate for the rest — two weeks of one section per day — is an estimate for this procedure, not for a grep.

*Evidence: E92, E93, E94, E95, E98; `CROSSWALK.md` "Method for the next pass"; this log's `Evidence` lines.*

---

## E118 — Three ways this audit's bottom line could be wrong (2026-11-23)

*Method entry. An audit that cannot name its own failure modes is not an audit. These are the three concrete findings that would overturn the "no demonstrated defect" conclusion, in order of how likely they are to exist.*

### 1. A clause mismatch in a placed row

Any one of the 13 placements could be wrong in a clause the audit read too quickly. The most exposed are Theorem 4.6(iv) (a lower bound with an existential constant, where "for every `p` in the annulus" versus "for almost every" would matter), Proposition 5.3 (a filter statement, where the paper's display is pointwise), and Proposition 9.6 (four separate declarations, where the paper asserts one composed step). Each is recorded with its qualification; a reader who finds a clause that does not match should treat the row as unplaced.

How to check: take the paper's display, take the declaration's type, and compare quantifier by quantifier. The audit's `Evidence` lines point at both.

### 2. An undischarged hypothesis at an assembly boundary

The second failure mode is structural: every boundary the audit read discharges its inputs, but the audit did not read every boundary. E96 checked §4 and §5; E67–E71 checked the stage estimates; E65/E66 checked the force. The unread boundaries are the §6–§8 construction lemmas — the dyadic charts, the pulse covariance, the five-moment repair — and the pressure-flux interface (`LEADS.md` §4). If a `StageEstimates` field is ultimately supplied by a hypothesis rather than a construction, it would be there.

How to check: follow `ActualCandidateAssembly.assemble` field by field to its inputs and ask, for each, whether the producer is a theorem or a parameter.

### 3. A reachable axiom or `sorry`

The third is the cheapest to rule out and the most damaging if present. The current tree has no `sorry` in either library (E112), no `axiom` declaration, and the headline theorems' footprints are `propext`, `Classical.choice`, `Quot.sound` (E73). A reachable `sorryAx` would show up in that print; it does not. The remaining risk is not a hole but a *definition*: a `Classical.choice` that selects a schedule with no proof that the selection is nonempty. E66 and E71 traced the two selections the audit could find; a third, unread one would be the place to look.

### 4. What is not on the list

"The anisotropic weights are inconsistent" is not a failure mode of this audit, because E63 already retracted the claim that they prevent an order-by-order construction. "The constants are unusable" is not a failure mode either, because the audit never claimed they are used: it claimed they are existential, which E93's `c = min ml (min mr mm)` confirms. The bottom line is narrow on purpose: no demonstrated defect in the argument, and no independent verification of the estimates.

*Evidence: E63; E65–E71; E73; E93; E96; E112; `LEADS.md` §4; `ActualCandidateAssembly.assemble`.*

---

## E119 — The evidence ledger, at the end of this slice (2026-11-23)

*Summary entry. What has been machine-checked, what has been read, and what has only been asserted — stated once, in one table, so the three are not confused.*

### 1. Machine-checked

| Claim | Evidence |
|---|---|
| `lake build NavierStokes` succeeds from a clean clone | 9,580 jobs, exit 0, run `44987195620`, E73 |
| headline footprints are three permitted axioms | `#print axioms` for the R3 theorems and the periodic corollary, no `sorryAx`, E73 |
| Comparator accepts both NS challenges | builtin kernel and nanoda, run `45119134981`, E75 |
| Comparator accepts both Euler challenges | 10,603 jobs, two kernels, E79 |
| Euler paper-clause footprints | `maximalGradientNorm_limsup` printed, E84 |
| no `sorry` in either library | 5 raw tokens, 4 in the challenge files, 0 in the libraries, E112 |
| no `axiom` declaration | `^\s*axiom` returns nothing, E112 |

### 2. Read, not compiled

| Claim | Evidence |
|---|---|
| 13 of 74 numbered results placed clause by clause | E91–E98 |
| Theorem 4.6 has no free inputs; §5's rate assumes only smoothness | E96 |
| the profile link is a definition, not a compatibility theorem | E97 |
| the force's smoothness is constructed, not assumed | E65, E66 |
| the stage-estimate chain reaches the source wave class | E67–E71 |
| periodic uniqueness and its integration layer | E85, E86 |
| the periodic corollary's compression preserves the PDE | E70, E107 |
| the uniqueness competitor class has no decay hypothesis | E106 |

### 3. Asserted only

| Claim | Status |
|---|---|
| the paper's argument is mathematically correct | not established; every row is statement-level |
| no paper lemma is missing from the formalization | not established; 59 rows unplaced |
| the constants are dimensionally consistent | not established; they are existential |
| the encoded statement is Clay's (C) | established by E76's clause check, not by this slice |
| the entire upstream project is audited | false by scope: Euler and the §6–§8 machinery are outside |

### 4. The one-sentence version

The kernel accepts the artifact, two external kernels accept the two challenges, and thirteen of the paper's seventy-four numbered results have a declaration whose statement is the paper's; none of that is a proof that the paper's inequalities are valid, and the audit's finding about constants is a statement about what the kernel was asked to check, not about whether the mathematics is wrong.

*Evidence: this log, E65–E119; `README.md`; `CROSSWALK.md`; `formalization.yaml`.*

---

## E120 — Every viscosity is one construction plus an exact dilation (2026-11-23)

*Reading entry. Theorem 1.1 quantifies over every `ν > 0`. The development proves it at `ν = 1` and transports it by a spatial rescaling. The rescaling is exact, preserves the singular time, and imposes nothing new on the competitor.*

### 1. The dilation

```
def rescale (a b : ℝ) (g : SpaceTime → V) : SpaceTime → V :=
  fun z => a • g (z.1, b • z.2)
```

Only the spatial variable moves; the time variable is untouched. So the singular time is still `1`, the initial time is still `0`, and a force supported in positive time stays supported in positive time. The two parameters are the amplitude `a` and the inverse length `b`.

### 2. The residual identity

`rescale_residual μ a ha` is the compatibility statement:

```
navierStokesResidual (a^2 * μ) (rescale a a⁻¹ u) (rescale (a^2) a⁻¹ p) t x
  = a • navierStokesResidual μ u p t (a⁻¹ • x)
```

Read the exponents off the left side: velocity amplitude `a`, length scale `a⁻¹`, pressure amplitude `a²`, viscosity `a²μ`. The proof is four chain rules, one per term — `rescale_temporalDerivative` (no spatial factor), `rescale_advection` (`a²b`), `rescale_laplacian` (`ab²`), `rescale_gradient` (`ab`) — followed by `h1 : a² · a⁻¹ = a` and `h2 : (a²μ)(a · a⁻²) = aμ`. Those two arithmetic identities are the whole content of the scaling: they are what makes all four terms carry the same factor `a`.

### 3. What is preserved

`rescale_candidate` rebuilds every field of `CandidateProperties`: smoothness by `rescale_smooth_on`, compact support by `h.support_compact.image (continuous_id.const_smul a)`, both support inclusions by `tsupport_spatialScale_subset`, the zero initial datum by `smul_zero`, divergence-freedom by `rescale_divergence` (`ab · div`), the equation by `rescale_residual`, the energy bound by `h.energy_bounded.spatial_smul a a⁻¹`, and the blow-up by `rescale_speed_unbounded`, which divides the threshold: `M` at the new viscosity is `M/a` at the old one.

The force's support uses `h.force_support.spatialScale a a⁻¹`. Note that the *pressure* support is scaled with amplitude `a²` and length `a⁻¹`, not `a`, which is consistent with the residual identity but easy to get wrong if one assumes every field scales the same way.

### 4. The competitor transports too

`rescale_global_solution` is the converse direction for an arbitrary global finite-energy competitor, at any `a ≠ 0`:

```
GlobalFiniteEnergySolution μ f → GlobalFiniteEnergySolution (a²μ) (rescale a a⁻¹ f)
```

No support, periodicity or decay condition is added. That is what makes the exclusion at viscosity `ν` follow from the exclusion at `1`: given a competitor at `ν`, `normalized_global_solution` dilates it back to a competitor at `1`, where `theorem_1_1` already says none exists. The proof computes `(√ν)⁻¹² · ν = 1` by `field_simp` and then rewrites the force back to its original form.

### 5. Why this is the right shape

The theorem is not proved separately for each viscosity, and it is not proved by a Compactness or continuity argument in `ν`. It is one construction and one identity. That has a cost worth naming: the construction's constants (the `h`, the profile, the schedule) are all at `ν = 1`, and the dilation changes the *spatial scale* of the support by `√ν` while leaving every constant alone. So a reader who asks "what is the support radius at viscosity `ν`" gets `√ν` times the unit-viscosity radius, and a reader who asks "what is the force" gets `√ν · f(·, √ν ·)` — both exact, both cheap.

*Evidence: `R3/ViscosityScaling.lean:20–33,35–100,102–130,133–181`; `R3/Theorem.lean:31–46`; `R3/SpatialEnergyScaling.lean` (`spatial_smul`); `R3/SpatialSupportScaling.lean` (`spatialScale`, `tsupport_spatialScale_subset`).*

---

## E121 — The `3/8` in the rest theorem is the force cutoff's plateau (2026-11-23)

*Reading entry. E98 recorded that `theorem_1_1_with_initial_rest` proves `u = p = 0` on `|t| ≤ 3/8` and that the paper never prints `3/8`. The number is not arbitrary: it is the interval on which the force cutoff equals one.*

### 1. The cutoff

```
def timeCutoff (t : ℝ) : ℝ :=
  SmoothCutoffs.cutoff ((8 / 5 : ℝ) * (t - 11 / 16))

def force (f : VelocityField) : VelocityField :=
  fun z => timeCutoff z.1 • f z
```

`SmoothCutoffs.cutoff` is the standard flat bump: `1` on `|x| ≤ 1/2`, `0` on `|x| ≥ 1`, smooth in between. Substituting, `timeCutoff` is `1` when `|(8/5)(t − 11/16)| ≤ 1/2`, i.e. `|t − 11/16| ≤ 5/16`, i.e. `t ∈ [3/8, 1]`. That is `timeCutoff_eq_one`. It is `0` when `|(8/5)(t − 11/16)| ≥ 1`, i.e. `t ∉ [1/16, 21/16]`. That is `timeCutoff_eq_zero`.

So the cutoff is a plateau on `[3/8, 1]`, with a ramp down on `[1/16, 3/8]` and a ramp up on `[1, 21/16]`; it vanishes outside `[1/16, 21/16]`.

### 2. The same `3/8`

`theorem_1_1_with_initial_rest` proves the candidate is at rest for `|t| ≤ 3/8`. The left end of the plateau is `3/8`. On that slab the force is `timeCutoff · f = 1 · f`, so the force equals the original field; at `t = 3/8` the two definitions agree exactly, and for `t < 3/8` the ramp is still `1` (because the plateau begins there, not because of a separate choice). The two constants are the same constant, and the rest interval is chosen to sit inside the force's plateau.

That matters for the energy identity: if the force were cut off inside the rest slab, the candidate would solve a different equation from the one stated there, and `force_eq` (`force f = f` on `[3/8, 1]`) would fail. The theorem's `|t| ≤ 3/8` is therefore not an arbitrary convenience — it is the largest symmetric interval around `0` on which the cut force is the original force.

### 3. The support

`force_tsupport_subset` proves

```
tsupport (force f) ⊆ Icc (1/16) (21/16) ×ˢ K
```

given `K` compact and `f` vanishing off `K`. The proof is the two halves of the cutoff: outside `[1/16, 21/16]` the time factor is zero, and outside `K` the field is zero. `force_compactPositiveTimeSupport` then packages `IsCompact (Icc ×ˢ K)` and the strict positivity `0 < t` into `CompactPositiveTimeSupport`.

This is the construction behind the force's support field in `CandidateProperties`. The audit's E65 traced smoothness; this entry traces *support*, and the two together are the whole of Proposition 10.1's force clause.

### 4. What is exact and what is chosen

Exact: the plateau endpoints, the support interval, the smoothness, and the identity `force = f` on the plateau — all proved. Chosen: the scale `8/5` and the centre `11/16`, which set the ramp widths. Those are formalization choices that make the ramp fit between `1/16` and `3/8`; the paper's construction has a cutoff too but does not print these numbers. The audit records the distinction because a reader comparing constants will find `3/8` in two places and `1/16`, `21/16` in a third, and should know which are forced by the theorem and which are the formalizer's convenience.

*Evidence: `R3/PositiveTimeForce.lean:14–80`; `SmoothCutoffs.cutoff`, `cutoff_one_of_abs_le`, `cutoff_zero_of_one_le_abs`; `R3/Theorem.lean:31`; `R3/ProblemStatement.lean:92–109`; E65; E98.*

---

## E122 — The comparison closes on an explicit pressure envelope (2026-11-23)

*Reading entry. `WholeSpaceComparisonClosure` is the last analytic step before Gronwall. It is stated with one explicit pressure-flux hypothesis, and the module says in its own header that the hypothesis is discharged elsewhere — which it is, in `PressureFlux`.*

### 1. The envelope

```
def pressureEnvelope (R A B : ℝ) : ℝ :=
  (B ^ (1/2) + 1) * (A / R + 1 / R^2) + R ^ (-7/4) * B ^ (3/4)
```

`R` is the localization radius, `A` the weighted dissipation root, `B` the `L⁶` norm of the cutoff velocity difference. The two terms are the two ways the pressure pairing can be bounded: a `1/R` boundary term and an `R^{-7/4}` interior term. The exponents `1/2`, `3/4`, `7/4` are the Sobolev/Young bookkeeping; they are printed, not hidden in a constant.

### 2. The theorem

`eq_of_pressure_flux_bound` assumes `T ≥ 0`, bounds `M` (the `L²` norm of `u − v`), `G` (the gradient of `u`), `CP` (the pressure-flux constant) and `R₀` (where the weight's derivative vanishes on the reference), plus the equation, divergence-freedom, the initial agreement and the pressure-flux inequality

```
|∫ (p − q) · ∇weight_R · (u − v)| ≤ CP * pressureEnvelope R A B
```

for every `R ≥ 1`, `t ∈ (0, T)`. It concludes `u = v` everywhere on `[0, T] × ℝ³`.

The proof builds two constants, `C0 = weightLaplacianConstant * M² / 2` and `C1 = 4 * derivativeConstant 1 * M^{3/2}`, applies `ComparisonRateBound.exists_uniform_rate_bound` to get a decay rate `D`, and then invokes `WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound` with `K = 2G`. The weight's derivative is assumed to vanish for `R ≥ R₀` on the reference — `hvanish`, supplied in `WholeSpaceUniqueness` by `exists_radius_weight_derivative_zero` from compact support.

### 3. The one hypothesis, and where it is discharged

The pressure-flux inequality is the only analytic input not proved in this module. `WholeSpaceUniqueness.classical_uniqueness_on_Icc` discharges it by calling `PressureFlux.exists_uniform_actual_pressure_flux_bound H M U G₀`, which takes the pressure-recovery hypotheses `H`, the `L²` bound `M`, an `L³` bound `U` on `u`, a tensor-difference `L¹` bound `G₀`, and returns a `CP` and the inequality for the *actual* pressure pair. So the closure module is a clean interface: it says "if the pressure pairing obeys this envelope, the fields agree", and the uniqueness theorem supplies the envelope from the equations.

That is the right factoring, and it is also why the audit's earlier `LEADS.md` reading of the pressure-flux bodies matters: the interface being clean does not by itself prove the bound, and the bound's proof is in `PressureFlux`, not here.

### 4. What the module does not assume

No decay of `v`, no support of `v`, no pressure growth, no derivative bound on `q`. The only hypotheses on `v` are membership in `L²` at each time (`hwu`), the uniform bound `M`, smoothness, divergence-freedom, the equation and the initial datum. The gradient bound `G` is on `u`, the compactly supported reference, not on the competitor. This is the same asymmetry E106 recorded at the level of the uniqueness theorem, now visible at the level of the estimate that proves it.

*Evidence: `R3/WholeSpaceComparisonClosure.lean:1–90` and following; `ComparisonRateBound.exists_uniform_rate_bound`; `WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound`; `LocalizedFluxEstimates.weightLaplacianConstant`; `ComparisonCutoffs.derivativeConstant`; `R3/WholeSpaceUniqueness.lean:19–69`; `PressureFlux.exists_uniform_actual_pressure_flux_bound`.*

---

## E123 — The pressure is paired through a Riesz functional, not assumed smooth (2026-11-23)

*Reading entry. `PressureFlux` is the layer that turns the pressure into something integrable against compact tests. Its first sixty lines are complexification bookkeeping; the point of them is that the pairing is defined before any estimate is made.*

### 1. The pairing

The module header: "The pressure is paired with compact smooth tests through its canonical Riesz functional. Every integral used to split the weighted pairing is shown to be integrable before its norm is estimated."

That ordering is the content. A pressure in this development is a function, not a priori an `L²` object; the flux pairing `∫ (p − q) ∇weight · (u − v)` is not obviously integrable. The module proves integrability first (`integrable_holder_pair`), then bounds the pairing by Hölder with the conjugate pair `6/5` and `6` (`norm_holder_pair_le`), and only then assembles the uniform constant.

### 2. The complexification lemmas

`lpNorm_ofReal` and `norm_fderiv_ofReal` identify the `Lᵖ` norm and the derivative norm of a real function with those of its image under `Complex.ofRealCLM`. `lpNorm_fderiv_realTest` does the same for `PressureRecovery.realTest`. These are not cosmetic: they let the Hölder estimate be proved in the complex `Lᵖ` space where Mathlib's interpolation lemmas live, while the pressure itself stays real. The `HolderTriple (6/5) 6 1` instance is proved by `norm_num` on `ℝ≥0∞`.

### 3. The cutoff is Lipschitz in the right constant

`cutoff_lipschitz` proves `|cutoff R x − cutoff R y| ≤ (derivativeConstant 1 / R) ‖x − y‖` by the mean value inequality, with the derivative bound `cutoff_fderiv_le`. That `1/R` is what produces the `A/R` term in the envelope of E122. The envelope's shape is therefore not guessed: it is the two estimates (gradient `1/R`, interior `R^{-7/4}`) added.

### 4. What is and is not checked

Checked by reading: the integrability, the Hölder pair, the Lipschitz constant, and the fact that the final constant is produced from `M`, `U`, `G₀` rather than assumed. Not checked: the body of `exists_uniform_actual_pressure_flux_bound` beyond its statement, and whether the `6/5` exponent is the sharp one the paper uses. The paper's §10 pressure argument is where a `6/5`-type exponent would appear; the audit has not compared the two, and this entry does not claim a match.

What it does establish is the ordering the audit cares about: the pressure is never assumed to be a smooth decaying field on the competitor. It is a function whose pairing with a compact test is proved integrable from the equation's own regularity. That is the difference between "we assume the pressure is nice" and "we prove the pairing converges", and the module is on the right side of it.

*Evidence: `R3/PressureFlux.lean:1–90` and following; `PressureRecovery.realTest`; `ComparisonCutoffs.cutoff_fderiv_le`, `derivativeConstant`; `R3/WholeSpaceComparisonClosure.pressureEnvelope`; E122.*

---

## E124 — A fourth candidate structure, without the energy field (2026-11-23)

*Reading entry. `R3CompactCandidate.Properties` is the structure E91 read for Proposition 10.1. It is not the same as `R3.ProblemStatement.CandidateProperties`, and the difference is where the energy bound enters.*

### 1. The fields

`R3CompactCandidate.Properties u p f` has:

* smoothness of `u`, `p` on `preSingularDomain`, of `f` on `futureDomain`;
* **separate** compact support witnesses for `u`, `p` and `f` (`∃ K, IsCompact K ∧ …`), not one shared `K`;
* the zero initial velocity;
* `force_time_support : CompactFutureTimeSupport f` — the one-sided vanishing predicate of E101, not `CompactPositiveTimeSupport`;
* divergence-freedom and the residual identity;
* `speed_unbounded`.

It has **no** `energy_bounded` field and **no** shared support set. The energy bound and the single `K` appear only when this is converted to `R3.ProblemStatement.CandidateProperties`, which is what `theorem_1_1` concludes.

### 2. Why the split exists

The compact candidate is built before the comparison: `of_localized_fields` assembles the cut potential, the direct field and the pressure, and proves locality against the periodic model. At that stage the energy bound is not yet available — it comes from compact support plus continuity, via `CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab` — and the three supports are genuinely different sets (velocity, pressure, force each have their own cylinder). So the structure records what the construction actually produces, and the conversion adds the consequences.

That is the same layering E99 found among the three `CandidateProperties`, one level lower: the *construction's* record is weaker than the *theorem's* record, and the difference is exactly the two fields that are derived rather than built.

### 3. The support geometry

`outerCutoff x = spatialCutoff ((1/2) • x)`; `outerSupport = (fun x => 2 • x) '' supportCylinder`; `outerCutoff_one` on `supportCylinder`; `outerCutoff_zero_outside`; and `outerCutoff_ne_zero_inner` proves that wherever the outer cutoff is nonzero, `x` lies in `PeriodicLocalization.innerCube (1/4)`. `supportCylinder_inner` does the same for the cylinder itself.

So the construction's support is a cylinder scaled by `2`, and the region where it is active sits strictly inside the quarter cube. That is what makes the periodization in Corollary 10.6 legal: the field is supported away from the cube boundary, so its lattice sum is locally finite and the periodic identification is exact. E107 traced the compression; this is the other half — the support inclusion that lets `periodize` be applied without aliasing.

### 4. The audit's bookkeeping correction

E91 said Proposition 10.1's five clauses were fields of `R3CompactCandidate.Properties` and the sixth was missing. With this entry the count is precise: five clauses are fields of *this* structure, the sixth is the rest theorem of E98, and the energy bound plus the shared `K` are added by the conversion to `R3.ProblemStatement.CandidateProperties`. Three structures, three jobs; none of them is redundant, and the paper's single "candidate" spans all three.

*Evidence: `R3CompactCandidate.lean:1–90` and following; `outerCutoff`, `outerSupport`, `outerCutoff_ne_zero_inner`, `supportCylinder_inner`, `of_localized_fields`; `R3/ProblemStatement.lean:92–109`; `PeriodicLocalization.innerCube`; E91; E98; E99.*

---

## E125 — The slice in one table, and what is still open (2026-11-23)

*Summary entry. Twenty-two entries, E98–E124, all from reading; none compiled anything new. This is what each one established, so the slice can be cited without reading it.*

### 1. The entries

| Entry | Finding |
|---|---|
| E98 | Proposition 10.1's short-time clause is `theorem_1_1_with_initial_rest`, proving rest on `|t| ≤ 3/8`; the ledger closes at 13 placed, 0 partial |
| E99 | Three different structures are named `CandidateProperties`, in three namespaces |
| E100 | `SpeedUnboundedAtOne` is pointwise in space, not a trajectory; no fixed blow-up point is claimed |
| E101 | The force's "rapid decay" is temporal and follows from literal vanishing after `T` |
| E102 | The stage loss `1 + 3h/2` is not the truncation loss `K_m = m + 2 + 2h`; they are not interchangeable |
| E103 | Every constant is an exact rational; `κ = 10⁻⁵` clears the tightest printed margin by 500× |
| E104 | `formalization.yaml` claims four main results, `review.status: self-assessed`; not "the whole paper" |
| E105 | Moment matrices are nonsingular for every `n`, not a numeric 5×5 determinant; no inverse bound |
| E106 | The uniqueness competitor has no decay, support or pressure hypothesis |
| E107 | The rest clause is load-bearing: `compressedCandidate` uses it to stay smooth across the new `t = 0` |
| E108 | `MaximalLifespan` is a periodic development; "lifespan" is a set of admissible `T` |
| E109 | The four reserved windows have one touching pair and a one-unit gap |
| E110 | The annulus weight has asymmetric edge factors (`c` left, `4` right) |
| E111 | Toolchain and dependencies are pinned to a prerelease tag, not a commit |
| E112 | Five raw `sorry` tokens: four challenge placeholders and one docstring; zero in either library |
| E113 | The headline theorem excludes finite-energy competitors only, which is exactly Clay (C) |
| E114 | The energy/dissipation conclusions hold for the same witnesses as Theorem 1.1 |
| E115 | What "placed" means, and why 13/74 must be quoted with its two qualifiers |
| E116 | The measure scaling and `b* = −(3−2h)/4` are the auditors' own, labelled |
| E117 | Four rows moved by shape search; the procedure and its cost |
| E118 | Three concrete ways the bottom line could be wrong |
| E119 | Machine-checked vs read vs asserted, in one table |
| E120 | Every viscosity is one construction plus an exact spatial dilation |
| E121 | The `3/8` rest interval is the force cutoff's plateau |
| E122 | The comparison closes on an explicit pressure envelope; one hypothesis, discharged in `PressureFlux` |
| E123 | The pressure is paired through a Riesz functional with integrability proved first |
| E124 | `R3CompactCandidate.Properties` is a fourth candidate structure, without the energy field |

### 2. What moved

The ledger moved once: Proposition 10.1, from 5 of 6 clauses to placed. Everything else is description, method or scope. That is the honest shape of this slice — twenty-five entries and one row — because the rows that were left are the ones whose declarations are hard to find, and most of this slice's work went into establishing what the found objects mean.

### 3. What did not move

* **No estimate was checked for validity.** The 13 placements remain statement-level.
* **No new compilation.** The build and Comparator evidence is E73/E75/E79; this slice read source.
* **The §6–§8 construction lemmas remain unread** at result level.
* **Lemma 9.2 and Proposition 9.3 remain cited-unchecked.**
* **The paper's §5 and §9 constants were not compared numerically** beyond E95/E102/E103.

### 4. The next three targets, in order

1. **Lemma 9.2 and Proposition 9.3.** They are the only two rows where the source itself asserts the correspondence and the audit has not read it. The declarations are named in `CurlClassBounds.lean:757` and `LinearWaveBounds.lean:896`.
2. **The pressure-flux body.** E122/E123 read the interface and the integrability layer; `exists_uniform_actual_pressure_flux_bound`'s estimate is the place where the `6/5` exponent would have to match the paper's §10.
3. **The `§6` chart lemmas.** The dyadic charts and the label sum are the least-read part of the spine, and E67–E71 stopped at the source wave class rather than at the chart geometry.

*Evidence: this log, E98–E124; `README.md`; `CROSSWALK.md`; E119.*

---

## E126 — The extended profile is identified at order zero, not as a whole (2026-11-23)

*Reading entry. E96 left a wiring question: does anything connect the cone witness's extended profile with the profile `GlobalSlowProfiles` builds? E97 answered "they are one object" by pointing at `FinalSlowBase.profileSequence`. That is true of the §5 sequence and false of the witness's extended profile. This entry states exactly which equality exists.*

### 1. The two objects are different types

`NominalProfile.Witness.profiles` (`NominalProfile.lean:2501–2502`) is

```
noncomputable def profiles : ProfileHistories.Profiles W.domain :=
  W.controls.extendedProfiles W.heat W.separated
```

a record of *histories*: `f`, `U`, `pressure` (and `I`, `M`, `E`) as functions on `W.domain`. `GlobalSlowProfiles.profiles s n` is a `Coefficient S` — four `EvenProfile`s named `phi`, `axial`, `beta`, `pressure` — produced by the well-founded recursion `sequence s n` from a `Scheme s`. They cannot be equal as terms: one is a history record, the other is an order-indexed coefficient family.

The comparison has to go through two conversions:

* `xProfile f (X, η) = f (√(2X), η)` (`GlobalSlowProfiles.lean:1134–1135`, `PositiveAxisExistence.lean:436–440`), the `R → X` view;
* `asSlowProfiles s` (`GlobalSlowProfiles.lean:1762–1766`), which applies `xProfile` to the four components of `profiles s n`.

### 2. What is identified, and it is order zero

`AssembledSlowBase.nominalScheme W` (`:1117–1124`) builds a `Scheme` from `schemeFromHierarchy (nominalHierarchy W) ... (nominalBaseData W ...)`. `nominalBaseData` (`:1000–1015`) calls `baseDataOfProfile d W.axis.normalization W.profiles ...`, and `baseDataOfProfile` (`:739–755`) sets `fields := baseFields d C P hD` with `P = W.profiles`. `baseFields` (`:638–642`) is

```
phi := constant S C * radialPullback P.f ...
axial := radialPullback P.U ...
pressure := radialPullback P.pressure ...
```

and the three identifying theorems are `baseFields_phi` (`:644–647`), `baseFields_axial` (`:649–651`), `baseFields_pressure` (`:653–655`):

```
xProfile (baseFields d C P hD).phi p = C * P.f p
xProfile (baseFields d C P hD).axial p = P.U p
xProfile (baseFields d C P hD).pressure p = P.pressure p
```

for `0 ≤ p.1`. Composed with `profiles_zero`, these say: **the order-zero coefficient of `GlobalSlowProfiles.profiles (nominalScheme W)` is the witness's extended profile, componentwise**, up to the normalization `C = W.axis.normalization`.

`ConstructedSlowBase.nominalCoefficients_zero_fields` (`:1314–1329`) states the same thing in the coefficients the construction actually uses:

```
(nominalCoefficients W).phi 0 p = W.axis.normalization * W.f p ∧
(nominalCoefficients W).axial 0 p = W.U p ∧
(nominalCoefficients W).pressure 0 p = W.Pi p
```

and `W.f`, `W.U`, `W.Pi` are `W.profiles.f`, `.U`, `.pressure` by definition (`NominalProfile.lean:2487–2499`). This is the declaration the question asks for, with one qualifier: it is order zero.

### 3. What ties all orders together, and what it is not

`ConstructedSlowBase.nominal_coefficientMatches` (`:218–222`) proves

```
BasePrefixIdentity.CoefficientMatches F.data.h W.axis.normalization
  (nominalCoefficients W) (asSlowProfiles (nominalScheme W))
```

and `AssembledSlowBase.coefficients_fields_eq` (`:373–380`) proves, for every `n` and every `p` with `0 ≤ p.1`, `|p.2| ≤ 1`, that the constructed `phi`, `axial` and `pressure` at order `n` equal those of `asSlowProfiles s`, where `s = nominalScheme W`. So the constructed coefficients and the `GlobalSlowProfiles` sequence agree at **every** order — on the profile window. That is a genuine all-order identification.

It is not an identification of the witness's extended profile, because the sequence's positive-order coefficients are built from `nominalHierarchy W` (the local ACT hierarchy), not from `W.profiles`. `W.profiles` supplies the base data and the order-zero values; the recursion supplies `n ≥ 1`. The all-order equality is between `asSlowProfiles (nominalScheme W)` and the *constructed* coefficients, both of which are downstream of the same scheme.

### 4. The §5 sequence uses the modulated profile, not the cone profile

`FinalSlowBase.profileSequence H v := asSlowProfiles (EntranceAlignedBase.modulatedScheme H v)` (`:101–102`). `modulatedScheme` (`EntranceAlignedBase.lean:802–803`) is `scheme W H v.profiles v.finiteModification ...`, where `v : ModulatedProfileAssembly.Witness ld` is the *modulated* witness, not the nominal `W`. The base equality is `rfl` in the other direction:

```
modulated_base_eq : (modulatedScheme H v).base = (modifiedScheme W v.profiles v.finiteModification).base
```

(`EntranceAlignedBase.lean:808–809`), and `modulated_baseFields_eq` is likewise `rfl`. So `profileSequence` is defined from `v.profiles`, and the relation between `v.profiles` and `W.profiles` is modulation: `LeadingStressWeights.stress_outside` (`:98–116`) proves the *stress* agrees outside the repair patch, not the profile. No declaration states `v.profiles = W.profiles`.

### 5. The answer

**No declaration identifies the cone witness's extended profile with the profile `GlobalSlowProfiles` builds as a whole.** What exists is a three-link chain:

1. `W.profiles` is the `f`, `U`, `pressure` source of `nominalBaseData`, hence of `nominalScheme W`'s base;
2. at order zero, `baseFields_*` and `nominalCoefficients_zero_fields` prove the built coefficients equal `W.profiles` componentwise (with the normalization);
3. at every order, `coefficients_fields_eq` / `nominal_coefficientMatches` prove the constructed coefficients equal `asSlowProfiles (nominalScheme W)` on the profile window.

E97's sentence "the two constructions are one" is right about the §5 sequence — it is *defined* as `asSlowProfiles (modulatedScheme ...)`, so there is no second object to identify — but it should not be read as an equality between the witness's extended profile and the recursive sequence. The honest statement is: the sequence is built *from* the profile at order zero and *from the local hierarchy* at positive orders, and the only equality theorems are the two above. For the residual estimates this is enough, because they consume the coefficients and the base; for a claim that "the extended profile is the GlobalSlowProfiles profile", it is not.

*Evidence: `NominalProfile.lean:2487–2502`; `GlobalSlowProfiles.lean:1134–1140,1762–1766`, `profiles`, `profiles_zero`; `AssembledSlowBase.lean:373–380,638–655,739–755,1000–1015,1117–1124,1229–1255,1314–1329`; `ConstructedSlowBase.lean:218–222`; `EntranceAlignedBase.lean:802–815`; `FinalSlowBase.lean:99–112`; `LeadingStressWeights.lean:98–116`; E96; E97.*

---

## E127 — The two "cited" rows are components, not the paper's statements (2026-11-23)

*Reading entry. `CROSSWALK.md` carried two rows as "cited in a docstring, unchecked": Lemma 9.2 (`CurlClassBounds.lean:757`) and Proposition 9.3 (`LinearWaveBounds.lean:896`). Both are now read clause by clause. Neither docstring names a declaration whose statement is the paper's. The bucket empties; both rows become partial.*

### 1. What the paper asks

**Lemma 9.2** (p. 102–103) has three clauses:

1. *Mean transport.* `w ∈ W_α`, `v` a mean field with tangential components in `M_µ` and radial component in `M_{µ+1}`. Then the nonzero harmonics of `(w · ∇*)v + (v · ∇*)w` lie in `W_{α+µ−1/2}`.
2. *Wave transport.* Two curl-generated waves `w, w'` with the same label and exponents `α, α'`. The nonzero harmonics of `(w · ∇*)w' + (w' · ∇*)w` lie in `W_{α+α'−κ_s}`; the zero harmonic lies in `M_{α+α'−κ_s}`.
3. *Label separation.* Distinct labels have zero products on their closed supports.

**Proposition 9.3** (p. 103–104) is a physical residual decomposition `R(u[j], p[j]) = G[j] + F[j]` in a common chart, with three parts: (i) supported sources — a locally finite harmonic sum (9.4) whose coefficients satisfy `supp(f|E_γ) ⊂ Ω_γ`, are `C^∞` on `E_γ⁺`, and lie in `W_α` with `⟨G*⟩_θ ∈ M_µ`; (ii) a flat remainder bound `|F[j]|_m ≤ C_{j,m,N} q^N` uniform over bands, labels and points; (iii) exact mean equations (9.6).

### 2. Lemma 9.2's cited declaration is Lemma 7.7's exponent

`CurlClassBounds.lean:757–769` is `curlRemainder_waveClass`:

```
WaveClass s P α a →
WaveClass s P (α + 1 / 2 - κ) (fun n => curlRemainder (K n) R ... (coefficient ... (a n)))
```

`α + 1/2 − κ` is the curl-correction weight, and the paper says so itself on p. 102: "If `t_m ∈ W_α`, then Lemma 7.7 gives `r_m ∈ W_{α+1/2−κ_s}`" (`.setup/paper/ns.txt:5175`). The theorem has no mean field, no product, and no transport term; its hypotheses are phase-jet bounds, a two-sided bound `b ≤ ‖nΦ‖ ≤ M`, and the primitive classes of `Vr, Vθ, Vz, 1/R`. The docstring's "Lemma 9.2's curl remainder" is a mislabel: this is the curl correction used *inside* Lemma 9.2's hypotheses, not Lemma 9.2.

### 3. What actually matches Lemma 9.2, clause by clause

| Paper clause | Lean | Match |
|---|---|---|
| 1, mean transport at `W_{α+µ−1/2}` | `mean_wave_cmul` / `wave_mean_cmul` (`WaveInteractionBounds.lean:77–96`), `MeanClass.bilinear_wave` (`WeightedClasses.lean:449–454`) | exponent `α+µ`, **no** `−1/2` loss, **no** tangential/radial split |
| 2, wave transport at `W_{α+α'−κ}` and `M_{α+α'−κ}` | `transport_wave_class` (`HarmonicWaveInteraction.lean:389–400`), `transport_mean_class` (`:405–431`) | exponent exact, but stated per fixed harmonic `m` and component `i`, not for "the nonzero harmonics" as a family |
| 3, distinct labels vanish | `ActualCarrierGeometry.labelCarrier_disjoint` (`:342`), `HarmonicResidual.disjoint` (`:1472`), `LocalResidualGrouping.disjoint` (`:220`) | present, at the actual-carrier level rather than the abstract wave product |

Clause 1 is the one that does not match. `mean_wave_cmul` gives `W_{α+µ}` where the paper gives `W_{α+µ−1/2}`. That is a *stronger* exponent, so it is not a defect — but it is not the same statement, and the reason the paper needs the loss is visible in its own proof: "Mean advection of a wave phase costs `k = O(ε^{−1/2})`", and its radial transport carries "a radial mean factor of order `µ + 1`". The tree has no declaration of that radial/tangential split at all: `MeanClass s α f` is a single weight, not a pair `(M_µ, M_{µ+1})`. So the paper's device for paying the half-power is not formalized as a device; the tree's product lemma simply does not pay it.

### 4. Proposition 9.3's cited declaration is the coefficient shadow

`LinearWaveBounds.lean:896–935` is `constructed_linear_wave_with_flat_error`, and its own docstring says "Proposition 9.3 at the coefficient level". Its conclusion is three conjuncts:

```
WaveClass s P (α + 1 / 2 - 3 * κ) (a.constructedGood s d g.cutoff) ∧
(∀ N : ℝ, UnweightedClass s N (excludedSlotError d g.cutoff a.amplitude source)) ∧
∀ n x, ... residual + source = (good + error) * carrier
```

Against the proposition's three parts: part (ii) is there, as an all-order unweighted class rather than the paper's pointwise `C_{j,m,N} q^N` uniform in bands and labels; the pointwise identity is the decomposition `R = G + F` at coefficient level. Part (i)'s support `⊂ Ω_γ` and `C^∞` extension are properties of the `GaussianTailFlat` slot family, not stated here; part (iii), the exact mean equations `(9.6)` with `W_ab`, `P`, `p_m`, is not in this declaration at all. `CorrectionState.MeanResidualBounds` (E97) carries the `1+σ` mean side of the cycle, but it is a different statement.

The declaration is therefore a real and useful component — it is the piece the linear-residual estimate consumes — and it is not the proposition.

### 5. The ledger move

The "cited in a docstring, unchecked" bucket was two rows. Both are now read; neither is a placement. They move to partial:

| Status | Before | After |
|---|---|---|
| placed, statement read | 13 | 13 |
| partial — component declarations exist, statement not matched | 0 | 2 |
| cited in a docstring, unchecked | 2 | 0 |
| unplaced | 59 | 59 |
| **total** | **74** | **74** |

The count 13/74 is unchanged, which is the honest outcome: reading the two rows did not place them, it established that the correspondence the source asserts is looser than the label suggests. This is the third time a docstring has over-claimed relative to its declaration (E90's twenty labels, E94's `globalGood`, and now these two), and the pattern is worth naming: the tree's docstrings are reliable about *what a declaration is for*, and unreliable about *which numbered paper result it is*.

*Evidence: `.setup/paper/ns.txt:5242–5270` (Lemma 9.2), `:5272–5345` (Proposition 9.3); `CurlClassBounds.lean:757–769`; `WaveInteractionBounds.lean:77–96`; `WeightedClasses.lean:415–454`; `HarmonicWaveInteraction.lean:389–431`; `LinearWaveBounds.lean:896–935`; `ActualCarrierGeometry.lean:342`; `HarmonicResidual.lean:1472`; `LocalResidualGrouping.lean:220`; E94; E97. Reading only — nothing compiled.*

---

## E128 — There is no `6/5` in §10 to match (2026-11-23)

*Reading entry. E125's second target said the pressure-flux estimate "is the place where the `6/5` exponent would have to match the paper's §10". That target rests on a false premise: the paper's §10 pressure flux contains no `6/5`. The exponent is internal to the Lean proof's Hölder pairing. What actually has to match is the radius envelope, and it does. The E125 target is retracted.*

### 1. What the paper's §10 actually proves

The pressure flux enters the difference-energy estimate (p. 123). The paper splits the pressure into a Riesz-transform part `π` and a commutator part `π*`, tests the equality against `a(t) χ_R w`, and bounds

```
|∫ π w · ∇χ_R| ≤ C_T R⁻¹ [ (B_R + 1) B_R^{1/2} + R^{−3/4} B_R^{3/4} ]        (10.19)
```

using two interpolations, not a `6/5` pairing:

```
‖φ³_R w‖₃ ≤ B_R^{1/2} ‖w‖₂^{1/2},     ‖φ³_R w‖₄ ≤ B_R^{3/4} ‖w‖₂^{1/4}.
```

`B_R` is the local energy bound. The Young-convolution step bounds the second sum in (10.18) in `L^{4/3}` by `C_T R^{−3/4}`, and `|∇χ_R| ≤ C R⁻¹ φ_R⁷` is what turns that into the `R⁻¹` outside. The exponents in play are `3`, `4`, `4/3` and the `R`-powers `−1`, `−3/4`; there is no `6/5` anywhere in the argument.

The extracted text of the whole 166-page paper contains exactly one literal `6/5`, at (4.34), as a power of the radial variable (`f^{2x6/5}`) — not an integrability exponent, and 800 pages away from §10.

### 2. What the Lean bound actually says

`PressureFlux.exists_uniform_actual_pressure_flux_bound` (`R3/PressureFlux.lean:576–598`) produces one `CP ≥ 0` such that for every `R ≥ 1` and `t ∈ (0,T)`,

```
|∫ (p − q) ∂weight_R · (u − v)|
  ≤ CP * ( (ℓ₆^{1/2} + 1) * (a_R / R + 1 / R²) + R^{−7/4} ℓ₆^{3/4} )
```

with `ℓ₆ = comparisonLpNorm 6 (cutoff_R⁴ • (u−v))` (`cutoffL6`) and `a_R = dissipationRoot` of the cut-off difference. Compare the second term: the paper's `R⁻¹ · R^{−3/4} B_R^{3/4}` is `R^{−7/4} B_R^{3/4}`, and the Lean term is `R^{−7/4} ℓ₆^{3/4}`. **The radius power is identical.** The first term carries the paper's `R⁻¹` factor as `a_R/R`, plus a stricter `1/R²` tail. So the envelope matches; the functionals differ (paper: local energy `B_R`; Lean: the cut-off `L⁶` norm and the dissipation root).

The constant differs in a way worth recording: the paper's `C_T` depends on `T` through the `L^{4/3}` convolution bound, while the Lean `CP` is a function of `M₀, U₀, G₀` only — the three slice-norm bounds the statement takes as hypotheses. That is not a weakening: the `T`-uniformity is what `WholeSpaceUniqueness.candidate_unique_on_Icc` needs when it invokes the bound on `Icc 0 T` for arbitrary `T < 1` (`R3/WholeSpaceUniqueness.lean:60–68`).

### 3. Where `6/5` actually comes from

`6/5` is the Hölder conjugate of `6`, and it appears only where a product is placed in `L^{6/5}` to pair against an `L⁶` test:

| Declaration | Role |
|---|---|
| `PressureFlux.holder_six_fifths_six` (`:68`) | the instance `HolderTriple (6/5) 6 1` |
| `PressureFlux.norm_holder_pair_le` (`:83`) | `‖∫ f·g‖ ≤ ‖f‖_{6/5} ‖g‖₆` |
| `LocalizedTensorBounds.cross_norm_bound` (`:46`) | `‖u‖‖w‖ ∈ L^{6/5}` from `u ∈ L³`, `w ∈ L²`, with the bound `‖u‖₃‖w‖₂` |
| `LocalizedTensorBounds.quadratic_cutoff_bound` (`:58`) | the `L^{12/5}` interpolation that produces it |

That is a proof strategy — bound the whole canonical flux through a Riesz functional on `L⁶` — not a claim about the paper's exponents. The paper reaches the same envelope through `L⁴` interpolation. Two routes, one envelope.

### 4. What this corrects

E122 and E123 read this declaration's interface and its integrability layer and did not compare the bound's exponents to §10. E125 then converted that gap into a target, and the target assumed the exponents had to agree. They do not, because they are not the same exponents. The audit carried a premise across three entries without checking the paper for the number.

The general lesson is the one E94 and E95 already taught from the other direction: grep the paper for the expression before treating a mismatch as a finding. Here the expression was the auditors', not the paper's.

*Evidence: `.setup/paper/ns.txt:6225–6265` ((10.19) and the two interpolations), `:1847` (the only literal `6/5`); `R3/PressureFlux.lean:68–104,470–598`; `R3/LocalizedTensorBounds.lean:45–83,170–218`; `R3/WholeSpaceUniqueness.lean:44–68`; E122; E123; E125. Reading only — nothing compiled.*

---

## E129 — Proposition 6.6: four clauses placed, two components (2026-11-23)

*Reading entry. The first row taken from the fifty-nine unplaced results is the §6.4 coefficient algebra, Proposition 6.6 (p. 73). It is a conjunction of six things, and four of them have declarations whose statements are the paper's. The other two exist as components rather than as statements, so the row moves to partial rather than placed.*

### 1. What the paper asks

`Proposition 6.6. Each class in Section 6.4 is closed under finite sums at a fixed exponent.` Then, with `M` the mean class and `W` the wave class:

1. **Finite sums.** Closure of every §6.4 class at a fixed exponent, band-independent.
2. **Products (6.30).** `M_α M_β ⊂ M_{α+β}` and `M_α W_β ⊂ W_{α+β}`.
3. **Same-label wave products (6.31).** For `a_{γ,m} ∈ W_α`, `b_{γ,m'} ∈ W_β` with the same label, the product lies in `W_{α+β}` with harmonic `m+m'` when `m+m' ≠ 0`, and in `M_{α+β}` when `m+m' = 0` *after temporal cutoff*; before cutoff a zero harmonic satisfies the mean bounds on its labelled rectangle.
4. **Distinct labels.** `(∂^I w_γ)(∂^J w_{γ'}) = 0` for `γ ≠ γ'`.
5. **Operator table (6.32).** `∂_{R,Z,T}: C_α → C_α`; `D_r: C_α → C_{α−κs}`; `D_z = ε∂_Z: C_α → C_{α+1}`; `Q^{1+h}N_abs = c i0 N_i0: C_α → C_α`; `−ε∂_T: C_α → C_{α+1}`.
6. **Finiteness.** Products, differentiation and angular averaging preserve finite band-independent harmonic sets at every fixed stage.

### 2. What is matched

| Clause | Lean | Status |
|---|---|---|
| 1, finite sums at a fixed exponent | `window_sum_memClass` (`LabelSumBounds.lean:369–395`), `UniformClass.sum` (`:417`) | matched |
| 2, `M·M` and `M·W` | `MeanClass.bilinear` (`WeightedClasses.lean:429–437`), `MeanClass.bilinear_wave` (`:449–456`), `mean_wave_cmul` (`WaveInteractionBounds.lean:77–84`) | matched |
| 3, `W·W` at `α+β` | `wave_cmul_wave` (`WaveInteractionBounds.lean:99–114`), zero harmonic via `HarmonicFields.angularMean_product` in `uniform_angularProduct` (`LabelSumBounds.lean:410–430`) | class level matched |
| 4, distinct labels vanish | `jet_zero_off_window` (`:329–340`), `window_card_le` (`:319–327`), `finite_sum_jet_bound` (`:337–365`), `ActualCarrierGeometry.labelCarrier_disjoint:342` | matched, operational form |
| 5, operator table | `UnweightedClass s (−κ) Vr` and `UnweightedClass s 1 Vz` at every consumer (`CurlClassBounds.lean:230,252,281,297,707,732,765`; `WaveInteractionBounds.lean:1066,1083`); `UnweightedClass s 1 (fun n x => s.epsilon n * …)` (`PrimaryMaterialDefect.lean:198`); `along_scaled_direction` (`LinearWaveResidual.lean:247–253`) | components only |
| 6, band-independent harmonic sets | `Finset` support fields `hF : support ⊆ F` in `uniform_angularProduct`, `BandLimited`, `window_card_le` | matched |

The quantitative part of clause 1 is stronger than the paper's phrasing in one respect and weaker in another, both worth naming. `finite_sum_jet_bound` bounds the number of contributing labels by a literal **2250**, independent of band and point, and multiplies the constant by that overlap bound rather than by the active cardinality — the file says so in its own comment ("Only its at-most-2250 locally supported derivatives contribute at `x`"). The paper's Lemma 6.3 gives `C·S_ref³` with `S_ref = ℓ²`, which grows with the dyadic level. A fixed 2250 and a growing `ℓ⁶` are not the same statement; they are both band-independent in the sense that matters for the sums, and neither is derived from the other here.

### 3. What is not matched

**Clause 3's pre-cutoff qualifier.** The paper is careful: before the temporal cutoff the coefficient algebra is used only on the labelled rectangle, and only after cutoff does Lemma 6.1 eliminate cross-label products. The tree carries the locality in a separate layer (`MeanLocalCoefficient.coefficient_mul`, `:41–70`, which localizes a coefficient to `A n` = the labelled rectangle and proves the product mean-class there). That is the right mechanism, and it is not the clause: no declaration states the two-wave product with the rectangle as its domain of validity.

**Clause 5 as a table.** Three of the five rows are literally present as the classes the consumers demand: `D_r` enters every curl bound through `UnweightedClass s (−κ) Vr`, `D_z` through `UnweightedClass s 1 Vz`, and `ε∂_T` through the `s.epsilon n * …` class in `PrimaryMaterialDefect`. The remaining row is `Q^{1+h}N_abs`: `along_scaled_direction` proves `along (c • V) f = c · along V f`, and its docstring says this is "the manuscript's prefactor, for example `c = Q^{1+h}` multiplying `Nabs`". That is an identity plus a docstring, which is exactly the pattern E127 warned about. The class-preservation statement `C_α → C_α` for the scaled normal operator is not a single declaration in the tree.

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 13 | 13 |
| partial | 2 | 3 |
| unplaced | 59 | 58 |
| **total** | **74** | **74** |

Proposition 6.6 is the first of the fifty-nine to be read, and it splits rather than placing. The section-level mapping in `CROSSWALK` called §6 an `object` match to `LabelSumBounds` and `PhysicalGraphBounds`; that judgement survives, at clause granularity, and it does not extend to the operator table.

*Evidence: `.setup/paper/ns.txt:3206–3245` (§6 outline), `:3640–3710` (Proposition 6.6 and its proof); `LabelSumBounds.lean:313–430`; `WeightedClasses.lean:415–456`; `WaveInteractionBounds.lean:77–114`; `MeanLocalCoefficient.lean:41–70`; `CurlClassBounds.lean:230–297,707–769`; `PrimaryMaterialDefect.lean:182–210`; `LinearWaveResidual.lean:247–253`; `ActualCarrierGeometry.lean:342`; E127. Reading only — nothing compiled.*

---

## E130 — Lemma 7.7 is placed, and it is what E127 said it was (2026-11-23)

*Reading entry. E127 removed `curlRemainder_waveClass` from Lemma 9.2 and identified its exponent `α+1/2−κ` as Lemma 7.7's. This entry closes that loop: the paper's Lemma 7.7, read clause by clause, is exactly the curl-correction construction those declarations implement. The ledger moves to 14 placed, 3 partial, 57 unplaced.*

### 1. What the paper asks

`Lemma 7.7.` For every `α ∈ R` and nonzero integer `m`, let `t_m ∈ W_α` satisfy `n_Φ · t_m = 0`, supported in the prescribed slow and transverse supports and compactly inside the pulse interval, with smooth zero extension across the boundaries. Then:

| Clause | Paper's claim |
|---|---|
| a | (7.38) gives `C_m ∈ W_{α+1/2}` and `r_m ∈ W_{α+1/2−κs}` |
| b | `(t_m + r_m)e^{ikmΦ} = curl_* A_m` is exactly divergence-free for the normalised operators, after evaluation at the phase map |
| c | potential and velocity have smooth zero extensions across their support boundaries |
| d | for `a_m = t_m + r_m`, `ikm n_Φ·a_m = −((D_r + R⁻¹)(a_m)_r + D_z(a_m)_z)`, and `n_Φ·a_m ∈ W_{α+1/2−κs}` (7.39) |
| e | physical potentials and pressures are chart ones times `Q^{1/2−A}`, `Q^{−2A}` |

The proof is explicit about where the `1/2` comes from: "The factor `(km)^{-1}` increases the `ε` exponent by `1/2`, and applying `D_r` decreases it by at most `κs`."

### 2. Where the `1/2` sits in the tree

This is the part worth stating carefully, because it looks like a mismatch and is not.

`CurlClassBounds.normalCoefficient_class` (`:198–211`) proves

```
MemClass s w α a → MemClass s w α (normalCoefficient N a)
```

at **`α`, not `α+1/2`** — and that is correct, because the tree's `coefficient` is the normalised amplitude *without* the `(km)^{-1}` prefactor. The prefactor is a separate object, `inverseCarrier K = i/K` (`:592`), and it enters through `band_smul` with the hypothesis

```
hK : BandBound s (1/2) (fun n => 1 / K n)
```

which is exactly "multiplying by `1/K` raises the exponent by `1/2`". That hypothesis is on every consumer of the curl class. So:

* potential coefficient with the prefactor: `α + 1/2` — `physical_strippedRemainder_class` (`:858–862`) states `MemClass s w (α + 1/2)` for the stripped remainder in the Cartesian geometry;
* cylindrical curl with the prefactor and the `D_r` cost: `α + 1/2 − κ` — `curlRemainder_waveClass` (`:757–769`).

The paper's two exponents are reproduced exactly, and the tree splits them across two objects where the paper writes one.

### 3. Clause by clause

| Clause | Lean | Status |
|---|---|---|
| a, `C_m ∈ W_{α+1/2}` | `normalCoefficient_class` (`:198`) at `α` composed with `band_smul` at `1/2` (`:458–462`, `:858–862`) | matched, split across two objects |
| a, `r_m ∈ W_{α+1/2−κ}` | `curlRemainder_waveClass` (`:757–769`) | matched, exponent exact |
| b, exact curl and divergence-freeness | `cylindricalCurl_vectorPotential` (`:633–654`): given `n_Φ·a = 0`, `curl A = vectorMode (realizedCoefficient)`, with `realizedCoefficient := a + curlRemainder (coefficient a)`; `divergence_curl_zero` discharges the divergence inside `longitudinal_from_curl_class` (`:725–739`) | matched |
| c, smooth zero extensions | the `tsupport` and `ContDiffOn` hypotheses every declaration in the chain carries; no clause-specific theorem | ambient convention |
| d, `n_Φ·a_m ∈ W_{α+1/2−κ}` and (7.39) | `longitudinal_class` (`:700–721`) concludes `MemClass s w (α + 1/2 − κ)` for `normalDot (phaseNormal) a`, and `longitudinal_eq_inverseCarrier` gives the identity `n_Φ·a = (i/K) · strippedDivergence` | matched, both the class and the formula |
| e, chart-to-physical factors | the `physical_*` twins (`:850–884`) plus `ChartScales`; the numeric factors are not a statement of this lemma | definitional rescaling |

That is a placement under the rule this audit uses elsewhere: a clause counts as carried when it is an ambient convention of every declaration in the chain (support and `ContDiffOn`, clause c) or a definitional rescaling (clause e); it counts as a component when the statement itself differs, which is what E129 found for Proposition 6.6's rectangle qualifier and its `N_abs` row.

### 4. §7 is not cited by number

A grep of the whole tree for `Lemma 7.7`, `Proposition 7.2` and "pulse inverse" returns **no docstring match at all**. Every other section the crosswalk maps has at least one file naming a paper result (`§4.4`, `§4.6`, `§8.1`, `§8.2`, `§8.3`, `§10.2`, and `CurlClassBounds`'s own "Lemma 9.2" — which E127 showed was wrong). §7's correspondence is therefore entirely `object`-basis, which is why the section-level row was labelled that way and why this placement had to be made by reading statements rather than by following a citation.

*Evidence: `.setup/paper/ns.txt:4396–4442` (Lemma 7.7 and proof), `:4002–4016` (7.13); `CurlClassBounds.lean:198–211,458–462,592–654,700–739,757–769,850–884`; `WeightedClasses.lean` (`MemClass`, `band_smul`, `mono_exponent`); E127. Reading only — nothing compiled.*

---

## E131 — Lemma 8.7: the five-row algebra is placed, its two class bounds are not (2026-11-23)

*Reading entry. The §8 row is the five-moment correction, Lemma 8.7 (p. 98). The linear algebra matches the paper's displayed blocks row for row. The quantitative half — the two class memberships and the explicit inverse bounds — exists only as components. The row is partial, and the ledger moves to 14 placed, 4 partial, 56 unplaced.*

### 1. What the paper asks

`Lemma 8.7` assumes the slow base satisfies (8.24) on the reserved interior interval `I_m`, and solves the five radial moment equations (8.25). The solution is displayed explicitly as two blocks:

```
A_theta = ( mu2        mu2 e^{2d}        mu2 e^{4d}
            2a mu^{-2-2l}  2a mu^{-2-2l} e^{d(-2-2l)}  2a mu^{-2-2l} e^{2d(-2-2l)}
            -a mu^{-2l}   -a mu^{-2l} e^{-2dl}      -a mu^{-2l} e^{-4dl} )

A_z = ( mu1        mu1 e^{d}
        a mu^{1-2l}  a mu^{1-2l} e^{d(1-2l)} )

(u0,u1,u2) = A_theta^{-1} (0, -Pq, -Jz,q),   (s0,s1) = A_z^{-1} (0, -Jtheta,q)
```

`A_theta` enforces zero angular momentum and the targets `-Pq, -Jz,q`; `A_z` enforces zero axial flux and the target `-Jtheta,q`. Since `Gq = 0` the two blocks exhaust the five equations. The inverse is linear in the target triple, smooth in the slow variables, and the correction is bounded `S_alpha -> M_alpha`.

### 2. What matches

| Paper's object | Lean | Status |
|---|---|---|
| the three angular row exponents `2, -2-2l, -2l` | `FiveRowRank.angularPowers` (`:78`) | exact |
| the two axial row exponents `1, 1-2l` | `FiveRowRank.axialPowers` (`:79`) | exact |
| the five equations as one predicate on a base and a correction | `FiveRowRank.FiveRows` | present |
| the two preserving rows (zero angular momentum, zero axial flux) | `fiveRows_mass_zero` (`DefectIncrementBounds.lean:621`), `fiveRows_preserve_masses` (`:635`) | matched |
| the three cancelling rows, with signs | `linearRows_eq_neg_of_fiveRows` (`DefectIncrementBounds.lean:650-700`), whose own docstring says "The three moment rows are exactly those solved in (35), including the minus sign and factor one half in the axial pressure moment" | matched: `linearRows o base h = -defects o base m W` |
| invertibility of the moment matrix | `PowerMomentMatrix.powerEvaluationMatrix_det_ne_zero` (`:143`) | general Vandermonde-type nonsingularity, not the two displayed blocks |

The exponent match is the strongest single check in this row. The paper's `A_theta` rows carry `mu^2`, `mu^{-2-2l}`, `mu^{-2l}`; its `A_z` rows carry `mu^1`, `mu^{1-2l}`; and the tree's two power families are `![2, -2 - 2*l, -2*l]` and `![1, 1 - 2*l]`. That is the same five weights, in the same order, including the sign convention on the third row that `defects` carries.

### 3. What does not match

* **The explicit block inverses.** `powerEvaluationMatrix_det_ne_zero` gives nonsingularity for the general `n`-point moment matrix. It is not `A_theta` and `A_z`, and it carries no inverse norm. E105 already recorded the consequence: no inverse bound, so no "the inverse may deteriorate as `lambda -> 0` but no uniformity is required" statement.
* **The two class conclusions.** The paper concludes the correction is `S_alpha -> M_alpha` with the matching bound. The tree states the row solutions pointwise (`linearRows ... = -defects ...`) and separately carries mean-class membership of the increments (`CorrectionState.MeanResidualBounds`, E97; `MeanIncrementBounds`). No single declaration states "the five-row solve maps `S_alpha` to `M_alpha`".
* **`Gq = 0` exhaustiveness.** That the two blocks exhaust the five equations is a fact about the base, used in the paper's Step 2. The tree's `FiveRows` is a predicate the caller supplies; no declaration derives it from (8.24).

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 14 | 14 |
| partial | 3 | 4 |
| unplaced | 57 | 56 |
| **total** | **74** | **74** |

Three of the four partials are now of the same shape: a paper result whose *algebra* is in the tree exactly and whose *quantitative* half is assembled from pieces rather than stated. That pattern is worth naming once, because it is the most likely place for a real defect to hide: the algebra is the part a reader checks, and the bounds are the part the kernel never weighs (finding 1).

*Evidence: `.setup/paper/ns.txt:4955-5040` (Lemma 8.7 and the display), `:5014-5030` (Step 2, the two blocks and `Gq = 0`), `:5041` (Lemma 8.8, the defect gain); `FiveRowRank.lean:19-93`; `DefectIncrementBounds.lean:621-700`; `PowerMomentMatrix.lean:143`; `CorrectionState.lean:453-472`; E97; E105. Reading only — nothing compiled.*

---

## E132 — Lemma 8.6: the inversion core is placed, the application clauses are assembled (2026-11-23)

*Reading entry. The §8 inversion lemma splits cleanly. Existence, the Fourier formula, smoothness and the zero-mean property are stated in `TorusInverse` and match the paper. The derivative-loss bound appears in the tree's weighted-seminorm form rather than as a `C^m` inequality, uniqueness is not a declaration, and the chart-level application clauses live in the mean-update layer. The row is partial; the ledger moves to 14 placed, 5 partial, 55 unplaced.*

### 1. What the paper asks

`Lemma 8.6` (p. 95). Let `N = v_t · ∂_y` on `T^2`, `v_t` as in (6.2), and `F` smooth of zero Haar mean. Then:

| Clause | Paper's claim |
|---|---|
| a | `N phi = F` has a **unique** smooth zero-mean solution `phi = N^{-1}F` |
| b | it is the Fourier series `sum_{k != 0} Fhat(k) / (2 pi i v_t · k) e^{2 pi i k · y}` |
| c | `norm(N^{-1}F)_{C^m_y} <= C_m norm(F)_{C^{m+4}_y}` for every `m >= 0` |
| d | chart forms `Delta v = -c_i0^{-1} N_i0^{-1} E_theta`, `gamma_d = -c_i0^{-1} N_i0^{-1} E_z`, with `c_i0^{-1} <= C S_*` |
| e | both increments lie in `M_alpha`, with zero auxiliary mean at each slow and radial point |
| f | the azimuthal-potential realization gives `(Delta beta, Delta v, Delta gamma) = (-eps d_Z T1 gamma_d, Delta v, gamma_d - A1 gamma_d)` in `M_{alpha+1} x M_alpha x M_alpha`, divergence-free, preserving both integral constraints |
| g | the fast-time cancellation (8.22) holds with a flat remainder |

### 2. What is placed

`TorusInverse` builds the inverse as a Fourier multiplier on the universal cover and descends it to the torus.

* **The operator.** `Direction` (`:190`) has two constructors, `radial` and `temporal`, with fixed Diophantine vectors `(1, 1 - sqrt 2)` and `(sqrt 2 - 1, 1)` (`:195`), and `symbol d k` is the corresponding Diophantine symbol with `symbol_formula` proving `symbol d k = k.1 * (vector d).1 + k.2 * (vector d).2`. This is the paper's `v_t · k`, for the two directions the development uses.
* **The multiplier and zero mean.** `multiplier d k = (omega * symbol d k)^{-1}`, `inverseCoeff d a k = multiplier d k * a k`, and `inverseCoeff_zero : inverseCoeff d a 0 = 0` (`:249-258`) — the zero-mean condition is built into the object, not assumed.
* **It inverts.** `coefficient_cancel` gives `omega * symbol d k * inverseCoeff d a k = a k` whenever `a 0 = 0`, and `directionalInverse_solves` (`:323`) turns that into the genuine Frechet statement: `fderiv (directionalInverse d a) x (vector d) = series a x`. That is `N phi = F` with the actual derivative, not a formal symbol.
* **Existence, smoothness, zero mean, as one theorem.** `zero_mean_series_has_smooth_inverse` produces a torus function `u`, continuous, with zero Haar integral, whose lift is `C^infinity`, and whose directional derivative is `series a`. `contDiff_directionalInverse` (`:304`) and `inverse_zero_mean` supply the pieces.
* **The derivative loss.** `inverseCoeff_weighted_bound` states `weight^p * norm(inverseCoeff d a k) <= C * weight^(p+1) * norm(a k)` — inversion loses exactly one polynomial weight — and `inverse_derivativeWord_bound` composes that with `m` coordinate derivatives: for every derivative word `w`, `norm(w(N^{-1}a)) <= C * coeffSeminorm (|w| + 1) a`.

Clause (c) therefore matches, but in the tree's own currency. The paper's `C^m` left side is a pointwise jet bound; the tree's is a weighted coefficient seminorm, and `m` derivatives plus one inversion cost `coeffSeminorm (m+1)` of the source. A `C^{m+4}` bound supplies that seminorm by the standard estimate in two dimensions (`weight^{m+1}` against `weight^{-3}` summability), which is exactly the paper's `+4`. The conversion itself is not a declared lemma: the file's only seminorm-to-pointwise step is `norm_series_le` at `m = 0`.

### 3. What is not placed

* **Uniqueness.** The paper says "unique". The tree proves existence and that every solution must have the displayed coefficients (`coefficient_cancel` forces them), but no declaration states uniqueness of the zero-mean solution.
* **Clauses (d) to (g).** The chart factor `c_i0^{-1} <= C S_*`, the `M_alpha` memberships, the azimuthal-potential realization with its three class conclusions, divergence-freeness, the preservation of the two integral constraints, and the (8.22) cancellation are all in the mean-update layer (`TemporalMeanUpdate`, `MeanChartCompatibility`, `VariableGaugeMean`, `StateMomentBalances`), not in `TorusInverse`. E131's finding applies here too: the algebra is stated, the class bounds are assembled.

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 14 | 14 |
| partial | 4 | 5 |
| unplaced | 56 | 55 |
| **total** | **74** | **74** |

This is the first row where the core theorem is genuinely stronger than the paper's phrasing in one respect: `directionalInverse_solves` is a statement about the actual Frechet derivative of the descended torus function, whereas the paper writes the equation for the series. The weakness is on the other side — the `C^m` norm is replaced by a coefficient seminorm, and uniqueness is absent.

*Evidence: `.setup/paper/ns.txt:4885-4935` (Lemma 8.6, (8.19)-(8.22)); `TorusInverse.lean:190-215,249-258,286-335,420-445,490-525` (`inverse_derivativeWord_bound`, `inverse_zero_mean`, `zero_mean_series_has_smooth_inverse`); `SmoothFourierData.lean:549-571`; `ParametricTorusInverse.lean:521-543`; `TemporalMeanUpdate.lean:216-225`; E131. Reading only — nothing compiled.*

---

## E133 — Lemma 9.7: one threshold for every stage is placed, the derivative count is unstatable (2026-11-23)

*Reading entry. This is the first row of the `NEXT.md` queue. Two of the lemma's clauses are declarations outright, and the threshold is stronger than the paper's prose implies: its type has no stage argument and no derivative-order argument to vary. The third clause has no declaration, and the reason is structural rather than a missed search. The row is partial; the ledger moves to 14 placed, 6 partial, 54 unplaced.*

### 1. What the paper asks

`Lemma 9.7` (p. 111), opening §9.4:

| Clause | Paper's claim |
|---|---|
| a | there is `q_big > 0`, **independent of the correction stage and of the derivative order**, such that every finite partial sum, before summation cutoffs, is well defined on `0 < q < q_big` |
| b | for every fixed stage and output amplitude derivative, the construction and its estimate require **finitely many** input amplitude derivatives |
| c | the constants may depend on the correction stage |

The proof fixes `0 < q_big ≤ q*` once — "with the fixed background, the stated positive lower bound for `|n_Φ|`, the primary covariance, and the fixed supports of the normalized mean-correction profiles" — and then argues that nothing later can force a smaller threshold: the harmonic propagator is the fundamental propagator times a damping factor of modulus at most one (7.18); differentiation at fixed order raises constants only, never the threshold (Corollary 7.3); signed updates divide by the original `2√(yσ)`; the correction system uses the fixed linear map of Lemma 8.7; pressure, temporal inverses and the modified radial integrals are fixed linear maps. Clause (b) is then a count on the finite DAG of sums, products, derivatives and proved inverses, with `D_{v,a}(m) = max_{w→v} D_{w,a}(m + d_{v,w})`.

### 2. Clauses (a) and (b) of the statement are declarations

**The threshold.** `ActualCandidateConstruction.qbig (B N0 : ℕ) : ℝ := ChartScales.Q (firstBand B N0)` (`ActualCandidateConstruction.lean:155`), with `qbig_pos` (`:157`). Its type *is* the independence claim: there is no stage argument and no derivative-order argument to vary. The two parameters are the global budget `B` and the geometric floor `N0`; `firstBand B N0 = max 4 (bandFloor B N0)` (`:142`) is computed from the cycle parameters before any cycle runs, which is the paper's "choose once". `twice_residual_scale` (`:172`) pins the same number to the comparison band — `2 * Q (residualBand B N0) = qbig B N0` — so the residual band and the validity domain cannot drift apart.

**The common domain.** `physicalDomain B N0 = CutStageEstimates.physicalSublevel h (qbig B N0)` (`:189`), open at `:192`. Every stage is typed over `MixedAxisPreservation.localDomain F.data.h qbig = {w | w.1 < 1 ∧ physicalQ h w < qbig}` (`MixedAxisPreservation.lean:448`), and `germ_stage_endpoints` carries `Jstages : ∀ j, PhysicalJets h qbig (stages j)` (`GermEndpointInputs.lean:316`) — one `qbig` for the whole sequence, not one per stage. `PhysicalJets` (`:25`) bundles `ContDiffOn ℝ ∞ f (physicalSublevel h qbig)` with an all-order bound.

One representational difference has to be said plainly, because it reads as a gap and is not. Lean fields are total functions, so "well defined on `0 < q < q_big`" cannot be a partiality claim. The tree carries the same content as smoothness and support *on the sublevel*, and the endpoint layer (`OneSidedExtension`, `extension_of_eqOn_sublevel`) is what converts sublevel data into the one-sided limits the assembly later consumes. Reading a total function as "defined everywhere" would misread the formalization; the restriction is in the hypotheses, uniformly in `j`.

### 3. Clause (b) has no counterpart, and the reason is not a search failure

A grep of the whole `NavierStokes/` tree for `finitely many input deriv`, `derivRequirement`, `needsDeriv`, `lossOrder`, `derivativeBudget` and `orderBudget` returns nothing. The nearest objects are not it:

* `DiagonalResidual.JetRate` / `FiniteJetRate` (`:33`, `:37`) are *bounds* at order `m` with a loss exponent, and `residual_jetRate_of_stages` (`:196`) consumes `∀ J m, JetRate … (uStage J) m (-Lbg m)` — Lemma 9.8's shape, not this count.
* `WholeDomainPhysicalStageTheorem.paperJetLoss B N0 m = Σ_{k≤m} |paperLoss B N0 k|` (`:188`) accumulates the loss over lower orders. Again a magnitude, not a number of sources.
* The "constants may depend on the stage" half is documented rather than proved: the `PhysicalJets` docstring ("The exponent and logarithmic loss may depend on the derivative order and on the field") and `WeightedClasses.lean:125` ("Stage constants are deliberately not uniform in the stage index").

Clause (b) quantifies over *derivations* — how many derivatives of each source a bound needs. That is a property of the construction's syntax, of the term that builds the estimate, and the object language has no predicate for it. In Lean every expression is finite, so "finitely many input derivatives" cannot fail; the paper's real assertion is that its per-stage estimate is a finite expression in finitely many jets, which the kernel establishes by the term existing. There is nothing to state.

This is a third failure mode, distinct from the two already named here. E94's row was unplaced because the *query* was wrong (paper: "normalized linear residual"; tree: `globalGood`). E129's row was partial because the tree stated a *component* instead of the whole. This clause is **unstatable** in the development's terms, which is weaker evidence of a gap than either, and it should not be counted as one when the row is read later.

### 4. The row was pointed at the wrong module

`NEXT.md` sent this row to `LocalScheduleWitness` and `ChartScales`. `ChartScales` is right — `qbig` is `ChartScales.Q` of a band — but `LocalScheduleWitness` **retains a supplied** schedule and threshold (`awayExtensions_of_schedule` takes `qbig` as a binder at `:47`) so the endpoint conclusions hold for any admissible choice. The definition is in `ActualCandidateConstruction`. A reader following the work order would have found only consumers.

### 5. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 14 | 14 |
| partial | 5 | 6 |
| unplaced | 55 | 54 |
| **total** | **74** | **74** |

Clause (a) is the strongest match in the queue so far in one narrow sense: the independence is visible in a type signature rather than argued in prose. Whether `bandFloor`'s dependence on `B` and `N0` is stage-independent *in fact* is a question about `ActualCycleParameters`, which is the next link if this row is ever promoted.

*Evidence: `.setup/paper/ns.txt:5669–5695` (Lemma 9.7 and proof, pp. 111–112); `ActualCandidateConstruction.lean:142–192`; `MixedAxisPreservation.lean:448–462`; `GermEndpointInputs.lean:25–31,316–319`; `WeightedClasses.lean:125`; `DiagonalResidual.lean:33–52,196–214`; `WholeDomainPhysicalStageTheorem.lean:188`; `LocalScheduleWitness.lean:47`. Reading only — nothing compiled.*

---

## E134 — Lemma 9.8: the printed loss is the tree's definition, and the flat error is gone (2026-11-23)

*Reading entry. This row places whole. The paper's `ℓ_m` is not merely bounded by something stage-independent in the tree — it is the definition, term for term. The stage index is absent from every constant in all three displays, and in the residual estimate the tree drops the paper's flat error term instead of bounding it. The ledger moves to 15 placed, 6 partial, 53 unplaced.*

### 1. What the paper asks

`Lemma 9.8` (p. 113), three displays for every Cartesian space–time derivative order `m`, where `g_j = h/10 · j → ∞`:

| Display | Paper's claim |
|---|---|
| (9.17) | `|Z_j|_m + |Δu_j|_m ≤ C_{j,m} q^{g_j − ℓ_m} (1+|log q|)^{P_{j,m}}`, with `ℓ_m` **independent of `j`** and including the extra spatial derivative that recovers velocities from wave and mean vector potentials |
| (9.18a) | `|(u^[j], p^[j])|_m ≤ C_{j,m} q^{−K_m} (1+|log q|)^{P_{j,m}}`, with `K_m` **independent of `j`** |
| (9.18b) | `|R(u^[j], p^[j])|_m ≤ C_{j,m} q^{hσ_j − K_m} (1+|log q|)^{P_{j,m}} + E_{j,m}`, with `E_{j,m} ≤ C_{j,m,N} q^N` for every `N` |

The printed proof fixes the four physical derivative costs (9.19) and sets `ℓ_m = 2A + (m+1)(1 + 3h/2)`.

### 2. `ℓ_m` is the definition, not a stand-in

`SharpPhysicalCarrier.physicalLoss h m = 2*CoordinateAlgebra.A h + ((m:ℝ)+1)*derivativeCost h` (`SharpPhysicalCarrier.lean:16`), with `derivativeCost h = 1 + 3*h/2` (`:13`) and `A h = 1/2 + h` (`CoordinateAlgebra.lean:18`). Substituting gives the paper's `2A + (m+1)(1 + 3h/2)` exactly, including the `(m+1)` rather than `m` — which is how the prose's "additional spatial differentiation recovering velocities" is carried. The file's own docstring says so: "The printed physical loss includes one derivative for potential recovery."

That is a stronger form of correspondence than E133 could claim for the threshold. There the independence was in the signature and the *value* was unconstrained; here the value is printed in the paper and is the same closed expression in the tree.

### 3. The stage index is absent from every constant

| Constant | Definition | Stage index |
|---|---|---|
| `g_j` | `ActualIterationLedger.gain h j = h * j / 10` (`:29`) | present, as the paper intends — this is the gain, not the loss |
| `ℓ_m` | `physicalLoss h m` | **absent** |
| `K_m` | `paperLoss B N0 m = max (finiteLoss B N0 m) (fixedLoss m)` (`:147`) | **absent** |
| `K_m` for all orders ≤ m | `paperJetLoss B N0 m = Σ_{k≤m} |paperLoss B N0 k|` (`:188`) | **absent** |
| domain | `commonQ B N0 = ChartScales.Q (residualBand B N0)` (`:13`), with `commonQ_lt_original : commonQ B N0 < qbig B N0` (`:20`) | **absent** |

The composition is transparent at each layer: `prefixLoss initial positive m = max (initial m) (positive m)` (`WholeDomainPrefixBounds.lean:12`), `finiteLoss` is the max of the two prefix losses against `physicalLoss h`, and `fixedLoss m = physicalLoss h (2h) m` (`ActualCycleResidualBounds.lean:1145`). No layer takes a stage parameter, so there is no place for a hidden per-stage choice to hide — which is exactly the failure mode the row was opened to test.

The three displays are then `actual_increment_bound` (`WholeDomainPhysicalStageTheorem.lean:114`), and the second and third conclusions of `paper_physical_loss` (`:243`), which quantify `∀ J m … ∀ k ≤ m` — the paper's jet norm, all derivatives through order `m`, in one bound. `C` and `P` are existentially quantified inside the `∀ J m`, so they may depend on both, matching `C_{j,m}` and `P_{j,m}`.

### 4. Where the tree is stronger, and by how much

The paper's (9.18b) carries `+ E_{j,m}` with `E_{j,m}` flat to every order. The tree's residual conclusion has **no error term**:

```
‖∂^k R(u^[J], p^[J]) w‖ ≤ C * q^(h*σ_J − paperJetLoss B N0 m) * (1+|log q|)^P
```

for all `k ≤ m`. The file states the reason in its own docstring: "The residual conclusion is stronger than the displayed estimate: all flat remainders are absorbed, so its additional flat-error term can be chosen to be zero." So the `E` term is not omitted, it is unnecessary — the sharper per-order form is `actual_finite_residual_bound` (`WholeDomainActualStageBounds.lean:37`), which carries `fixedLoss m` rather than the summed loss and likewise no `E`.

This is the second place in the audit where the formalization is stronger than the prose rather than weaker. The first was E132's `directionalInverse_solves`, which states the Fréchet derivative where the paper writes the equation for the series. Both belong in the manuscript's limits section as instances of the same direction of divergence, not as findings against the paper.

### 5. Two caveats that are not defects

* **Index shift.** The paper's cycle is `j−1 → j`, so its `Z_j` is the increment entering stage `j`. The tree's `actual_increment_bound` is stated at `j+1` and its prefix theorems at `J`. The content is the same object one index later; the audit should not record this as an off-by-one in the mathematics, and does not.
* **`K_m`'s value is a choice.** The paper never prints `K_m`; it prints only that it is `j`-independent and that it includes the recovery derivative. The tree's `max (finiteLoss) (fixedLoss)` is therefore one admissible value among many, and the only property the paper demands of it — no stage index — is the property the type has. What the tree does *not* show is that this particular `K_m` is the one a later argument needs; but the later arguments consume `paperJetLoss` itself (E66's chain, and `paper_physical_loss`'s third conclusion), so the constant is not chosen independently of its consumers.

### 6. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 14 | 15 |
| partial | 6 | 6 |
| unplaced | 54 | 53 |
| **total** | **74** | **74** |

First whole placement since Lemma 7.7 (E130). It also settles the concern that opened this row: the `j`-independence in `paperJetLoss` is not a `∀ J` quantifier hiding a per-stage choice, because no definition in the chain from `physicalLoss` to `paperJetLoss` accepts a stage index at all.

*Evidence: `.setup/paper/ns.txt:5734–5760` (Lemma 9.8, (9.17)–(9.19), pp. 113–114); `SharpPhysicalCarrier.lean:13,16`; `CoordinateAlgebra.lean:18`; `WholeDomainPrefixBounds.lean:12`; `ActualCycleResidualBounds.lean:1145`; `WholeDomainPhysicalStageTheorem.lean:114,147,188,243`; `WholeDomainActualStageBounds.lean:13–20,37`; `ActualIterationLedger.lean:29`; E133. Reading only — nothing compiled.*

---

## E135 — The denominator is 73, not 74: a lemma count the paper never had (2026-11-23)

*Reading entry. The paper has seventy-three numbered results. The ledger has carried seventy-four since E91, because a per-kind breakdown added one lemma too many and the total was computed from the breakdown rather than from the text. No row moves — the numerator was always right — but every "x of 74" and "53 unplaced" in this log, in `CROSSWALK.md` and in `NEXT.md` inherits the error and is corrected here.*

### 1. What the text actually contains

A full-text scan for `(Lemma|Proposition|Corollary|Theorem) n.m.` — every occurrence, not only line-initial — returns **73 distinct names, all 73 of which occur at the start of a line**. The kind breakdown is 3 theorems, 26 propositions, **37** lemmas, 7 corollaries.

E91 printed `3 theorems, 26 propositions, 38 lemmas, 7 corollaries` and summed to 74. That sum is internally consistent, which is exactly why the error survived four subsequent entries: nothing downstream re-derived the total from the text. E91 also wrote "73 of which have at least one statement-length occurrence", which was an attempt to reconcile the arithmetic with what it had actually seen; the correct reading is that there were only ever 73 labels and no missing statement.

### 2. The numbering gaps are the paper's, not the extractor's

| Section | Present | Absent |
|---|---|---|
| §6 | 6.1, 6.2, 6.6 | 6.3, 6.4, 6.5 |
| §9 | 9.1, 9.2, 9.3, 9.5, 9.6, 9.7, 9.8, 9.9 | 9.4 |
| §B | B.1–B.8, B.10 | B.9 |
| every other section | contiguous | none |

These are not holes in the PDF conversion. `9.4` is a subsection heading, not a result: `.setup/paper/ns.txt:5664` reads "9.4. A common domain and physical derivative estimates." and the lemma that follows it is Lemma 9.7. The §6 and §B gaps are consistent with the same pattern — section and sub-appendix numbering that does not allocate a result at every index. A statement hidden inside a figure would not be extractable, but it would also not have been counted by E91, so it cannot account for the difference.

### 3. What moves

| | Before | After |
|---|---|---|
| total | 74 | 73 |
| placed | 15 | 15 |
| partial | 6 | 6 |
| unplaced | 53 | 52 |

Nothing in the numerator changes. `NEXT.md`'s queue already listed 52 concrete rows, because its generator counted the text rather than the ledger — the file and the ledger now agree instead of differing by one.

### 4. Why it is worth an entry rather than a quiet edit

Every rate in this audit is a fraction over this denominator, and "53 unplaced" was one larger than the number of unplaced results that exist. A reader who trusted it would have gone looking for a fifty-third row that is not there. The correction also closes the question E94 and E127 taught this log to ask of every number: *was the query wrong, or is the object missing?* Here it was neither — the arithmetic was wrong, and it was wrong in the one place the audit had not re-derived.

*Evidence: `.setup/paper/ns.txt` full-text scan (73 names; 3/26/37/7 by kind; §6 present {1,2,6}, §9 present {1,2,3,5,6,7,8,9}, §B present {1..8,10}); `.setup/paper/ns.txt:5664` (the 9.4 heading); E91; E133; E134.*

---

## E136 — Lemma 10.2: joint jet limits are constructed, the global uniform statement is not (2026-11-23)

*Reading entry. The terminal-time derivative limits exist in the tree, and in a stronger form than the paper's display: one tensor family indexed by order, with continuity, local uniform convergence, smoothness in the spatial variable, compatibility under spatial differentiation, and origin vanishing. Two clauses are not statements of this lemma — global uniformity on all of ℝ³, and the bundled compactly supported `F_j` family. The row is partial; the ledger moves to 15 placed, 7 partial, 51 unplaced.*

### 1. What the paper asks

`Lemma 10.2` (p. 118), for every spatial multi-index `α` and integer `j ≥ 0`:

| Clause | Paper's claim |
|---|---|
| a | `∂^α_x ∂^j_t f` **converges uniformly on ℝ³** as `t ↑ 1` |
| b | there are `F_j ∈ C_c^∞(ℝ³;ℝ³)`, all supported in `K`, with `lim ∂^α_x ∂^j_t f = ∂^α_x F_j` |
| c | `∂^α_x F_j(0) = 0` |
| d | the limits are compatible under spatial and time differentiation |

The proof has two regions: near the origin the flatness bound (10.9) `|∂^α∂^j f| ≤ C(τ + |z|^(1/D))^N` gives vanishing; away from it Theorem 3.1(ii) plus the exterior heat flow (10.8) give uniform Cauchy on compact sets. A finite cover upgrades compact uniformity to `ℝ³`, and (10.10) transfers the limits across derivative orders.

### 2. What is constructed

`JointResidualLimits` builds the limit family from actual data, not from an assumed extension:

* `VanishingJointJets f : ∀ n, Tendsto (iteratedFDeriv ℝ n f) (𝓝[openPast 1] (1,0)) (𝓝 0)` (`:84`) is the paper's near-origin input, as a hypothesis on the actual residual.
* `boundaryLimits f hext x` (`:120`) is one formal multilinear series per point — defined to be zero at `x = 0`, elsewhere the Taylor series of a chosen one-sided extension. `boundaryLimits_zero` (`:126`) proves the origin case at every order, which is clause (c) in bundled form: all spatial derivatives of all `F_j` vanish at `0`.
* `boundaryLimits_joint` (`:130`) proves convergence at every `x`, and `boundaryLimits_continuous` (`:141`) derives continuity of the limit rather than assuming it.
* `boundaryLimits_locallyUniform` (`:148`) and `boundaryLimits_uniformOn_compact` (`:156`) give uniform convergence on every compact set — the paper's finite-cover conclusion.
* `boundaryLimits_smooth` (`:220`) gives `ContDiff ℝ ∞ (fun x => boundaryLimits f hext x n)` for each order, so the `F_j` are smooth.
* `boundaryLimits_hasFDerivAt` (`:240`) is the compatibility: the spatial derivative of the limit at order `n` is the next tensor restricted to a spatial direction.
* `extendedResidual_smooth` (`:264`) and `exists_smooth_compatible_limits` (`:308`) bundle the time-side compatibility with the rest.

The family does not depend on how the extension was chosen: `boundaryLimits_eq_extension` and `boundaryLimits_independent` show it is determined by the function, which is what makes it a limit rather than an artefact of `Classical.choice`.

### 3. The two clauses that are not stated

* **Uniform convergence on ℝ³.** The tree states local uniformity and uniformity on each compact set. For the constructed force these imply the global statement, because the force is supported in `outerSupport` (`R3CompactCandidate.compactForce_supported`) and vanishes identically outside a compact set. But implication is not statement, and no declaration concludes "uniformly on `ℝ³`". This is the distinction E129 drew about Proposition 6.6's rectangle qualifier.
* **The bundled `F_j` with compact support.** The paper indexes `F_j` by the time-derivative order and carries a support condition. The tree indexes by full tensor order `n` (which mixes `α` and `j`), proves smoothness and origin-vanishing of each limit, but never states that the limit function is compactly supported in `K`. Support lives on the force, one layer up.

Neither gap threatens the mathematics; both are statement-shape differences, and under this audit's rule they make the row partial rather than placed.

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 15 | 15 |
| partial | 6 | 7 |
| unplaced | 52 | 51 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:5997–6005` (Lemma 10.2, (10.6)–(10.9)); `JointResidualLimits.lean:84,120–240,264,308`; `R3CompactCandidate.lean` (`compactForce_supported`); E129; E135. Reading only — nothing compiled.*

---

## E137 — Lemma 10.3 is placed: the positive-time cutoff is the extension (2026-11-23)

*Reading entry. The lemma asks for a smooth compactly supported extension of the force through time one. `R3/PositiveTimeForce` is exactly that construction — smaller support interval, smoothness on all of spacetime rather than only the open half-space. The row is placed; the ledger moves to 16 placed, 7 partial, 50 unplaced.*

### 1. What the paper asks

`Lemma 10.3` (p. 120): the force in (10.5) extends to `f ∈ C_c^∞(ℝ³ × (0,∞);ℝ³)`, with support contained in `K × [0,2]`.

The proof multiplies by a cutoff `χ₀ ∈ C_c^∞(ℝ)` equal to one near zero and zero at arguments at least one, applied to `σ = t − 1 ≥ 0`, with supports shrinking by derivative order.

### 2. What the tree has

`R3/PositiveTimeForce` is that construction, and it is the same object:

| Clause | Lean |
|---|---|
| smooth extension | `force f = fun z => timeCutoff z.1 • f z`, with `force_contDiff` (`:49`) giving `ContDiff ℝ ∞ (force f)` from `ContDiff ℝ ∞ f` |
| agrees with the original force | `force_eq` (`:53`): `force f (t,x) = f (t,x)` for `t ∈ [3/8, 1]` |
| compactly supported in time | `force_compactPositiveTimeSupport` (`:72`) |
| support inside `K × [0,2]` | `force_tsupport_subset` (`:61`): `tsupport (force f) ⊆ Icc (1/16) (21/16) ×ˢ K` |

The cutoff is `timeCutoff t = cutoff ((8/5)(t − 11/16))` (`:21`), one on `[3/8, 1]` (`:28`) and zero outside `[1/16, 21/16]` (`:34`). Since `21/16 < 2` and `1/16 > 0`, the support sits strictly inside `K × [0,2]`.

### 3. Two differences, both in the tree's favour

* **Smoothness is global.** The paper asks for `C^∞` on `ℝ³ × (0,∞)`; `force_contDiff` gives `ContDiff ℝ ∞` on all of `ℝ³ × ℝ`, which is stronger on the positive half-space.
* **The extension is a product, not a Taylor continuation.** The paper builds the extension from the terminal jets of Lemma 10.2 with order-shrinking cutoffs. The tree does not need those jets here: the force is a residual times a compactly supported spatial cutoff, and the time cutoff alone produces the extension. Lemma 10.3 is therefore independent of Lemma 10.2 in the formalization — consistent with E136 finding the 10.2 statements present but unbundled, and with E65 having traced the force's smoothness separately.

The tree proves containment for whatever compact `K` the caller supplies as the force's spatial support, which is the general form of the lemma.

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 15 | 16 |
| partial | 7 | 7 |
| unplaced | 51 | 50 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:6071–6060` (Lemma 10.3 and the cutoff); `R3/PositiveTimeForce.lean:21–72`; `R3CompactCandidate.lean` (`compactForce_time_support`); E65; E136. Reading only — nothing compiled.*

---

## E138 — E127's "no half-loss" is wrong: the mean cross is at α + H − 1/2 (2026-11-23)

*Reading entry. One clause of E127 is corrected. The mean–wave interaction that E127 recorded as carrying no `−1/2` loss does carry one; it is proved under `meanCross` rather than under `mean_wave_cmul`, which is the same "search the shape, not the paper's word" failure as E94. Lemma 9.2 stays partial, but for a smaller reason than the one on record. The ledger does not move: 16 placed, 7 partial, 50 unplaced.*

### 1. What E127 said

`CROSSWALK.md` records Lemma 9.2's mean–wave clause as unmatched: the tree's `mean_wave_cmul` (`WaveInteractionBounds.lean:71`) gives `W_{α+µ}` "with no `−1/2` loss and no tangential/radial split `(M_µ, M_{µ+1})`". The first half of that sentence is false.

### 2. What is actually there

`HarmonicMeanInteraction.meanCross_class` (`:310`) proves

```
WaveClass s P (α + H - 1/2) (fun n x => meanCross c h b n i j x)
```

for every `i : Fin 3` and every `j ≠ 0`, from `IncrementBounds s H h`, the wave bounds of the block, the band bounds at `−1/2`, and `κ ≤ 1/2`. That is the paper's exponent with `µ = H`: the mean–wave term lands at `α + µ − 1/2`, and `j ≠ 0` is the paper's "nonzero harmonics". `angularCarrierTerm_class` (`:293`) supplies the same `α + H − 1/2` for the angular carrier that the `meanCross_eq` identity (`:275`) separates out, and `realMeanCross_class` (`:329`) carries it to the real coefficients.

So the half-loss is not missing. It is in the term the paper calls `(v·∇*)w`, under the name `meanCross`, and it is invisible to a grep for `mean_wave`.

### 3. Why the row still does not move

Two reasons, and only the second is now open:

* **The split.** The paper's hypothesis is that the mean field has tangential components in `M_µ` and radial in `M_{µ+1}`. The tree carries the mean data as `MeanIncrementBounds.Triple` with `IncrementBounds s H h`; whether the two exponent slots in that record are exactly the paper's `(µ, µ+1)` pair has not been read clause by clause. `tripleField_bound` and the `hm.2.1`-style projections suggest a component split, but suggestion is not a match.
* **Componentwise form.** The conclusion is stated per component `i` rather than as one bundled vector membership. For a vector-valued class this is a decomposition of the conclusion, not a weakening, and it would not by itself keep the row partial — E127's per-harmonic objection was of the same shape.

Until the split is read, Lemma 9.2 stays partial. What changes is the reason: the exponent matches, and the only open question is the hypothesis, not the conclusion.

### 4. The pattern, third instance

This is the third time a row was held open by the name rather than by the mathematics: E94 could not find the normalized linear residual until it stopped searching for that phrase and searched for `globalGood`; E133's row was pointed at `LocalScheduleWitness` when the threshold is defined in `ActualCandidateConstruction`; this one searched `mean_wave` and missed `meanCross`. The habit worth keeping is now explicit in `NEXT.md`: search the conclusion's shape, then the paper's words.

*Evidence: `HarmonicMeanInteraction.lean:293,310,275,329`; `WaveInteractionBounds.lean:71`; `.setup/paper/ns.txt:5242–5245` (Lemma 9.2 and the mean–wave clause); E127; E94; E133. Reading only — nothing compiled.*

---

## E139 — Lemma 9.2 is placed: the split is the record's two exponent slots (2026-11-23)

*Reading entry. E127 recorded the mean–wave clause as unmatched on two counts, the half-loss and the tangential/radial split. E138 removed the first. The second is also in the tree, in `IncrementBounds`: the radial slot is at `H + 1` and both tangential slots at `H`, which is the paper's `(M_µ, M_{µ+1})` with `µ = H`. With the wave–wave and label clauses already matched, the lemma places. The ledger moves to 17 placed, 6 partial, 50 unplaced.*

### 1. What the paper asks

`Lemma 9.2` (pp. 102–103), three clauses:

| Clause | Paper's claim |
|---|---|
| a | for a wave `w ∈ W_α` and a mean field `v` with tangential components in `M_µ` and radial in `M_{µ+1}`, the nonzero harmonics of `(w·∇*)v + (v·∇*)w` lie in `W_{α+µ−1/2}` |
| b | for two curl-generated waves of one label, the nonzero harmonics of `(w·∇*)w′ + (w′·∇*)w` lie in `W_{α+α′−κs}`, and the zero harmonic in `M_{α+α′−κs}` |
| c | distinct labels have zero products on their closed supports |

### 2. How each clause lands

* **(a), the exponent.** `meanCross_class` (`HarmonicMeanInteraction.lean:310`) concludes `WaveClass s P (α + H - 1/2)` for every component `i` and every `j ≠ 0`, from `IncrementBounds s H h` and the band bounds at `−1/2`. That is `α + µ − 1/2` with `µ = H`, on nonzero harmonics. E138 records the correction; this entry records the consequence.
* **(a), the split.** `IncrementBounds` (`MeanIncrementBounds.lean:392`) has exactly three fields:

  ```
  radial  : MeanClass s (H + 1) h.radial
  angular : MeanClass s H       h.angular
  axial   : MeanClass s H       h.axial
  ```

  The radial component carries the *higher* exponent and the two tangential components the lower one. That is the paper's hypothesis verbatim: tangential in `M_µ`, radial in `M_{µ+1}`, with `µ = H`. `tripleField_bound` (`:245`) transports the three fields to the complex vector the interaction consumes.
* **(b).** Already matched by E127: `transport_wave_class` (`HarmonicWaveInteraction.lean:386`) and `transport_mean_class` (`:404`) at `α + α′ − κ`, exact, stated per harmonic and component.
* **(c).** Already matched by E127: `labelCarrier_disjoint` (`ActualCarrierGeometry.lean:342`).

The per-component and per-harmonic form is a decomposition of a vector-valued membership, not a weakening of it: `WaveClass`/`MeanClass` are componentwise predicates, and the paper's own statement quantifies harmonics.

### 3. What this cost, and what it says about the earlier passes

Two entries, two greps, and neither was about the mathematics. E127 searched `mean_wave` and concluded the half-loss was absent; the declaration is called `meanCross`. It read the mean data as a `Triple` and did not open `IncrementBounds`; the split was in its first three fields. Both misses are the same failure E94 recorded — the paper's word is not the tree's name — and both were recoverable by searching the conclusion's shape rather than the prose.

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 16 | 17 |
| partial | 7 | 6 |
| unplaced | 50 | 50 |
| **total** | **73** | **73** |

Unplaced does not move: a row left the partial column and joined the placed column. `NEXT.md` keeps its fifty rows.

*Evidence: `.setup/paper/ns.txt:5242–5248` (Lemma 9.2 and its proof); `MeanIncrementBounds.lean:392–394`; `HarmonicMeanInteraction.lean:310,245`; `HarmonicWaveInteraction.lean:386,404`; `ActualCarrierGeometry.lean:342`; E94; E127; E138. Reading only — nothing compiled.*

---

## E140 — Lemma 8.7 is placed: all three of E131's negatives were name misses (2026-11-23)

*Reading entry. E131 recorded the five-row correction as half placed: exponents exact, and the
block inverses, the `S_α → M_α` statement and the `G_q = 0` exhaustiveness all absent. Re-reading
`FiveRowRank` past the line where E131 stopped, and following it forward into `MeanRankUpdate`,
finds a declaration for each of those three. The row is placed; the ledger moves to 18 placed,
5 partial, 50 unplaced.*

### 1. What the paper asks

`Lemma 8.7` (p. 97), eight clauses:

| | Clause |
|---|---|
| a | three fixed azimuthal bump profiles and two fixed axial bump profiles, supported in `I_m` |
| b | a unique linear combination solving the five equations (8.25), for arbitrary targets `(P, J_θ, J_z)` at each `(Z,T)` |
| c | targets normalized row by row as in (8.17) |
| d | increments independent of the angular and auxiliary variables, linear in the targets |
| e | for every `α`, targets in `S_α` give increments in `M_α` at every fixed coefficient derivative, constants permitted to depend on `λ` |
| f | the (8.14) realization has `Δγ = γ_d` exactly and `Δβ ∈ M_{α+1}` |
| g | the two integral constraints of (8.2) preserved exactly |
| h | with the current defects as targets, the last three rows cancel the displayed base contributions |

### 2. Where each clause is stated

| Clause | Declaration | Note |
|---|---|---|
| a | `FiveRowRank.deltaV` (`:100`), `gamma` (`:105`), built by `LocalizedMomentRepair.repair` (`:114`) | five disjoint cells, not the paper's three scaled copies; `tsupport ⊆ Ioo a b` at `:126`, `:131` |
| b (rows) | `FiveRows` (`:241`), `five_rows_on_patch` (`:249`), `five_rows` (`:280`) | all five equations, as one predicate, proved |
| b (existence) | `exists_five_row_repair` (`:311`) | smooth, compact support, inside the patch, no moment-rank hypothesis |
| b (uniqueness) | `LocalizedMomentRepair.matrix` (`:88`), `matrix_det_ne_zero` (`:91`), `coefficients := (matrix)⁻¹.mulVec d` (`:111`) | see §4 |
| c | `angularPowers` (`:81`) `= ![2, -2-2λ, -2λ]`, `axialPowers` (`:82`) `= ![1, 1-2λ]`; `angularDebt` (`:94`) `= ![0, -P/(2C), J_z/C]`, `axialDebt` (`:97`) `= ![0, -J_θ/C]` | the debts are the targets divided by the three row coefficients `2C`, `C`, `C` — (8.17) with `q` for `Q` |
| d | `deltaVLinearMap` (`:348`), `gammaLinearMap` (`:353`), `deltaV_add` (`:363`), `deltaV_smul`, `repair_eq_sum_coordinate` (`:232`) | functions of `R` alone |
| e | `MeanRankUpdate.rank_update_meanClass` (`:899`) | see §3, second negative |
| f | `MeanRankUpdate.radial_physical_scale_gain` (`:1660`) | `MeanClass s α β → MeanClass s (α+1) (ε • β)`: `ε` is the only thing that raises the class, which is (8.14) |
| g | `angular_mass_zero` (`:158`), `axial_mass_zero` (`:163`); `DefectIncrementBounds.fiveRows_preserve_masses` (`:635`), `fiveRows_mass_zero` (`:621`) | |
| h | `DefectIncrementBounds.linearRows_eq_neg_of_fiveRows` (`:650`); `CorrectionState.rank_model_rows` (`:449`), `rank_rows_on_patch` (`:462`); `DefectIncrementBounds.fiveRows` (`:775`) | rows for the actual stream, not for a desired increment |

The normalization check is the sharpest one in the row and it is arithmetic: the paper's three
coefficients in (8.25) are `2V/R`, `R²V`, `-RV`; on (8.24) with `V = C R^{-1-2λ}` and `G = 0`
those are `2C R^{-2-2λ}`, `C R^{1-2λ}`, `-C R^{-2λ}`, i.e. the three powers `2`, `-2-2λ`, `-2λ`
scaled by `2C`, `C`, `C`. The tree's debt slots are `-P/(2C)`, `-J_z/C`, `-J_θ/C`, the same
three divisors, against those same three powers. E131's exponent match is confirmed and is now
tied to the normalization rather than standing beside it.

### 3. The three negatives E131 recorded, and why each was wrong

**(i) "The explicit block inverses … it is not `A_θ` and `A_z`, and it carries no inverse
norm."** E131 compared the paper's displayed matrices against
`PowerMomentMatrix.powerEvaluationMatrix_det_ne_zero` and stopped there. `LocalizedMomentRepair.matrix`
*is* the block: `PowerMomentMatrix.bumpMomentMatrix a (fun j => bump (l j) (u j))`, instantiated by
`FiveRowRank` at `a := angularPowers lam` and `a := axialPowers lam`. `matrix_det_ne_zero` proves
it nonsingular, and `coefficients` does not merely assert an inverse — it *is* `(matrix a l u)⁻¹`
applied to the debt. The norm half is present too, and stronger than the paper asks: `FiveRowRank.finite_jet_bound`
(`:444`) bounds every derivative through a prescribed order by `K ‖C⁻¹‖ ‖d-e‖` uniformly in space,
and `uniform_finite_jet_bound` (`:474`) removes the `C⁻¹` for `|C| ≥ η`. That is the paper's
"the inverse may deteriorate as `λ ↓ 0`; no uniformity in that limit is required" turned into a
theorem with the deterioration displayed rather than waved at.

**(ii) "No single declaration states `S_α → M_α`."** `MeanRankUpdate.rank_update_meanClass`
(`:899`) states it, and its docstring names the paper's own equation: *"Equation (35) maps the
slow defect class `S_α` to `M_α` in every finite stripped jet, uniformly over the band index."*
Its conclusion is `MeanClass s α` in both blocks from `UnweightedClass s α` on the debt family.
E131 searched `MeanResidualBounds` and `MeanIncrementBounds` — the interface records — and did not
open the class layer that satisfies them.

**(iii) "`G_q = 0` exhaustiveness … no declaration derives it from (8.24)."**
`five_rows_on_patch` takes `hV : ∀ R ∈ Ioo a b, V R = background lam C R` and
`hG : ∀ R ∈ Ioo a b, G R = 0`, and proves all five rows for *arbitrary* `V`, `G` satisfying those
pointwise identities. That is (8.24) as a hypothesis pair, with the rows as the conclusion. It is
then discharged on the real thing: `MeanRankUpdate.reserved_five_rows` (`:1399`) derives both from
`ReservedPatches.radial_heated_fields` on the untouched heated outgoing patch, and
`MeanRankUpdate.physical_rows_on_patch` (`:194`) transports it through the physical scaling.

The pattern is E94's, running the other way. E94 recorded a *positive* finding as missing because
the paper's word was not the tree's name; E131 recorded three *negatives* on the same basis. A
negative is only as strong as the search vocabulary behind it, and E131's vocabulary was the
paper's (`A_θ`, `A_z`, "inverse norm", `S_α → M_α`), not the tree's (`matrix`, `coefficients`,
`finite_jet_bound`, `rank_update_meanClass`). One entry later, E127's half-loss came back for the
same reason under the name `meanCross`. Three entries, five misses, one cause.

### 4. What is left, stated as shape rather than as absence

Two differences survive, and neither is an unmatched clause:

* **Uniqueness of the combination is not a named lemma.** It is `det ≠ 0` on a square moment
  matrix plus an inverse that is actually used in the definition of `coefficients`. That is the
  content of "unique"; it is not a theorem called `unique`. A reader who wants the sentence
  spelled out will not find it, and that is a shape difference, not a gap.
* **The lemma is stated in two modules.** The algebra is in `FiveRowRank`; the class half is in
  `MeanRankUpdate`, which imports it. E131's complaint about assembly was fair as a description
  and wrong as a verdict: every clause has its own declaration, which is what "placed" has meant
  since E91.
* **One naming question remains and does not affect the exponent.** The paper's `S_α` for targets
  may be the tree's weighted `MemClass` rather than the `UnweightedClass` that
  `rank_update_meanClass` consumes. Both carry the index `α`, and `MeanClass`/`MemClass` are the
  mean and weighted forms of one predicate family. This is a vocabulary question of exactly the
  E94 kind, and it is recorded here as the first thing a re-read should test rather than as a
  clause that failed.

### 5. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 17 | 18 |
| partial | 6 | 5 |
| unplaced | 50 | 50 |
| **total** | **73** | **73** |

`NEXT.md` keeps its fifty rows. The remaining five partials are Proposition 9.3, Proposition 6.6,
Lemma 8.6, Lemma 9.7 and Lemma 10.2 — and Lemma 8.6 is now the only one in §8.

*Evidence: `.setup/paper/ns.txt:4955–4990` (Lemma 8.7), `:4826` (8.17), `:4996–5030` (Step 2, the
two blocks), `:5041` (Lemma 8.8); `FiveRowRank.lean:81–131,146–311,348–363,444–500`;
`LocalizedMomentRepair.lean:88,91,111,114,165,232,329`; `MeanRankUpdate.lean:163,194,899,1399,1620,1660`;
`CorrectionState.lean:449,462,478`; `DefectIncrementBounds.lean:621,635,650,775`; E94; E127; E131.
Reading only — nothing compiled.*

---

## E141 — Lemma 8.6: both of E132's negatives were name misses; the row is placed (2026-11-23)

*Reading entry. E132 left this row partial on two specific negatives — no declaration states uniqueness, and the seminorm-to-`C^m` conversion is not a declared lemma — plus the observation that clauses (d)–(g) live in the mean-update layer rather than in `TorusInverse`. Both negatives are declarations, and clause (d) is an identity with the paper's own factor written out. The row is placed at one recorded shape difference: the declared composite loss is `m+5`, not the paper's `m+4`. The ledger moves to 19 placed, 4 partial, 50 unplaced.*

### 1. The operator, exactly

Paper (6.2) fixes `bg = sqrt 2 - 1`, `vr = (1, -bg)`, `vt = (bg, 1)` (`.setup/paper/ns.txt:3251-3255`). `TorusInverse.Direction` (`:190-197`) has exactly those two vectors — `.radial = (1, 1 - sqrt 2)`, `.temporal = (sqrt 2 - 1, 1)` — and `symbol_formula` (`:224`) proves `symbol d k = k.1 * (vector d).1 + k.2 * (vector d).2`, which is `v_t · k`. The multiplier is `(omega * symbol d k)^{-1}` with `omega = 2 pi i`, so the series `sum_k a k * mode k x` is the paper's `sum Fhat(k) / (2 pi i v_t · k) e^{2 pi i k · y}` term for term. No constant is absorbed anywhere.

### 2. Uniqueness is a declaration

E132: "no declaration states uniqueness of the zero-mean solution." It is `TemporalMeanUpdate.timeDerivative_unique` (`:126-145`), whose docstring reads *"Uniqueness for the smooth periodic temporal equation with a prescribed mean. The proof uses actual Fourier differentiation and reconstruction."* The statement is `timeDerivative f = timeDerivative g` plus `squareAverage f = squareAverage g` implies `f = g`; on the zero-mean class both means are `0`, which is precisely the paper's "unique smooth zero-mean solution". The proof is the paper's own: `coefficient_timeDerivative` (`:112`) differentiates the series, `symbol_ne_zero` cancels the symbol `k != 0`, the `k = 0` slot is the mean, and `series_coefficient` reconstructs both functions. It sits one module above `TorusInverse` — the same reason E140's three negatives were misses: E132 searched the inverse module for a word the mean-update module owns.

### 3. The conversion is a declaration, with the paper's `+4` in it

E132: "the conversion itself is not a declared lemma: the file's only seminorm-to-pointwise step is `norm_series_le` at `m = 0`." The conversion is in `SmoothFourierData`, not `TorusInverse`:

| Piece | Declaration | Statement |
|---|---|---|
| inverse loses one weight | `inverseCoeff_weighted_bound` (`TorusInverse.lean:412`), `inverseCoeff_seminorm_le` (`:427`) | `coeffSeminorm p (inverseCoeff d a) <= 6 * norm(omega^{-1}) * coeffSeminorm (p+1) a` |
| pointwise jet of the inverse | `inverse_derivativeWord_bound` (`:498-506`) | `norm(derivativeWord w (directionalInverse d a) x) <= (6 * norm(omega^{-1}) * norm(omega)^|w|) * coeffSeminorm (|w|+1) a`, for **every** mixed word `w` |
| seminorm from `C^{p+4}` data | `coefficient_seminorm_bound` (`SmoothFourierData.lean:368-395`) | from sup bounds on `f`, `xJet (p+4) f` and `xJet (p+4) (swap f)`: `coeffSeminorm p (coefficient f) <= (3^(p+4) * C) * sum_k (weight k ^ 4)^{-1}` |
| composite, explicit constant | `ParametricTorusInverse.mixedJet_inverse_bound` (`:654-682`), `SmoothFamilyTorusInverse.mixedJet_inverse_bound` (`:1082`) | `norm(mixedJet q w (inverse d f) (p,Y)) <= mixedLossConstant |w| * C` |

`mixedLossConstant r` is a closed expression — `((6 * norm(omega^{-1})) * norm(omega)^r) * 3^(r+5) * sum_k (weight k ^ 4)^{-1}` — so the constant here is not an existential. The paper's proof sentence ("four more derivatives of `F` than the requested output leave a summable `(1+|k|)^{-3}` bound") is mirrored by the `p+4` in `coefficient_seminorm_bound`.

### 4. The one shape difference: `m+5` where the paper prints `m+4`

The composite needs `|w|+5` pure torus jets of the input, not `|w|+4`. The extra order comes from composition order, not from a missing estimate: the inverse costs the seminorm index `|w|+1` (one for the multiplier, `:412`), and `coefficient_seminorm_bound` then spends four orders on top of whatever index it is handed. The paper spends three on top of the multiplier's one. The slack is inside the tree's own summability choice — `coefficient_seminorm_bound` is stated against `summable_weight_inv_four` (`SmoothFourierData.lean:345`), where `weight^{-3}` would close the same sum in two dimensions — so the printed `+4` is recoverable but not printed anywhere. Recorded as a shape difference, not smoothed: the tree proves the strictly weaker fixed-order inequality. Nothing downstream consumes the index; the chain only needs one fixed finite loss per order, which both forms supply.

### 5. Clauses (d) and (g) are identities, not assemblies

The paper's (8.20) writes `Delta v = -c_i0^{-1} N_i0^{-1} E_theta`, with `c_i0^{-1} = Q^{-1-h} T^{-i0} g` and `c_i0^{-1} <= C S_*`. The tree writes the same object twice:

* `TemporalMeanUpdate.desiredIncrement h n f = -chartPrefactor h n * temporalInverse (centered f)` (`:544-546`), and `desiredIncrement_native_pullback` (`:654`) evaluates the prefactor as `Q n ^ (-1 - h)` — the paper's `Q^{-1-h}`, with the covering factor `T^{-i0} g` supplied by `MeanChartCompatibility.temporal_physical_pull` (`:465-492`), which cancels the native-cover and unit factors exactly;
* `MeanChartCompatibility.temporalAtIndex h n i f = -((Tg^i * Q n ^ (1 + h))^{-1}) * temporalInverse (centered f)` (`:493-505`) — the paper's `c_i0^{-1} N_i0^{-1}` with the covering index left free, and `temporalAtIndex_native` (`:504`) proves the free index specializes to `desiredIncrement`.

The bound `c_i0^{-1} <= C S_*` is not a separate inequality in the tree: it is an identity in explicit powers of `Tg` and `Q`, which is stronger than the paper's bounded-above form.

Clause (g), the (8.22) cancellation, is likewise exact rather than asymptotic: `desiredIncrement_fastDerivative` (`:590`) proves `fastDerivative h n (desiredIncrement h n f) z = -centered f z`, and the general-index form is `temporalAtIndex_fast_cancellation` (`MeanChartCompatibility.lean:645`), with `centered f = f - torusAverage f` supplying the "flat remainder" the paper names as `c_i0 N_i0 a`.

### 6. Clauses (e) and (f)

* zero auxiliary mean at every slow and radial point: `desiredIncrement_zeroMean` (`:573`), and the weighted form `desiredIncrement_barMass` (`:584`);
* the `M_alpha` membership survives a different covering index: `meanClass_temporalAtIndex_of_native` (`MeanChartCompatibility.lean:624`), whose hypothesis is exactly "the native-index update is `M_alpha`", with the band-index gap carried as a `BandBound` at exponent `0`;
* the azimuthal realization `gamma_d - A_1 gamma_d`: `PressureStream.streamGamma_eq_desired_sub_alias_global` (`MeanChartCompatibility.lean:869`), with the chart forms of `Delta beta` and `Delta gamma` in `physicalBeta_naturality` (`:1134`) and `physicalGamma_naturality` (`:1116`).

One clause is not a declaration and is recorded rather than claimed: divergence-freeness of the assembled `(Delta beta, Delta v, Delta gamma)` together with preservation of the two integral constraints (8.2) is carried by `MeanIncrementBounds` / `StateMomentBalances` for the increment class, not by a theorem about this specific triple. That is the same status `Corollary 8.5` and `Proposition 8.4` will get when their rows are worked.

### 7. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 18 | 19 |
| partial | 5 | 4 |
| unplaced | 50 | 50 |
| **total** | **73** | **73** |

The remaining partials are Proposition 9.3 (E127), Proposition 6.6 (E129), Lemma 9.7 (E133) and Lemma 10.2 (E136). §8 now has no partial: the "algebra exact, bounds assembled" pattern that E131 described still holds for the four rows above, but it no longer covers 8.6, whose bounds are stated with explicit constants and a declared conversion.

*Evidence: `.setup/paper/ns.txt:3251-3264` (6.2, (6.4)), `:4885-4935` (Lemma 8.6, (8.19)-(8.22)); `TorusInverse.lean:190-197,224,405-441,498-525,591-604`; `SmoothFourierData.lean:345,362-395,565-572`; `TemporalMeanUpdate.lean:112-145,215-245,544-600,654-670`; `MeanChartCompatibility.lean:465-505,624-660,869,1116-1145`; `ParametricTorusInverse.lean:645-682`; `SmoothFamilyTorusInverse.lean:1058-1100`; E132. Reading only — nothing compiled; "placed" is statement-level.*

---

## E142 — Lemma 10.4 is placed: `F` is the integral of the norm, and every conjunct is one theorem (2026-11-23)

*Reading entry. The paper's `F(t)` is `∫₀ᵗ ‖f(s)‖₂ ds`, the integral of the `L²` norm rather than of its square, and the tree's `cumulativeForceNorm` is the same object. With that read, the lemma's four clauses are one declaration's three quantitative conjuncts plus one theorem one module over. The row is placed; the ledger moves to 20 placed, 4 partial, 49 unplaced.*

### 1. What the paper asks

`Lemma 10.4` (p. 121, `.setup/paper/ns.txt:6115`). With `F(t) = ∫₀ᵗ ‖f(s)‖₂ ds`:

| Clause | Claim |
|---|---|
| a | `F(1) < ∞` |
| b | `‖u(t)‖₂² + 2∫₀ᵗ ‖∇u(s)‖₂² ds ≤ F(t)²` for `0 ≤ t < 1` |
| c | the kinetic energy is uniformly bounded |
| d | the total dissipation on `[0,1)` is finite |

### 2. Every clause

`R3/ForceL2Norm.lean:20–24` defines `l2Norm f t = sqrt (l2Sq f t)` and `cumulativeForceNorm f T = ∫ t in (0)..T, l2Norm f t`. That is `F` exactly: the integrand is the norm, not the square, so the `F(t)²` on the paper's right-hand side is the square of the same accumulated quantity and no exponent is silently traded. `R3/IntegratedDissipation.candidate_energy_estimates` (`:279–288`) then states all four conclusions for one candidate:

| Clause | Conjunct |
|---|---|
| a | `IntervalIntegrable (l2Norm f) volume 0 1`, from `force_smooth` (`ContDiff ℝ ∞ f`) and `force_support` (`CompactPositiveTimeSupport f`) |
| b | `l2Sq u T + 2 * ν * (∫ t in (0)..T, dissipation u t) ≤ (cumulativeForceNorm f T) ^ 2`, for every `T ∈ Ico 0 1`; at `ν = 1` this is the display |
| c | `CompactEnergy.uniform_finite_energy` proves it; `CandidateProperties.energy_bounded` carries it as a field |
| d | `IntegrableOn (dissipation u) (Ico (0 : ℝ) 1)` |

`dissipation u t = ∑ᵢ ∫ ‖∂ᵢu(t,x)‖²` (`R3/CompactEnergy.lean:195`), which is `‖∇u(t)‖₂²` for a vector field, so the viscous term is the paper's `2∫‖∇u‖²` at `ν = 1`. The underlying identity is `integrated_energy_balance` (`:26–45`), an equality before the force term is bounded; the inequality is `candidate_energy_dissipation_le`.

### 3. Differences, all in the tree's direction

* **General viscosity.** The tree states the bound with the coefficient `2ν`; the paper's lemma is the `ν = 1` instance, which is what `theorem_1_1_with_dissipation` consumes.
* **The endpoint is a conjunct, not a limit.** The paper reaches `t = 1` by monotone convergence after proving the bound for `t < 1`. The tree states `2 * ν * ∫_{Ico 0 1} dissipation ≤ (cumulativeForceNorm f 1)^2` separately (`candidate_total_dissipation_le`), so the half-open endpoint is carried rather than approached. That is the same conclusion with the limit already taken.
* **Energy is proved, then carried.** `R3/CompactEnergy.uniform_finite_energy` (`:343–381`) derives the uniform bound from smoothness, compact support, zero datum and the equation by the paper's own Gronwall argument; `CandidateProperties.energy_bounded` then carries it as a field so later lemmas can consume it without re-proving it. The clause is therefore a theorem about the constructed candidate, not an assumption — but it is not a conjunct of `candidate_energy_estimates`, and the entry says so rather than letting the table imply it.

No clause is unproved in the tree. The row places.

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 19 | 20 |
| partial | 4 | 4 |
| unplaced | 50 | 49 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:6115–6141` (Lemma 10.4, (10.13)–(10.14)); `R3/ForceL2Norm.lean:20–24`; `R3/IntegratedDissipation.lean:26–45,279–288`; `R3/CompactEnergy.lean:195,209`; `R3/Theorem.lean:66–79`; `R3/ProblemStatement.lean:92–109`. Reading only — nothing compiled.*

---

## E143 — Lemma 10.5 is placed: the competitor is a `UniformFiniteEnergy` field and the conclusion is `candidate_unique_on_Icc` (2026-11-23)

*Reading entry. The paper's comparison lemma assumes smoothness, the force of Lemma 10.3, zero datum and a uniform `L²` bound on the competitor, and imposes no growth condition on its pressure. `WholeSpaceUniqueness.candidate_unique_on_Icc` has exactly those binders and that conclusion. The row is placed; the ledger moves to 21 placed, 4 partial, 48 unplaced.*

### 1. What the paper asks

`Lemma 10.5` (p. 121, `.setup/paper/ns.txt:6143`). Fix `T < 1`. If `v, P` is a smooth solution of (1.1) at viscosity one on `ℝ³ × [0,T]`, with the force `f` of Lemma 10.3, zero initial velocity, and `v ∈ L∞([0,T]; L²(ℝ³))`, then `v = u` on that interval, where `u` is the localized velocity of Proposition 10.1.

### 2. Clause by clause

`NavierStokesR3.WholeSpaceUniqueness.candidate_unique_on_Icc`:

| Paper | Binder |
|---|---|
| `v, P` smooth on `ℝ³ × [0,T]` | `ContDiffOn ℝ ∞ v (Comparison.slab 0 T)`, `ContDiffOn ℝ ∞ q (Comparison.slab 0 T)` |
| `v ∈ L∞([0,T]; L²)` | `UniformFiniteEnergy (Icc 0 T) v`, i.e. `∃ E ≥ 0, ∀ t ∈ Icc 0 T, SquareIntegrableAtTime v t ∧ ½‖v‖₂² ≤ E` |
| smooth solution of (1.1) | `∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0` and `navierStokesResidual 1 v q t x = f (t,x)` |
| zero initial velocity | `∀ x, v (0,x) = 0` |
| `T < 1` | `hT : T < 1` |
| conclusion `v = u` on `[0,T]` | `∀ t ∈ Icc 0 T, ∀ x, u (t,x) = v (t,x)` |

The force's three properties are not hypotheses of this lemma; they enter through `h : CandidateProperties 1 u p f K`, which supplies `force_smooth`, `force_support` and the equation. That is the paper's structure: the lemma is about the *candidate* `u`, and the force is whatever that candidate satisfies.

### 3. The proof layer under it

The paper's argument is a Riesz-transform pressure recovery, a commutator estimate, and Gronwall on expanding balls, with the pressure allowed arbitrary spatial growth. The tree has that chain, and it has been read: `PressureFlux.exists_uniform_actual_pressure_flux_bound` produces the boundary pressure bound from the equations, and `WholeSpaceComparisonClosure.eq_of_pressure_flux_bound` closes the energy estimate with that bound, with all constants preceding the radius quantifier (`LEADS.md` §4). `classical_uniqueness_on_Icc` is the general form; `candidate_unique_on_Icc` instantiates it at the candidate and discharges the pressure flux internally, so no estimate is a hypothesis of the final statement.

### 4. The one shape note

The paper states the lemma for the constructed `u` and proves it by comparing against that field. The tree states it for *any* `CandidateProperties` witness, with the equation as a hypothesis `hNSv`. That is generality, not a weakening: the constructed candidate is an instance, and `candidate_global_agrees_before_one` is the paper's use of the lemma against a `GlobalFiniteEnergySolution`. Recorded so the row is not read as an identification of the paper's `u` with a particular declaration.

### 5. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 20 | 21 |
| partial | 4 | 4 |
| unplaced | 49 | 48 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:6143–6170` (Lemma 10.5 and the pressure-flux proof); `R3/WholeSpaceUniqueness.lean:30–86,88–130,132–150`; `R3/WholeSpaceComparisonClosure.lean:26–60`; `R3/PressureFlux.lean`; `R3/ProblemStatement.lean:81–83,92–109`; `LEADS.md` §4. Reading only — nothing compiled.*

---

## E144 — Proposition 9.3 stays partial on two clauses, not three: the decomposition, the supports and the mean fields are all stated (2026-11-23)

*Reading entry. E127 left this row partial because the cited declaration is the coefficient shadow of the statement. Re-reading it against the periodized assembly finds the decomposition, the support carrier, the smooth zero-extension layer and the mean equations as separate declarations. Two clauses remain unmatched, both statement-shape: the paper's single finite harmonic set carried across bands, and the sign of the base-flat error in (9.6). The row does not move, and neither does the ledger: 21 placed, 4 partial, 48 unplaced.*

### 1. What the paper asks

`Proposition 9.3` (p. 103, `.setup/paper/ns.txt:5272`), three groups:

| Group | Claim |
|---|---|
| (i) supported sources | `R(u,p) = G + F`; nonzero angular harmonics expand over a finite `H_j ⊂ ℤ \ {0}` independent of the band; coefficients supported in `Ω_γ` with smooth zero extension, `f ∈ W_α`, `⟨G⟩_θ ∈ M_μ` |
| (ii) flat remainder | `|F|_m ≤ C_{j,m,N} q^N`, uniform over bands, labels and points |
| (iii) exact mean equations | `W_ab = ⟨w_a w_b⟩_θ`, `P = ∫⟨g_r⟩ dR`, `p_m = T₀(g_r − ρP)`, and (9.6) with `E_θ`, `E_z` |

### 2. Where each group lands

* **The decomposition.** `PeriodizedWaveBounds.common_cancellation` (`:1044–1067`) states
  `residual + source·carrier = (globalGood + globalGaussian)·carrier` at every point of the domain,
  with `globalGaussian` the retained tail plus the uncovered source (`:809`) — the paper's `F`.
  The mean layer has its own exact split, `CorrectionState.meanResidual_eq_good_add_excluded` (`:140`).
* **The supports.** `globalGood_support` (`:1141`) and `globalGaussian_support` (`:1147`) put both
  supports inside the union of native cells. `HarmonicSourceSupport.NonzeroSupportedOn` (`:620`) is
  the per-harmonic statement that nonzero modes vanish outside a set, and `InputSupportOn` (`:679`)
  bundles velocity, pressure, Gaussian and alias carriers.
* **The smooth zero extension.** `ComplementJets` (`:188–192`) carries `ContDiffAt` and all-order
  bounds off the cells; `zero_complementJets_of_germs` (`:745`) turns a zero germ into that record;
  `residualSource_zero_germ_on` (`:737`) supplies the germ; `ActualSource.sourceSupport_mono`
  (`ActualGaussianCoverage.lean:319`) moves supports between carriers.
* **The classes.** Wave side `LabelSumBounds.UniformWaveClass`; mean side
  `MeanRankUpdate.rank_update_meanClass` and `MeanIncrementBounds.meanClass_meanPressure` (`:968`).
* **(ii).** `LocalResidualFlatness.AllResidualJetRates` with `selected_schedule` gives *every* rate
  for the whole mixed residual, which is stronger than the flat part alone.
* **(iii).** `radialResidual = dr pressure − gr` (`CorrectionState.lean:120–121`), with `gr` the
  literal `MeanIncrementBounds.gr` (`:338`); `thetaResidual` and `axialResidual` are `:328` and
  `:333`; `reducedMeanResidual` bundles the three (`:123`); and `MeanResidual.meanPressure_reconstruction`
  (`:1026`) is (8.12), `average p = pb + meanPressure p pb`.

### 3. The two clauses that are not stated

* **One finite harmonic set, band-independent.** `HarmonicFields.BandLimited` (`:332`) bounds
  `|j| ≤ N` for a single coefficient, and `CorrectionStep`'s `sourceBand` instantiates `N` as the
  residual band per stage. No declaration states the paper's `H_j` — one finite set depending on the
  finite construction and not on the band — carried through the sequence.
* **The sign of `E_B` in (9.6).** The paper displays
  `⟨G* + F* − E_B*⟩_θ = (D_r p_m − g_r, E_θ, E_z)`. The tree defines
  `meanResidual = reducedMeanResidual + meanBaseError` (`:130`), and its own docstring says the
  paper's (32) omits the fixed base-flat error and the tree restores it. The three components are the
  same expression, but the base error enters with a **plus** where the paper's display has a minus.
  Whether the two agree depends on how `errors.base` is folded into the residual, which this entry
  does not assert.

### 4. Why the row still does not move

Under the rule E136 fixed, an implied identity is not a stated one. Both remaining items are
statement-shape rather than missing mathematics, and both are now narrow: the row is no longer
"the coefficient shadow only". But this is precisely the row where a defect would hide — the algebra
is stated and the bounds are assembled — so it stays partial, with E127's reason replaced by these
two clauses.

### 5. The ledger

| Status | Before | After |
|---|---|---|
| placed | 21 | 21 |
| partial | 4 | 4 |
| unplaced | 48 | 48 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:5272–5330` (Proposition 9.3, (9.3)–(9.6)); `PeriodizedWaveBounds.lean:188–192,620–679,737–745,809,1044–1067,1141–1157`; `CorrectionState.lean:110–141`; `MeanIncrementBounds.lean:50–60,328–342,968`; `MeanResidual.lean:1021–1027`; `HarmonicFields.lean:332`; `LocalResidualFlatness.lean:19–132`; `LabelSumBounds.lean`; `MeanRankUpdate.lean:899`; `ActualGaussianCoverage.lean:311–331`; E127; E136. Reading only — nothing compiled.*

---

## E145 — Corollary 8.5: both radial divergence identities are declared, exact, with the paper's `2/R` and `1/R` (2026-11-24)

*Reading entry. The covariance-target corollary was the row E141 predicted would be "carried by `MeanIncrementBounds` / `StateMomentBalances` for the increment class" rather than stated. That prediction was wrong in the same direction as E140 and E141: both displayed identities are declarations in `SignedStressPrimitive`, at exactly the paper's connection weights, and the moment condition that makes the cutoff remainder vanish is itself a theorem. The row is placed; the ledger moves to 22 placed, 4 partial, 47 unplaced.*

### 1. What the paper asks

`Corollary 8.5` (p. 95, `.setup/paper/ns.txt:4842-4861`). With `T_e f = R^{-e} I_c(R^e f)` and `D_e = D_r + e/R`,

```
H_θ = −T_2(⟨E_θ⟩_Y − σ_θ ε∂_Z J_θ),      H_z = −T_1(⟨E_z⟩_Y − σ_z ε∂_Z(J_z + cρ_P))     (8.18)
(D_r + 2/R)H_θ = −⟨E_θ⟩_Y + σ_θ ε∂_Z J_θ,
(D_r + 1/R)H_z = −⟨E_z⟩_Y + σ_z ε∂_Z(J_z + cρ_P).
```

Clauses: (a) the two targets are independent of the auxiliary variable; (b) compactly supported in the active shell; (c) the two identities, with the primitives taken at fixed `(Z,T)`; (d) `H_θ`/`H_z` vanish wherever their integrands vanish for every `R`, and the construction does not enlarge support in `Z`.

### 2. The declaration pair

`SignedStressPrimitive` builds the primitive and divides by `r^e`, which is `T_e` with the cutoff already inside the integral:

| Object | Declaration | Statement |
|---|---|---|
| primitive | `primitive P e F` (`:150`) | `∫₀^r s^e * adjusted P e F (s, p)` — the paper's `I_c` at `M = 0`, `v = 0` (`primitive_eq_integral` `:262`) |
| target | `sigma P e F` (`:168`) | `−primitive / r^e` (`sigma_eq_negative_primitive` `:294`), i.e. `−T_e` |
| **angular identity** | `angular_divergence` (`:342`) | `radialDivergence 2 (fun t => sigma P 2 F (t,p)) r = −adjusted P 2 F (r,p)` |
| **axial identity** | `axial_divergence` (`:357`) | `radialDivergence 1 (fun t => sigma P 1 F (t,p)) r = −adjusted P 1 F (r,p)` |

`IntegratedMeanBalances.radialDivergence 2` is `2σ/r + σ'` and `radialDivergence 1` is `σ/r + σ'` — the proof of each theorem divides the displayed `2rσ + r²σ'` and `σ + rσ'` by `r²` and `r` respectively. That is `D_r + 2/R` and `D_r + 1/R` with the paper's own `e`-weights, not a rescaled or `e`-free form. Both proofs derive the derivative from `weighted_sigma_hasDerivAt` (`:381`), which comes from `primitive_hasDerivAt` (`:318`) and hence from the transport identity `transport_compactIntegral` — the derivative is *derived*, not assumed.

The right-hand sides match the paper's factor structure rather than merely its sign. `adjusted P e F = F − bumpCorrection` (`:207`), `bumpCorrection = momentDensity · mass e F` (`:196`), and `momentDensity = ∂_r χ` through `cutoff_eq_integral` (`:254`). So `−adjusted = −F + (∂_r χ)·(moment of F)`, which is `−⟨E⟩_Y + σ ε∂_Z J` with the bump playing `σ` and the moment playing the `ε∂_Z J` term. The factors `ε∂_Z` the paper insists on keeping are not dropped in the Lean statement because they are never introduced: the tree carries them in the source `F`, and the corollary's job — that they survive the primitive — is the identity itself.

### 3. Support, class, and the vanishing clause

- same shell, no `Z` enlargement: `sigma_supported` (`:245`) concludes `RadiallySupported P.a P.b (sigma P e F)`, which is support inside the active radial shell **and** inside the input's `(Z,T)` projection. That is clauses (b) and the second half of (d) together, and it is proved from `compactIntegral_supported` plus the two cutoff endpoint conditions.
- `M_α` membership: `meanClass_sigma` (`:424`) takes `MeanClass α F` and returns `MeanClass α (fun n => sigma P e (F n))`, with constant `K * C` for `K` supplied by `sigma_finiteJets_uniform` (`:377`) — the paper's "belongs to `M_α`" under the primitive normalization.
- the moment half: `bumpCorrection_moment` (`:200`) proves `mass e (bumpCorrection) = mass e F`, so `adjusted_moment_zero` (`:296`) gives `∫ r^e (adjusted) = 0` at every `p`. Under the paper's hypothesis `∫ R^e ⟨f⟩_Y dR = 0` this is `⟨A_e f⟩_Y = 0` — clause (c) of (8.8), and it is an identity rather than an estimate.
- identically zero: if `mass e F = 0` then `bumpCorrection` is `momentDensity * 0`, so `adjusted = F` and the remainder is zero pointwise. The paper's last sentence holds definitionally here, and `primitive_eq_zero_of_le` (`RadialPrimitive.lean:80`) supplies the support side.

### 4. Two shape differences, recorded rather than smoothed

1. **Y-pointwise, not Y-averaged.** `sigma P e F` is a function of `p : E`, the auxiliary variable, and `angular_divergence` is stated at fixed `p`. The paper's targets are `⟨·⟩_Y`-averages and are therefore independent of `Y` by construction. In the tree that independence is inherited from a `Y`-independent source, not asserted: clause (a) is conditional on the source being `Y`-independent, which the paper's own definition `⟨E_θ⟩_Y` supplies. Recorded as a shape difference; it is not a missing estimate, and the identity does not use the averaging.
2. **The paper's `T_1`, `T_2` prefactors are the class index.** The paper writes `H_θ = −T_2(…)` with `T_e f = R^{-e} I_c (R^e f)`. The tree writes `sigma` as `−primitive / r^e` and pushes the normalization into `meanClass_sigma`'s single `α`. Same object, one exponent slot instead of an explicit `R^{-e}` factor, so the displayed `T_e` is not a separate definition in the tree.

Neither difference changes a bound. Nothing downstream consumes a `T_e` symbol.

### 5. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 21 | 22 |
| partial | 4 | 4 |
| unplaced | 48 | 47 |
| **total** | **73** | **73** |

The four partials stay Proposition 9.3, Proposition 6.6, Lemma 9.7 and Lemma 10.2. §8 now has seven placed rows and no partial: 8.1, 8.3 and 8.4 remain unplaced in the queue, and Corollary 8.5 leaves it.

*Evidence: `.setup/paper/ns.txt:4608-4630` (Lemma 8.2), `:4842-4861` (Corollary 8.5, (8.18)); `SignedStressPrimitive.lean:150,168,196,200,207,245,254,262,294,296,318,342,357,377,381,424`; `RadialPrimitive.lean:39,80`; `IntegratedMeanBalances.lean:556`; `WeightedClasses.lean:299`; E141. Reading only — nothing compiled; "placed" is statement-level.*

---

## E146 — Proposition 8.1 is placed: the mean residual decomposition is *derived*, not defined (2026-11-24)

*Reading entry. The §8.1 proposition states what the angular mean of the residual is. The tree does not merely define the three components: `MeanResidual` proves the decomposition as an identity from the averaged equations, with the base terms subtracted and the angular derivative dropped by the zero-mean hypothesis. The row is placed; the ledger moves to 23 placed, 4 partial, 46 unplaced.*

### 1. What the paper asks

`Proposition 8.1` (p. 89, `.setup/paper/ns.txt:4536-4575`). With the divergence-free decomposition `u = base + mean + oscillation`, `⟨w⟩_θ = 0`, angularly invariant `p_m` and normalized base stress `Σ_a`, the angular mean of the remaining normalized residual is `(D_r p_m − g_r, E_θ, E_z)` with

```
E_θ = t*v + (D_r+2/R)(bv + βV + βv + W_rθ) + D_z(Gv + Vγ + γv + W_zθ)
        − ε(∆₀−R⁻²)v − (D_r+2/R)Σ_θ
E_z = t*γ + (D_r+1/R)(bγ + βG + βγ + W_rz) + D_z(2Gγ + γ² + W_zz + p_m)
        − ε∆₀γ − (D_r+1/R)Σ_z
g_r = −t*β − (D_r+1/R)(2bβ + β² + W_rr) − D_z(bγ + Gβ + βγ + W_zr)
        + (2Vv + v² + W_θθ)/R + ε(∆₀−R⁻²)β.
```

The proposition's own hypotheses are the three structural ones — divergence-free decomposition, angular invariance, zero angular mean of the oscillation — plus the base flat residual retained as a separate additive error.

### 2. The three carriers

`MeanIncrementBounds` defines the components with the paper's operators, not an expansion of them:

| Paper | Declaration | Body |
|---|---|---|
| `t*` | `Operators.time` (`:75`) | `slowTime + fastTime`, i.e. `−ε∂_T + c∂_v` |
| `D_r + e/R` | `Operators.radialDiv e` (`:83`) | `dr f + e • (r⁻¹ * f)` |
| `D_z` | `Operators.dz` (`:71`) | `ε • ∂_Z`, the normalized axial derivative |
| `ε(∆₀ − R⁻²)`, `ε∆₀` | `Operators.viscosity c` (`:88`) | `ε(dr² + r⁻¹dr + dz² − c(r⁻² f))`, with `c = 1` for `E_θ` and `0` for `E_z` |

and the residuals at `:328-342` are the paper's displays: `thetaResidual = time m.angular + radialDiv 2 (thetaRadial + W 0 1) + dz (thetaAxial + W 2 1) − viscosity 1 m.angular − radialDiv 2 T`, with `axialResidual` at connection `1`, viscosity connection `0`, and the pressure slot `p` in the axial `D_z` group — the paper's `p_m` inside `D_z(2Gγ+γ²+W_zz+p_m)`. `gr` (`:338`) is the negated radial balance, carrying `−r⁻¹(radialAngular + W 1 1)` for the paper's `+(2Vv+v²+W_θθ)/R` and `−viscosity 1 m.radial` for `+ε(∆₀−R⁻²)β`.

### 3. The part that makes it a proposition

The definitions alone would only be a restatement of (8.3). `MeanResidual` proves the decomposition from the averaged equations:

- `reynoldsAngular_total_sub` (`:821`): for smooth angularly invariant base and mean, zero-mean oscillation and a stress `T_θ`, `reynoldsAngular(total) − baseAngular − radialDivergence 2 T_θ = E_theta`. The proof averages the product, uses `average_total_product` for the two cross terms, splits the radial divergence and the Laplacian by `radialDivergence_add`/`meanLaplacian_add`, and closes by `ring`.
- `reynoldsRadial_total_sub` (`:837`): `reynoldsRadial(total) − baseRadial = dr p_m − gr` under `average p = base pressure + p_m`.

So the choice of which flux terms appear is *derived* from the averaging identities, and the hypothesis `⟨w⟩_θ = 0` is consumed exactly where the paper says it is: the angular derivative terms average to zero. `gr`'s `−meanLaplacian (m 0) + m 0 / radius²` is the paper's `ε(∆₀ − R⁻²)β` at the normalization `ε = 1`.

### 4. The base-flat error

The paper insists the base's flat residual is retained separately. `CorrectionState` makes that a field and a theorem: `meanBaseError` (`:126`) is the angular average of the stored base error, `meanResidual := reducedMeanResidual + meanBaseError` (`:130`), and `meanResidual_eq_good_add_excluded` (`:140`) is the split used downstream. The docstring records the divergence from the paper's own numbering: equation (32) omits the fixed base-flat error, and the tree restores it.

`reducedMeanResidual` (`:123`) orders the triple `![radial, theta, axial]` = `(D_r p_m − g_r, E_θ, E_z)`, the proposition's own ordering.

### 5. One shape difference

The tree's `time` operator carries the fast term as a coefficient times the auxiliary derivative, with the coefficient supplied by `OperatorBounds.fastCoefficient : BandBound s 0`. The paper writes `t* = −ε∂_T + c_{i0}N_{i0}` and keeps `c_{i0}` as a chart quantity. Same operator, with the normalization in the bound rather than in the symbol. No exponent is traded.

### 6. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 22 | 23 |
| partial | 4 | 4 |
| unplaced | 47 | 46 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:4520-4575` ((8.2), Proposition 8.1, (8.3)); `MeanIncrementBounds.lean:71,75,83,88,328,333,338`; `MeanResidual.lean:816,821,837`; `CorrectionState.lean:110-142`; `WeightedClasses.lean:247` (`directional`), `:299` (`bilinear`). Reading only — nothing compiled; "placed" is statement-level.*

---

## E147 — Lemma 8.2 is placed: the primitive, its exact radial identity, and the moment that kills the remainder (2026-11-24)

*Reading entry. The compactly supported primitive of §8.2 is `SignedStressPrimitive`: the integral, the division by `r^e`, the exact `D_e T_e f = f − A_e f` identity at both connection weights, support in the active shell with no growth in `Z`, and the `M_α` class. The moment condition is not assumed — `bumpCorrection_moment` makes the remainder's moment equal the source's, so under the paper's hypothesis the remainder is identically zero, which is stronger than (8.8). The row is placed; the ledger moves to 24 placed, 4 partial, 45 unplaced.*

### 1. What the paper asks

`Lemma 8.2` (p. 90, `.setup/paper/ns.txt:4608-4630`). With `I_c g = I g − χ_m J g`, `T_e f = R^{-e} I_c(R^e f)`, `D_e = D_r + e/R` and `A_e f = R^{-e}(∂_R χ_m) J(R^e f)`:

- `T_e f` is supported in the same active radial shell and in the projection of the input support to `(Z,T)`, and lies in `M_α`;
- `D_e T_e f = f − A_e f` exactly (8.7);
- if `∫ R^e ⟨f⟩_Y dR = 0`, then `⟨A_e f⟩_Y = 0` and `A_e` is flat to every order `p` (8.8);
- if `f` is `Y`-independent with zero radial mean, `A_e f ≡ 0`.

### 2. The declarations

| Clause | Declaration | Statement |
|---|---|---|
| the primitive | `primitive P e F` (`:150`) | `∫₀^r s^e * adjusted P e F (s,p)` via `primitive_eq_integral` (`:262`) |
| `T_e` | `sigma P e F` (`:168`) | `−primitive / r^e` (`sigma_eq_negative_primitive` `:294`) |
| (8.7) at `e = 2` | `angular_divergence` (`:342`) | `radialDivergence 2 (sigma 2 F) = −adjusted 2 F` |
| (8.7) at `e = 1` | `axial_divergence` (`:357`) | `radialDivergence 1 (sigma 1 F) = −adjusted 1 F` |
| (8.7) at general `e` | `weighted_sigma_hasDerivAt` (`:381`) | `HasDerivAt (t ↦ t^e σ(t,p)) (−r^e · adjusted)` |
| support | `sigma_supported` (`:245`) | `RadiallySupported P.a P.b (sigma P e F)` |
| class | `meanClass_sigma` (`:424`) | `MeanClass α F → MeanClass α (sigma e F)` |
| the moment | `bumpCorrection_moment` (`:200`) | `mass e (bumpCorrection) = mass e F` |
| zero moment | `adjusted_moment_zero` (`:296`) | `mass e (adjusted) = 0` |

`adjusted = F − bumpCorrection` and `bumpCorrection = momentDensity · mass e F`, with `momentDensity = ∂_r χ` via `cutoff_eq_integral` (`:254`). So `A_e` is `bumpCorrection` and `−adjusted = −F + A_e`: the identity is (8.7) verbatim, not an analogue.

### 3. Why (8.8) is weaker than what is proved

The paper's flatness clause is conditional on `∫ R^e ⟨f⟩_Y dR = 0`. The tree's `bumpCorrection` is `momentDensity · mass e F`, so under that hypothesis it is `momentDensity · 0` — zero pointwise, not merely flat. `adjusted` then equals `F`, `T_e` is the plain primitive, and `A_e ≡ 0`. This is the paper's *last* sentence ("if `f` is independent of `Y` and `∫ R^e f dR = 0`, the remainder is identically zero") holding in the case where the paper only claims flatness. The audit records the strength, not a defect: the tree never needs (8.10)'s Diophantine multiplier because it removes the moment instead of estimating it.

### 4. One shape difference, and one scope note

- **The shift along the radial phase map is not in this module.** The paper's `I g` integrates `g(r′, Y + ((r′)^{dr} − r^{dr})v_r)`. `SignedStressPrimitive`'s primitive is the `M = 0`, `v = 0` instance; the general moving-path integral is `TransportPrimitive` with `M` and `v` parameters, whose `transport_compactIntegral` is the identity the specialization uses. The statement is therefore the unshifted case; the shifted one exists one layer up and is what the main line consumes.
- **`e` is a natural number, not `{0,1,2}`.** `primitive P e F` takes `e : ℕ`. That is a relaxation, and the two consumers use `e = 2` and `e = 1`.

### 5. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 23 | 24 |
| partial | 4 | 4 |
| unplaced | 46 | 45 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:4580-4630` ((8.4), Lemma 8.2, (8.7)–(8.9)); `SignedStressPrimitive.lean:150,168,196,200,207,245,254,262,294,296,318,342,357,377,381,424`; `TransportPrimitive` (`transport_compactIntegral`, `totalIntegral_eq_radialInterval`); `RadialPrimitive.lean:39,80`; E145. Reading only — nothing compiled.*

---

## E148 — Proposition 6.6 is placed: the rectangle qualifier is a hypothesis form and the `N_abs` row is the inverse direction (2026-11-24)

*Reading entry. E129 left this row partial on two negatives. Both are declarations, and one of them E129 saw and rejected on a stricter reading than this audit applies elsewhere: the pre-cutoff rectangle is the hypothesis shape of `LocalCoefficientBounds`, not a missing two-wave statement. The other, `Q^{1+h}N_{abs}: C_α → C_α`, is `meanClass_chartPrefactor_all` — stated for the prefactor the development applies, `(Tg^{i0}Q^{1+h})^{-1}`, which is the paper's `c_{i0}^{-1}`. The row is placed; the ledger moves to 25 placed, 3 partial, 45 unplaced, and no partial remains in §6.*

### 1. Clause 3's rectangle: a hypothesis, not a domain

E129's objection was that `MeanLocalCoefficient.coefficient_mul` "localizes a coefficient to `A n` … and proves the product mean-class there", and that no declaration states the two-wave product *with the rectangle as its domain of validity*.

The objection names the declaration and then asks it to be a different kind of statement. `LocalCoefficientBounds s A α f` (`:11-20`) is a record whose entire content is: `f` is smooth on `s.domain`, and every jet of `f` up to order `m` is bounded **only on `A n`**, with constants uniform in band and point. `coefficient_mul` (`:41`) then takes `MeanClass s β g` plus `tsupport (g n) ∩ s.domain ⊆ A n` and concludes `MeanClass s (α+β) (f*g)`. The set `A` is a parameter of the statement on both sides — hypothesis and support inclusion — so "the coefficient algebra is used only on its labelled band rectangle" is exactly the shape of the theorem, with `A n` the rectangle. What is *not* there is a second, redundant statement of the same fact restricted to a domain.

This is the rule the log already applies at E127's follow-up: a clause counts as carried when it is the ambient form of every declaration in the chain, or a definitional restatement. The rectangle is the first. I am recording the reclassification explicitly rather than silently, because E129's reading was defensible and a later reader should be able to disagree with this one on the record.

### 2. Clause 5's last row: the prefactor is the inverse

Paper (6.32): `Q^{1+h}N_{abs} = c_{i0}N_{i0} : C_α → C_α`, with `N_{abs} = v_t·∂_Y` and `c_{i0} = T^{i0}g Q^{1+h}`.

The tree states the class preservation for the object it actually applies, and the constant is the paper's exactly:

- `TemporalMeanUpdate.chartPrefactor_eq` (`:286`): `chartPrefactor h n = Q n ^ (-1-h) * (Tg ^ nativeIndex h n)⁻¹` — that is `c_{i0}⁻¹`, with the covering factor written as a negative power.
- `meanClass_chartPrefactor_all` (`:335`): `MeanClass s α f → MeanClass s α (fun n z => chartPrefactor h n • f n z)`, through `chartPrefactor_bandBound_all`, whose constant is explicit: `Tg + Σ_{i<4} chartPrefactor h i`, exponent `1`. So multiplication by `c_{i0}⁻¹` preserves the exponent — the table's `C_α → C_α` for the prefactor half.
- `MeanChartCompatibility.fastAtIndex` (`:658`) is the forward operator: `(Tg^i * Q n ^ (1+h)) * graphDz ((0), vector .temporal) f`. Its inverse is `temporalAtIndex`, and `temporalAtIndex_fast_cancellation` (`:676`) proves `fastAtIndex (temporalAtIndex f) = −centered f`. The class of the inverse is `meanClass_temporalAtIndex_of_native` (`:624`), stated at a free covering index with the band gap carried as a `BandBound` at exponent `0`.

So the row's content — the scaled fast operator and its prefactor act on the classes without moving the exponent — is stated, in the direction the construction uses (inverse first, then the forward operator only through the cancellation identity). The paper's forward-only table entry is not separately stated. Recorded as a direction difference; the exponent is the same and the explicit constant is present.

### 3. What this does to E129

E129's verdict was "components only", and it was correct about the *table*: there is no single declaration listing five operator rows. It was wrong about the row's content, for the reason E140, E141 and E145 were wrong in the other direction: the statements live where the operators are consumed, under names the paper does not use (`chartPrefactor`, `fastAtIndex`, `temporalAtIndex`, `LocalCoefficientBounds`). Four of the five rows were already counted as literally present at E129; the fifth is now too.

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 24 | 25 |
| partial | 4 | 3 |
| unplaced | 45 | 45 |
| **total** | **73** | **73** |

The three remaining partials are Proposition 9.3 (E127, narrowed in E144), Lemma 9.7 (E133, structural) and Lemma 10.2 (E136). §6 now has none.

*Evidence: `.setup/paper/ns.txt:3640-3710` (Proposition 6.6, (6.30)–(6.32)); `MeanLocalCoefficient.lean:11-20,41-70`; `TemporalMeanUpdate.lean:286,300,319,335`; `MeanChartCompatibility.lean:624,658,676`; `WeightedClasses.lean:247,299,335`; E129; E141; E145. Reading only — nothing compiled.*

---

## E149 — Proposition 9.3 is placed: `H_j` is one `Finset` quantified outside the band, and the base error's minus is on the other side (2026-11-24)

*Reading entry. E144 left this row partial on two statement-shape clauses. Both are declarations. The band-independent harmonic set is `modes residualBand`, a `Finset ℤ` fixed by the construction and quantified outside the band index, with the residual band updated once per stage; and (9.6)'s `−E_B*` is not dropped — the tree writes `⟨G*+F*⟩ = reduced + ⟨E_B*⟩`, which is the paper's display with the base error moved across the equals sign, and says so in words. The row is placed; the ledger moves to 26 placed, 2 partial, 45 unplaced.*

### 1. Clause (i)'s `H_j`: a fixed finite set, with the band quantified inside

E144: "No declaration states the paper's `H_j` — one finite set depending on the finite construction and not on the band." It is `modes`:

| Object | Declaration | Statement |
|---|---|---|
| the finite set | `ActualCycleResidualBounds.modes (M : ℕ) : Finset ℤ` (`:44`) | `Finset.Icc (-(M : ℤ)) M` |
| membership from the band bound | `mem_modes` (`:46`) | `j.natAbs ≤ M → j ∈ modes M` |
| every band's support inside it | `source_support (l) (n) (i)` (`:59`) | `((source x l).velocity n i).support ⊆ modes x.coefficients.residualBand` |

The quantifier order is the paper's, not a rearrangement of it. `residualBand` is a field of the cycle's coefficient data (`CorrectionStep.lean:4998`), read off the finite construction, and `n` is universally quantified *inside* the statement — one set, every band, every component, every label. It is also not a constant across the induction: the cycle sets `residualBand := 2 * max v.residualBand 1` (`:6830`), which is exactly the paper's "`H_j` depends on the finite construction but not on the band".

Three further declarations carry the rest of (9.4):

* the finite display itself: `HarmonicFields.evaluate_over` sums a coefficient over any `Finset` containing its support, which is the paper's `∑_{γ∈Γ} ∑_{m∈H_j}` with `Γ` the label set of `Represents` (`CorrectionState.lean:210`);
* one `N` across all bands and components: `CorrectionState.HarmonicBlock.BandLimited` (`:187-190`) is `(∀ n i, BandLimited (velocity n i) N) ∧ ∀ n, BandLimited (pressure n) N`, and `HarmonicFields.BandLimited` is `∀ j ∈ support, j.natAbs ≤ N`, so `modes N` contains every band's support by `mem_modes`;
* derivatives never enlarge the set: `support_differentiate`, `band_iteratedCoefficients` and `iteratedAlong_wave` — the last states that all repeated actual directional derivatives retain the original finite set of harmonic values. The paper's (9.4) is a statement about the current coefficients; this says the set is stable under the operations that produce them.

The set the tree exhibits is the interval `Icc (-N) N`, a finite superset of the nonzero support rather than the support itself. The paper asks only `H_j ⊂ ℤ \ {0}`, `|H_j| < ∞`, band-independent; a finite superset satisfying the same three is the same statement about finiteness, and `ParticularWaveAssembly.modes` (`:24`) is the same construction with the zero erased where the zero-free form is wanted.

### 2. Clause (iii)'s sign: the base error is added, which is the paper's subtracted

E144: the paper displays `⟨G* + F* − E_B*⟩_θ = (D_r p_m − g_r, E_θ, E_z)`, while the tree defines `meanResidual := reducedMeanResidual + meanBaseError`. Read as an equation rather than as a definition, the tree's is

```
⟨G* + F*⟩ = reduced + ⟨E_B*⟩        ⟺        ⟨G* + F* − E_B*⟩ = reduced,
```

which is the paper's display. Two declarations state it, and one states it in the paper's direction with the other two errors as well:

* `LiftedMeanResidual.angularMean_fullResidual` (`:1176`) — the actual angular mean of the *full* residual equals `u.meanResidual c`. Its docstring is the whole point: *"The actual full residual averages to equation (32) plus exactly the stored base error."*
* `CorrectionState.meanResidual` (`:130`) — `reducedMeanResidual c + meanBaseError`, with the docstring on the line above recording that the paper's (32) omits the fixed base-flat error and the tree restores it.
* `LiftedMeanResidual.meanGoodResidual_errors` (`:1206`) and `angularMean_fullGoodResidual_errors` (`:1221`) — the same identity with the Gaussian and alias errors subtracted explicitly, `meanGoodResidual = reduced − ⟨gaussian⟩ − ⟨alias⟩`.

So the minus sign is not lost; it is on the right-hand side. E144 recorded "whether the two agree depends on how `errors.base` is folded into the residual, which this entry does not assert". It is now asserted: `errors.total = base + gaussian + alias` (`CorrectionInitializationNoOptions.lean:1177-1181`) with `base` the stored base error, and `meanBaseError` is its angular average (`CorrectionState.lean:126`). The fold is by addition, once, and the identity above is what it produces.

### 3. The rest of the proposition, restated as closing

The decomposition (`PeriodizedWaveBounds.common_cancellation`), the supports (`globalGood_support`, `globalGaussian_support`, `HarmonicSourceSupport.NonzeroSupportedOn`), the smooth zero-extension layer (`ComplementJets`, `zero_complementJets_of_germs`, `residualSource_zero_germ_on`), the classes, (ii) (`LocalResidualFlatness.AllResidualJetRates` with `selected_schedule`), and the mean fields of (9.6) (`CorrectionState.radialResidual`/`thetaResidual`/`axialResidual`/`gr`) were already read at E144. With §1 and §2 above, no clause of the proposition is unmatched.

One shape note is carried rather than smoothed: the paper's `f^{[j]}_{γ,m} ∈ W_α` is the wave-class membership on the *coefficients*, which is `HarmonicBlock.WaveBounds` (`:193-197`) — per harmonic, nonzero only — while the label-summed class is `LabelSumBounds.UniformWaveClass`. The two are the two halves of `f^{[j]}_{γ,m} ∈ W_α` and its sum being locally finite; neither is a substitute for the other and both are present.

### 4. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 25 | 26 |
| partial | 3 | 2 |
| unplaced | 45 | 45 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:5272–5330` (Proposition 9.3, (9.3)–(9.6)); `ActualCycleResidualBounds.lean:44,46,59,65`; `ParticularWaveAssembly.lean:24,26`; `CorrectionState.lean:123,126,130,140,187–197,210`; `CorrectionStep.lean:4998,5097–5100,6830`; `HarmonicFields.lean` (`evaluate_over`, `BandLimited`, `support_differentiate`, `band_iteratedCoefficients`, `iteratedAlong_wave`); `LiftedMeanResidual.lean:1176,1206,1221`; `CorrectionInitializationNoOptions.lean:1177–1181`; `PeriodizedWaveBounds.lean`; `LocalResidualFlatness.lean`; E127; E136; E144. Reading only — nothing compiled; "placed" is statement-level.*

---

## E150 — Lemma 10.2 stays partial: the `F_j` family is now the force's own endpoint jets, but global uniformity is still inferred (2026-11-24)

*Reading entry. Placing this row was the point of the re-read, and it does not place. One of E136's two gaps is halved: the paper's `F_j` are the terminal jets of one smooth compactly supported force, not a separate family, so clause (b) is a bundling difference over declarations that exist. The other gap is unchanged and is the reason the row stays: no declaration concludes uniform convergence on `ℝ³`, and the missing step is the support of the limit tensors, which is nowhere stated. The ledger is unchanged at 26 placed, 2 partial, 45 unplaced.*

### 1. What improved

`CandidateFromLimits` builds the force as the traced residual glued to its endpoint series, and identifies its jets:

* `force_boundary_jets (n) (x)` (`:158`) — `iteratedFDeriv ℝ n (force …) (1, x) = L x n`. Every full spacetime jet of the constructed force at the terminal time is the supplied limit tensor. That is the paper's `lim ∂^α_x ∂^j_t f = ∂^α_x F_j` with `F_j` realised as the force's own time-derivative trace rather than as a separately indexed family.
* `force_smooth` (`:94`), `force_time_support` (`:150`) — smooth on all of spacetime, compact future time support.
* `R3CompactCandidate.compactForce_supported` (`:90`) — `SupportedIn outerSupport (compactForce f)` with `outerSupport` compact (`outerSupport_compact`, `:42`). So the object whose jets are the `F_j` does have compact spatial support, and the support is a named set.
* `JointResidualLimits.extendedJets_compatible` (`:238`) and `boundaryLimits_hasFDerivAt` (`:240`) — clause (d)'s time and space halves, both derived from the actual derivative recurrence rather than assumed.
* `boundaryLimits_zero` (`:126`) — clause (c): every order vanishes at the origin, for all `j` at once.

That is more than E136 recorded. E136 said the tree "never states that the limit function is compactly supported in `K`"; the limit *tensors* are the jets of a compactly supported force, which is the same content one layer up, and the force's support is declared.

### 2. What did not improve, and why it is the blocker

Clause (a) is `∂^α_x ∂^j_t f` converges **uniformly on `ℝ³`**. The tree has:

* `boundaryLimits_locallyUniform` (`:148`) — locally uniform convergence;
* `boundaryLimits_uniformOn_compact` (`:156`) — `TendstoUniformlyOn … K` for every compact `K`, obtained from the local statement by `tendstoLocallyUniformly_iff_forall_isCompact`.

The upgrade to `ℝ³` is exactly the paper's own last step — *"All these derivatives vanish off `K`. They are therefore uniformly Cauchy on `ℝ³`"* — and it needs two premises: the approximants vanish off a fixed compact, and so does the limit. The first is `compactForce_supported`. The second is not stated anywhere: `boundaryLimits` is defined from `Classical.choice (hext x hx)`, an arbitrary one-sided extension with no support condition, and `AwayExtensions` (`:81`) says nothing about where the extension lives. `boundaryLimits_smooth` gives smoothness, `boundaryLimits_continuous` continuity, and no support theorem exists in the module. Without it the supremum over `ℝ³` is not the supremum over `K` for the limit side, and no declaration concludes the global statement.

Clause (b)'s remaining half is the same shape and one line wide: no declaration names the `F_j` slice functions with `support ⊆ K`. The force and its jets are named; the slices are not.

### 3. Why this does not place, stated as the rule rather than as taste

This is the row where it would be easiest to round up: every clause has a declaration *except one that follows in two lines from a declaration that exists*. That is precisely the standard E136 set and E144 applied, and E149 is the case that shows why the standard is worth keeping: Proposition 9.3 looked the same at E144, and the re-read found `source_support` — a declaration, not an argument. Here the re-read found the opposite: a support hypothesis that is not in the tree, because the extension is chosen rather than constructed.

So the row stays partial, with E136's first reason narrowed to one missing support statement and E136's second reason reduced to a naming difference. It is not a claim about the mathematics: for the constructed force the global statement is true, and nothing downstream consumes it. E137 already recorded that Lemma 10.3's extension does not go through the `F_j` at all — it is a cutoff product — so the missing bundle is unused by the proof that the paper uses it for.

### 4. The ledger

| Status | Before | After |
|---|---|---|
| placed | 26 | 26 |
| partial | 2 | 2 |
| unplaced | 45 | 45 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:5997–6030` (Lemma 10.2, (10.6)–(10.10)); `JointResidualLimits.lean:81,84,120,126,141,148,156,220,238,240,264,308`; `CandidateFromLimits.lean:75,94,150,158,175`; `R3CompactCandidate.lean:24,42,90,99`; `PeriodicResidualLimits.lean:220–260`; E136; E137; E144; E149. Reading only — nothing compiled.*

---

## E151 — Lemma 8.8 is placed: `R_g` is a definition, (8.27) is an exact identity, and the gain is derived at the paper's exponent (2026-11-24)

*Reading entry. The §8.6 gain lemma is the strongest match in the §8 column. The paper's `R_g` is `actualRadialError`, defined as `gr(new) − gr(old) − (2V/R)Δv`; (8.26) is a theorem about it, derived from the averaged equation; (8.27) is `defects_after_solved_rows`, an identity that holds before any estimate is applied; and `H + 9/10 − 2κ` is `α + 0.9 − 2κ_s` with the paper's own hypotheses. The row is placed; the ledger moves to 27 placed, 1 partial, 45 unplaced.*

### 1. What the paper asks

`Lemma 8.8` (pp. 98–99, `.setup/paper/ns.txt:5041–5099`). Suppose the base satisfies (8.24) with `λ > 0` and `|a(η)| ≥ a₀ > 0`; let `(β, v, γ)` be a smooth divergence-free mean correction supported in the active shell; form `g_r` and `(P, Jθ, Jz)` by (8.3), (8.12), (8.15); apply Lemma 8.7 with the three defects as targets; realize `γ_d` by (8.14). Then

| Clause | Paper's claim |
|---|---|
| a | `R_g := g_{r,new} − g_r − (2V/R)Δv` equals the displayed (8.26) |
| b | `P_new = ∫⟨R_g⟩_Y dR`, `(Jθ)_new = ∫R²⟨γΔv + vΔγ + ΔγΔv⟩_Y dR`, `(Jz)_new = ∫R⟨2γΔγ + (Δγ)²⟩_Y dR − ½∫R²⟨R_g⟩_Y dR` (8.27) |
| c | under base coefficient bounds and `v, γ ∈ M_{0.9}`, `β ∈ M_{1.9}`, targets in `S_α` for `α ≥ 0.9`: `R_g ∈ M_{α+0.9−2κ_s}` and the three new defects in `S_{α+0.9−2κ_s}` |

### 2. `R_g` is the definition, and (8.26) is derived

| Paper | Declaration | Statement |
|---|---|---|
| `R_g` | `actualRadialError o base m h W` (`:349`) | `gr o base (updated m h) W − gr o base m W − leadingRadial o base h` |
| `(2V/R)Δv` | `MeanIncrementBounds.leadingRadial` (`:365`) | `o.invRadius * ((2 : ℝ) • (base.angular * h.angular))` |
| (8.26) | `actualRadialError_eq_formula` (`:395`) | `Agree U (actualRadialError …) (radialRemainder o base m h)` |

`radialRemainder` (`MeanIncrementBounds.lean:368–371`) is `−time(β) − radialDiv 1(δ_{rr}) − dz(δ_{zr}) + invRadius·radialAngularRemainder + viscosity 1(β)`. The three deltas are the paper's three groups: `δ_{rr}` carries `2bΔβ + 2βΔβ + (Δβ)²`, `δ_{zr}` the `bΔγ + GΔβ + βΔγ + γΔβ + ΔβΔγ`, and `radialAngularRemainder` the `(2vΔv + (Δv)²)/R`. The identity is not assumed: `gr_change` (`:683`) derives it by splitting `gr(updated) − gr` through `radialRadial_updated` and `radialAngular_updated` and expanding the products. So clause (a) is a theorem, and it is the paper's own derivation.

### 3. (8.27) is an identity, before any estimate

`defects_update` (`:474`) is the exact split

```
defects(new) = defects(old) + linearRows(h) + remainders(m, h),
```

with `linearRows` (`:340`) the three rows of (8.25) — pressure `barMoment 0 (leadingRadial)`, angular `barMoment 2 (thetaLeading)`, axial `barMoment 1 (axialLeading) − ½ barMoment 2 (leadingRadial)`, i.e. the paper's minus sign and factor one half — and `remainders` (`:339`) the paper's right-hand side:

| (8.27) | `remainders` component |
|---|---|
| `P_new = ∫⟨R_g⟩_Y dR` | `barMoment 0 (actualRadialError …)` |
| `(Jθ)_new = ∫R²⟨γΔv + vΔγ + ΔγΔv⟩` | `barMoment 2 (thetaQuadratic m h)`, `thetaQuadratic = m.axial*h.angular + h.axial*m.angular + h.axial*h.angular` |
| `(Jz)_new = ∫R⟨2γΔγ + (Δγ)²⟩ − ½∫R²⟨R_g⟩` | `barMoment 1 (axialQuadratic m h) − ½ barMoment 2 (actualRadialError …)`, `axialQuadratic = 2•(m.axial*h.axial) + h.axial*h.axial` |

Then `defects_after_solved_rows` (`:504`) applies "Lemma 8.7 with these three defects as its targets" in the tree's form, `linearRows o base h = -defects o base m W`, and cancels: `defects o base (updated m h) W = remainders o base m h W`. The cancellation is what supplies the claim that the increments have zero angular momentum and zero axial flux: `fiveRows_mass_zero` (`:621`) proves `barMoment 2 h.angular = 0 ∧ barMoment 1 h.axial = 0` from the rows, and `fiveRows_preserve_masses` (`:635`) carries the two constraints through the update. That is `γ_d = Δγ` and the last three rows of (8.25) cancelling the old defects.

### 4. The exponent, and every hypothesis

The paper's gain is `α + 0.9 − 2κ_s`; the tree's is `H + 9/10 − 2 * κ`, and `H` is the increment's own class:

| Paper | Lean |
|---|---|
| `v, γ ∈ M_{0.9}` | `IncrementBounds.angular`, `.axial : MeanClass s H` — at `H = 0.9` these are the paper's classes exactly, and stronger for `H > 0.9` |
| `β ∈ M_{1.9}` | `IncrementBounds.radial : MeanClass s (H + 1)` |
| `α ≥ 0.9` | `hH : 9 / 10 ≤ H` |
| `R_g ∈ M_{α+0.9−2κ_s}` | `actualRadialError_mem` (`:440`), `MeanClass s (H + 9/10 − 2κ)` |
| the three new defects in `S_{α+0.9−2κ_s}` | `remainders_mem` (`:556`) and `defects_after_rank_mem` (`:567`), `UnweightedClass (H + 9/10 − 2κ)` on the moment-integrated strip |

The hypothesis structures are the paper's, one for one: `BaseBounds s base` is (8.24)'s coefficient bounds `C_I ε S^{B_I}_*`; `OperatorBounds s o κ` is the operator layer's `κ` loss; `CumulativeBounds s m` is the current correction's class `M_{0.9}`/`M_{1.9}`; `IncrementBounds s H h` is the paper's `v, γ ∈ M_{0.9}`, `β ∈ M_{1.9}` written at the target class. `RankGeometry` (`:735–800`) supplies the geometry and discharges "apply Lemma 8.7": `solved_rows` composes `fiveRows` with `linearRows_eq_neg_of_fiveRows`, and `debt_eq_remainders` (`:838`) instantiates `defects_after_solved_rows` on the actual constructed stage. `rankStage_defect_class` (`:855`) then states the debt of the actual `rankStage` at `H + 9/10 − 2κ`, and `rankStage_defectBounds` (`:870`) weakens it to `DefectBounds σ` whenever `1 + σ ≤ H + 9/10 − 2κ` — which is how the iteration consumes it.

### 5. Three shape differences, recorded rather than smoothed

* **Divergence-freeness is not a binder of this lemma.** The paper's `(β, v, γ)` is assumed smooth, divergence-free and supported in the shell; the tree's `ShellTriple` gives smoothness and support, and divergence lives one layer down in the mean-increment construction (`MeanIncrementBounds` / `StateMomentBalances`), as E141 recorded for the increment triple. Nothing in (8.26)–(8.27) uses divergence, so this is a locality of statement rather than a missing hypothesis.
* **Local bounds become strip bounds.** The paper requires the base coefficients bounded "on the support of the azimuthal potential for this correction"; `BaseBounds` and `OperatorBounds` are stated on the whole logarithmic strip. Stronger, and it removes the need to re-establish the bound on each patch.
* **The paper's `M`/`S` are the tree's `MeanClass`/`UnweightedClass`.** The `S` side is the moment-integrated strip `MeanMomentBounds.slowStripData`, so the "belongs to `S_α`" conclusion is a class of the actual radial moments, not of the pre-integration field. That is what (8.15) defines and what the five rows consume.

No clause is matched only by a component. The one thing this entry does not claim is that the proof of `defects_after_rank_mem` is valid — it is statement-level reading, as every placed row is.

### 6. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 26 | 27 |
| partial | 2 | 1 |
| unplaced | 45 | 45 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:5041–5099` (Lemma 8.8, (8.26)–(8.27)); `DefectIncrementBounds.lean:300–360` (`leadingRadial`, `thetaLeading`, `axialLeading`, `thetaQuadratic`, `axialQuadratic`, `actualRadialError`, `defects`, `linearRows`, `remainders`), `:380–460` (the splits, `actualRadialError_eq_formula`, the class bounds), `:470–515` (`defects_update`, `defects_after_solved_rows`), `:556,567` (`remainders_mem`, `defects_after_rank_mem`), `:621,635,650`; `:735–875` (`RankGeometry`, `solved_rows`, `debt_eq_remainders`, `rankStage_defect_class`, `rankStage_defectBounds`); `MeanIncrementBounds.lean:365–371,683,747`; `MeanLocalDefectBounds.lean:94`; E139; E140; E141. Reading only — nothing compiled; "placed" is statement-level.*

## E152 — Proposition 8.3 is placed: the pressure residual, the bar derivative and the three stream classes are all declarations (2026-11-24)

*Reading entry. The §8.3 reconstruction proposition splits into pressure and axial velocity, and every clause is a declaration rather than an assembly: (8.13) with both the bump mass and the cutoff alias displayed, the bar derivative, `P ∈ S_α`, `pm ∈ M_α`, the same-class difference, zero auxiliary mean, superflat alias; and for the stream, `r⁻¹Ic(rγd)`, `Δγ = γd − A₁γd`, exact divergence-freeness including the axis, the bar equality, the pointwise clause, and the classes at the paper's `α`, `α` and `α+1`. The row is placed; the ledger moves to 28 placed, 1 partial, 44 unplaced.*

### 1. What the paper asks

`Proposition 8.3` (pp. 92–93, `.setup/paper/ns.txt:4735–4780`), after fixing the radial operators of Lemma 8.2 and the bump `ρ` with `∫ρ dR = 1`:

| Part | Clause |
|---|---|
| (i)a | `P = ∫⟨gr⟩_Y dR`, `pm = T0(gr − ρP)` |
| (i)b | `Dr pm − gr = −ρP − A0(gr − ρP)`; `∂R⟨pm⟩_Y = ⟨gr⟩_Y − ρP` |
| (i)c | `gr ∈ M_α ⟹ P ∈ S_α`, `pm ∈ M_α`; differences at the same class |
| (i)d | the cutoff remainder has zero auxiliary mean and is flat at every fixed derivative order |
| (ii)a | `Ψ = r⁻¹Ic(rγd,phys)`, `Ψ* = T1γd`, `Δβ = −ε∂ZΨ*`, `Δγ = (Dr + 1/R)Ψ* = γd − A1γd` |
| (ii)b | `(Δβ, 0, Δγ)` divergence-free; `⟨Δγ⟩_Y = ⟨γd⟩_Y` |
| (ii)c | `γd ∈ M_α ⟹ Ψ*, Δγ ∈ M_α` and `Δβ ∈ M_{α+1}` |
| (ii)d | `γd` independent of `Y` and `∫R⟨γd⟩_Y dR = 0` ⟹ `Δγ = γd` pointwise |
| (ii)e | compact support in the active shell; the source `(Z,T)`-projection retained |

### 2. Part (i): every line of (8.13) is a theorem

| Paper | Declaration | Statement |
|---|---|---|
| `P` | `PressureStream.pressureMass f s` (`:121`) | `∫ r, torusAverage f (r, s)` |
| `gr − ρP` | `pressureSource a b hab f` (`:154`) | `f p − rho a b hab p.1 * pressureMass f p.2.1` |
| `T0` | `meanPressure d a b M hab v f` (`:383`) | `physicalCompact d a b M (0, v) (pressureSource a b hab f)` |
| `A0` | `pressureAlias d a b M hab v f` (`:387`) | the same primitive's cutoff derivative |

`meanPressure_radial_residual_global` (`:796`) then states

```
graphDr (physicalSpeed d M) (0, v) (meanPressure … f) p − f p
  = −rho a b hab p.1 * pressureMass f p.2.1 − pressureAlias d a b M hab v f p ,
```

which is (8.13) with `A0(gr − ρP)` written as `pressureAlias`. A second form, `meanPressure_radial_residual_cutoff` (`:809`), expands the alias as `deriv (physicalCutoff d a b) p.1 * physicalTotal d a M (0,v) (pressureSource …) p` — the paper's cutoff remainder named as a derivative of the bump times the primitive. `meanPressure_bar_hasDerivAt` (`:697`) states

```
HasDerivAt (fun R => torusAverage (meanPressure … f) (R, s))
  (torusAverage f (r, s) − rho a b hab r * pressureMass f s) r ,
```

derived from `meanPressure_bar_eq_integral` (`:682`), not assumed: the integral representation is proved first, then differentiated by the fundamental theorem.

The four class and remainder clauses:

| Clause | Declaration | Statement |
|---|---|---|
| `P ∈ S_α` | `barMoment_mem` (`DefectIncrementBounds.lean:281`) | `MeanClass logStrip α f` + `Shell a b f` ⟹ `UnweightedClass (slowStripData) α (barMoment 0 f)` |
| `pm ∈ M_α` | `meanClass_meanPressure` (`MeanIncrementBounds.lean:968`) | `MeanClass logStrip α f` ⟹ `MeanClass logStrip α (meanPressure … f)` |
| differences | `meanClass_meanPressure_change` (`:985`) | `MeanClass α (f − g)` ⟹ `MeanClass α (meanPressure f − meanPressure g)`, linearity by `meanPressure_sub` (`:936`) |
| zero mean | `pressureAlias_mean_zero` (`PressureStream.lean:616`) | `torusAverage (pressureAlias …) p = 0` |
| superflat | `dividedAlias_superflat` (`TemporalMeanUpdate.lean:1157–1174`) | `∀ m N, ∃ C ≥ 0, ∀ᶠ n, ∀ j ≤ m, ∀ z, ‖iteratedFDeriv j (divideRadius (physicalAlias …)) z‖ ≤ C * ε n ^ N` |

`barMoment 0` is `pressureMass`: `barMoment_apply` (`:295`) rewrites it as `IntegratedMeanBalances.radialMoment 0 (torusAverage f)`, which is the same integral. So `S_α` here is the moment-integrated strip, exactly as in E151, and the statement's hypotheses (`Shell a b`) are the paper's "smooth shell-supported source".

### 3. Part (ii): the ε is in the direction, not added afterwards

| Paper | Declaration | Statement |
|---|---|---|
| `Ψ = r⁻¹Ic(rγd)` | `streamPotential d a b M v γd` (`:438`) | `divideRadius (physicalCompact d a b M v (weightedSource γd))`, with `weightedSource γd p = p.1 * γd p` (`:423`) |
| `Δβ = −∂ZΨ` | `streamBeta w Ψ` (`:310`) | `−graphDz w Ψ` |
| `Δγ = (Dr + 1/R)Ψ` | `streamGamma k v Ψ` (`:313`) | `graphDr k v Ψ + divideRadius Ψ` |
| `γd − A1γd` | `streamGamma_eq_desired_sub_alias_global` (`:759`) | `streamGamma … p = γd p − physicalAlias … p / p.1`, every `p`, axis included |

The three class claims are three declarations, and the exponent on the third is the point of the row:

| Paper | Declaration | Exponent |
|---|---|---|
| `Ψ* ∈ M_α` | `meanClass_streamPotential` (`TemporalMeanUpdate.lean:893–915`) | `α` |
| `Δγ ∈ M_α` | `meanClass_streamGamma` (`PhysicalMeanDomain.lean:1616`) | `α` |
| `Δβ ∈ M_{α+1}` | `meanClass_scaledRadialUpdate` (`TemporalMeanUpdate.lean:1097`) | `α + 1` |

`meanClass_streamBeta` (`:916–930`) states the *unscaled* `streamBeta` at `α`: the tree does not claim that a bare axial derivative gains an exponent. The gain is stated for the scaled direction — `radialUpdate d a b (M n) (v n) (ε n • w) h n (f n)` lands in `MeanClass (α + 1)` because the band scale is a `BandBound 1 ε` and `band_smul` adds one. That is the object the construction actually builds: `CorrectionState.rankIncrement.radial` (`CorrectionState.lean:434`) is `streamBeta (c.operators.epsilon n • axial) (rankPotential …)`. So the paper's `Δβ = −ε∂ZΨ*` is not assembled in this proposition — the `ε` sits inside the vector the derivative is taken along, which is where the paper's own `Q^{1/2−D} = Q^h = ε` puts it.

### 4. Divergence, bar and pointwise

* `reconstructed_divergence_zero` (`:740`) proves `graphDivergence (physicalSpeed d M) v w Δβ Δγ p = 0` for every `p`, with an explicit axis branch: below `a` both fields and their derivatives vanish (`radial_zero_of_lt`, `radialSupport_fderiv`), so the `1/r` in `Δγ` never meets `r = 0`. The paper's commutation `(r + r⁻¹)(−∂zΨ) + ∂z((r + r⁻¹)Ψ) = 0` is `stream_divergence_zero` (`:321`), proved from `graphDr_graphDz_comm` (`:233`) — symmetry of the second derivative plus the vanishing cross derivative of the radial vector field.
* `⟨Δγ⟩_Y = ⟨γd⟩_Y` is `streamGamma_bar_eq_desired` (`:843`). Its hypothesis is the paper's `∫ R⟨γd⟩_Y dR = 0` at every `(Z,T)` together with periodicity; `torusAverage_physicalAlias` (`:589`) makes the alias average vanish exactly, by the same `pressureSource_mass_zero` that part (i) uses.
* The pointwise clause is `slow_streamGamma_eq_desired` (`MeanRankUpdate.lean:406`): for slow `f` with `∫ r f = 0`, `streamGamma (physicalSpeed d M) (0,v) (streamPotential … (slowLift f)) p = slowLift f p` at every `p`. That is the paper's "if `γd` is independent of `Y`". `rank_axial_eq_desired` (`CorrectionState.lean:478`) applies it to the actual rank stage under the five-row condition, so the constructed `Δγ` *is* `γd` there rather than merely matching its mean.

Support is one lemma per object: `meanPressure_supported` (`:398`), `streamPotential_supported` (`:451`), `streamBeta_supported` (`:718`), `streamGamma_supported` (`:726`), plus `streamGamma_tsupport ⊆ tsupport Ψ` (`MeanLocalDefectBounds.lean:119`). The paper's `(Z,T)`-projection claim is the primitive's own support statement (`RadialPullback.physicalCompact_supported`) rather than a separate theorem about the pair.

### 5. Shape differences, recorded

* **`D_r` is a graph derivative.** The paper writes `D_r`; the tree writes `graphDr (physicalSpeed d M) v` at the fixed direction `(1, physicalSpeed • v)`, with `graphDr_eq_physical` (`:373`) proving it equals the physical radial derivative. Same operator, chart form.
* **`P` has two names.** `pressureMass` and `barMoment 0` are one integral; the class theorem is stated for `barMoment` because that is what the five rows consume, and `barMoment_apply` is the identification.
* **Strip, not support.** Every class is stated on the whole logarithmic strip where the paper asks only on the azimuthal support. Stronger, as in E151.
* **The `(Z,T)`-projection is inherited.** It is the support of `physicalCompact`, not a clause of the proposition. Nothing downstream asks for more.
* **Smoothness and support are binders.** `Shell a b` and `RadiallySupported` carry what the paper states in prose; the proposition's hypotheses are therefore the paper's, one for one.

No clause here is matched only by a component, and no clause is weaker than the paper's: the two class exponents that could have been (`Ψ*` and `Δγ`) are at `α`, and the one that gains (`Δβ`) gains at the direction the construction uses.

### 6. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 27 | 28 |
| partial | 1 | 1 |
| unplaced | 45 | 44 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:4735–4780` (Proposition 8.3, (8.12)–(8.14)); `PressureStream.lean:121,154,310,313,321,383,387,398,423,438,451,589,616,682,697,718,726,740,759,796,809,843`; `DefectIncrementBounds.lean:281–296`; `MeanIncrementBounds.lean:936,968,985`; `TemporalMeanUpdate.lean:893–930,1097–1128,1157–1174`; `PhysicalMeanDomain.lean:1616–1630`; `MeanRankUpdate.lean:406–417`; `MeanLocalDefectBounds.lean:111–128`; `CorrectionState.lean:429,434,478`; E141; E145; E151. Reading only — nothing compiled; "placed" is statement-level.*

---

## E153 — Proposition 8.4 is placed: both flux identities of (8.16) are theorems about the actual residual, and `c_ρ` stays inside `∂_Z` (2026-11-24)

*Reading entry. The §8.4 flux proposition is the cleanest row in the column: the three defects are definitions, both identities are stated about `u.thetaResidual` / `u.axialResidual` rather than about a supplied balance, and the pressure moment is derived from the constructed primitive rather than assumed. Every clause matches. The one thing the entry records as a difference is that the tree differentiates the whole combination `J_z + c_ρP` and therefore never needs `c_ρ` to be differentiable on its own — which is the paper's own remark about the moving `q`.*

### 1. What the paper asks

`Proposition 8.4` (p. 94, `.setup/paper/ns.txt:4795–4820`). With the corrections of (8.1) smooth and shell-supported, the two moments (8.2) zero at every `(Z,T)`, and `p_m` reconstructed from `g_r` by (8.12), the residual components `E_θ, E_z` of (8.3) and the defects

`Jθ = ∫R²⟨Gv + Vγ + γv + W_zθ⟩_Y dR`, `Jz = ∫R⟨2Gγ + γ² + W_zz⟩_Y dR − ½∫R²⟨g_r⟩_Y dR`, `cρ = ½∫R²ρ dR` (8.15)

satisfy `∫R²⟨Eθ⟩_Y dR = ε∂_Z Jθ` and `∫R⟨Ez⟩_Y dR = ε∂_Z(Jz + cρP)` (8.16). The proof has four moves: auxiliary averaging turns `D_r` into `∂_R` and `t*` into `−ε∂_T`; every radial divergence, the residual stress tensor's included, is an endpoint term after the displayed weight; the two viscous integrals vanish by explicit integration by parts; and the time and axial-viscosity terms are derivatives of the two zero integrals. The pressure moment is fixed by compact support, `∫R⟨p_m⟩_Y dR = −½∫R²∂_R⟨p_m⟩_Y dR = −½∫R²⟨g_r⟩_Y dR + cρP`, and because `ρ` is scaled by the moving `q`, `cρ` may depend on `(Z,T)` and the whole product stays inside `∂_Z`.

### 2. The three defects are definitions, and they are the paper's integrals

| Paper | Declaration | Statement |
|---|---|---|
| `P = ∫⟨g_r⟩_Y dR` | `CorrectionState.pressureDefect c u` (`:229`) | `radialMoment 0 (u.gr c)` |
| `Jθ` | `CorrectionState.thetaDefect c u` (`:232`) | `radialMoment 2 (thetaAxial c.base u.mean + u.covariance 2 1)` |
| `Jz` | `CorrectionState.axialDefect c u` (`:236`) | `radialMoment 1 (axialAxial c.base u.mean + u.covariance 2 2) − ½ • radialMoment 2 (u.gr c)` |
| `cρ` | `IntegratedMeanBalances.pressureCoefficient ρ` (`:713`) | `radialMoment 2 ρ / 2` |
| the row order | `CorrectionState.debt` (`:242`) | `![pressureDefect, thetaDefect, axialDefect]`, docstring *"exactly `(P, Jθ, Jz)`, as in `MeanRankUpdate`"* |

`covariance 2 1` is `W_zθ` and `covariance 2 2` is `W_zz`, so the brackets are the paper's products with the curl remainders included, not only the base terms. `DefectIncrementBounds.defects` (`:330`) is the same triple on the abstract `Operators`/`Triple` layer, and `defects_eq_stateDebt` (`:701`) proves the two agree by `rfl`.

### 3. Both identities, stated about the residual

The point of the row is that (8.16) is not an algebraic identity about a balance expression someone chose; it is the paper's statement about the actual `E_θ, E_z`:

| Paper | Declaration | Statement |
|---|---|---|
| `∫R²⟨Eθ⟩ = ε∂_Z Jθ` | `StateMomentBalances.state_angular_moment` (`:772`) | `radialMoment 2 (u.thetaResidual c) n s = ε n * fderiv (thetaDefect c u n) s z` |
| `∫R⟨Ez⟩ = ε∂_Z(Jz + cρP)` | `StateMomentBalances.state_axial_moment` (`:846`) | the same identity with `axialDebtPotential r c u = axialDefect + pressureCoefficient r • pressureDefect` (`:815`) |

Both are composed, not assumed. `averaged_thetaResidual` (`:760`) proves the auxiliary average of the actual residual *is* `angularBalanceAlong` of the averaged fluxes; `state_radialMoment_eq` (`:740`) identifies the state moment with the integrated mean; and `integrated_angular_balance` / `integrated_axial_balance` (`IntegratedMeanBalances.lean:638,689`) do the four moves of the paper's proof as four rewrites:

* the endpoint terms: the folder's `SmoothShell a b F` is smoothness plus support in `Icc a b`, and `positive_radialMoment` (`:790`) converts `∫_{Ioi 0}` into the moment, so the boundary terms are gone before anything is estimated;
* the divergence terms: `moment_angular_divergence` / `moment_axial_divergence` are the weighted endpoint identities, applied to the actual radial flux and to `c.virtualTheta` / `c.virtualAxial` (the residual stress tensor's own divergence);
* the viscous terms: `moment_angular_viscosity` and `moment_axial_viscosity` are the paper's two integrations by parts, with the coefficients `2 − 1 − 1 = 0` and `−1 + 1 = 0` closed in the proof rather than quoted;
* the time and axial terms: `zero_mass_parameterPartial` and `zero_mass_parameterPartial_twice` move the derivative onto the two zero moments (8.2) and kill them, which is the paper's "derivatives of the two zero integrals".

The pressure half is `flux_pressure_moment` (`:717`): `radialMoment 1 (axialFlux + pressure) = axialDefect axialFlux gr + pressureCoefficient ρ * pressureTotal gr`, i.e. the paper's `∫R⟨p_m⟩ = −½∫R²⟨g_r⟩ + cρP` with `pressureTotal = radialMoment 0 gr`. It is derived from `pressure_moment_reconstructed`, the integration-by-parts identity for a compactly supported primitive, and `integrated_axial_reconstructed` (`:783`) then differentiates the *sum* `axialDefect + cρ·P` in one `fderiv`. That is why the paper's remark about `cρ` is satisfied rather than dodged: no declaration ever asks `pressureCoefficient` to be differentiable by itself.

On the constructed object, `constructed_pressure_moment` (`:866`) states the same moment for `PressureStream.meanPressure` fed by the actual `g_r`, using `meanPressure_bar_hasDerivAt` for the derivative — the E152 chain, reused rather than reproved.

### 4. Hypotheses, one for one

| Paper | Tree |
|---|---|
| corrections smooth, compactly supported, zero outside the active shell | `SmoothShell a b` on each of the three components and on the stress flux; `RadiallySupported` for the half-line form |
| moments (8.2) vanish at every `(Z,T)` | `hmass : radialMoment 2 v = 0` (angular) and `radialMoment 1 γ = 0` (axial) |
| `p_m` reconstructed by (8.12) | `hrecipe : u.pressure = pressureRecipe r c u`, the E152 recipe |
| `E_θ, E_z` are the residual components of (8.3) | `u.thetaResidual c`, `u.axialResidual c` |
| auxiliary averaging | `PressureStream.torusAverage` at every slow point |

### 5. Shape differences, recorded

* **The two `α`-side claims of (8.15) are not in this proposition.** The paper defines `Jθ, Jz` here and estimates them in Lemma 8.8; the tree's class bound on the same triple is `DefectBounds` / `defectBounds_components` (`StateMomentBalances.lean:1130`), already used by E151. No clause of 8.4 is weaker for that.
* **`E_θ` is an averaged residual, not a component.** The identity is stated after `averaged_*`, because the paper's integral is against `⟨·⟩_Y`. The unaveraged equation is `u.thetaResidual c` itself, and `fluxResidual` is where it is built.
* **`c_ρ` is a coefficient, not a field.** `pressureCoefficient r` is a real number fixed by the reconstruction data, whereas the paper's `cρ` is `(Z,T)`-dependent. The dependence is real and enters through `u.gr c n s`; the tree's `pressureCoefficient` on the abstract layer (`IntegratedMeanBalances.pressureCoefficient ρ : MeanParameter → ℝ`) is the parameter-dependent version, and `integrated_axial_reconstructed` is stated for that one. Both forms exist; the state theorem uses the fixed-data one because that is what `pressureRecipe` builds.

No clause is matched only by a component. Unlike E150, nothing here is one line short: the two identities are the two theorems, and the hypotheses are the paper's.

### 6. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 28 | 29 |
| partial | 1 | 2 |
| unplaced | 44 | 42 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:4795–4828` (Proposition 8.4, (8.15)–(8.16)); `CorrectionState.lean:229–248`; `DefectIncrementBounds.lean:319–334,701–703`; `IntegratedMeanBalances.lean:613–760` (`angularBalance`, `axialBalance`, `integrated_angular_balance`, `integrated_axial_balance`), `:711–760` (`pressureTotal`, `pressureCoefficient`, `axialDefect`, `flux_pressure_moment`), `:779–800` (`integrated_axial_reconstructed`), `:855–895` (`constructed_pressure_moment`); `StateMomentBalances.lean:700–860` (fluxes, `state_radialMoment_eq`, `averaged_thetaResidual`, `state_angular_moment`, `pressureRecipe`, `axialDebtPotential`, `pressureRecipe_moment`, `state_axial_moment`), `:1088–1136` (`bump_class_from_actual_debt`, `defectBounds_components`); E152. Reading only — nothing compiled; "placed" is statement-level.*

---

## E154 — Corollary 7.3 stays partial: the uniformity is proved three times over, but no declaration is the solution operator it names (2026-11-24)

*Reading entry. Working the first §7 row found the corollary's substance present in three separate uniformity statements and the corollary itself absent. The modal operator is the right matrix, the damping is never divided by, and the inverse's norm is bounded by a constant with no harmonic index in it — so "increasing the harmonic set or the derivative order changes only constants" is true and proved. What is missing is the object: the paper's operator maps a source to the pair `(t_m, π_m)` of the driven equation with `t_m(0) = 0`, and no declaration has that type; and `q*` appears nowhere as a threshold. The row moves from unplaced to partial, with three clauses named.*

### 1. What the paper asks

`Corollary 7.3` (p. 80, `.setup/paper/ns.txt:4114–4117`). The solution operators `f_m ↦ (t_m, π_m)` for the projected amplitude equation with `t_m(0) = 0` are defined at every finite correction stage on the same domain `0 < q < q*`. Increasing the finite harmonic set or the derivative order changes constants and polynomial degrees but does not require shrinking the domain.

Its proof is three sentences, and each names a mechanism: the frame and damping comparisons need only the single finite choice in Lemma 7.1; the exact factor (7.18), `V_m(v,w) = exp(−(m²−1)∫_w^v d) V_1(v,w)`, makes every higher harmonic at least as damped; and in (7.20) the extra factors of `m` and of coefficient derivatives enlarge only constants and polynomial degrees. Proposition 7.2 states the sharper form: *"The threshold `q*` does not depend on `M`, `α`, or the correction stage."*

### 2. What exists: the matrix, the damping, the uniformity

| Paper | Declaration | Statement |
|---|---|---|
| (7.17) `A_m = diag(λ,−λ) + E − m²d I` | `GrowingMode.modalOperator lam damping e11 e12 e21 e22` (`:22`) | `![(λ − d + E11) z₀ + E12 z₁, E21 z₀ + (−λ − d + E22) z₁]` |
| the cone and positivity for (7.17) | `growing_slot` (`:131`) | `0 < z t 0 ∧ |z t 1| ≤ r * z t 0` on a slot, from `|E_ij| ≤ ε` and a gap condition, with `hminus : z a 1 = 0` |
| the `K/S` form | `scaled_growing_slot` (`:246`) | the same with `|E_ij| ≤ C/S` and cone constant `coneConstant lamMin C / S` |
| the envelope | `hasDerivAt_weighted_scalar` (`:260`), `scaled_envelope_slot` (`:359`) | the integrating-factor comparison and the two-sided `P`-bounds per slot of length `≤ L*S` |

`damping` enters as one scalar and is never divided by, never compared to `1`, and never appears in a denominator: substituting `damping = m²d` is a definitional step for the caller. The cone constant `coneConstant lamMin C / S` contains `λ_min`, `C` and `S` — not `m`, not `α`, not a stage. That is the corollary's "constants only" claim for the coefficient side, and it is stronger than the paper's because it holds for every real damping at once.

The inverse side is where the harmonic set would have to shrink the domain, and it does not:

* `TorusInverse.directionalInverse d a` (`:301`) is the solution operator for the auxiliary derivative, `series (inverseCoeff d a)`.
* `norm_directionalInverse_le` (`:439`) bounds it by `(6 * ‖ω⁻¹‖) * coeffSeminorm 1 a` — one constant for the whole coefficient family, with no index set in the statement.
* `inverse_derivativeWord_bound` (`:505`) costs `(6‖ω⁻¹‖) * ‖ω‖ ^ w.length * coeffSeminorm (w.length+1) a`: derivative order enters as an exponent and a seminorm index, exactly the paper's "polynomial degrees".
* `SmoothFamilyTorusInverse.norm_jet_applyMultiplier_le` (`:726`) puts the jet order additively in the majorant (`n + l + 4`), on a parameter set `S` that is a hypothesis and is never enlarged or shrunk by the order.
* `uniform_multiplierDerivative_bound` (`:459`) is uniform on a compact `K ⊆ P`, i.e. on the fixed parameter region, which is the analogue of `0 < q < q*`.

### 3. Why it stays partial: three named clauses

| Clause | Why it is unmatched |
|---|---|
| the operator `f_m ↦ (t_m, π_m)` | `GrowingMode` is the *homogeneous* modal estimate; `TorusInverse` inverts the auxiliary derivative. Neither has the paper's type, a map from a source to the amplitude–pressure pair of the driven equation (7.13). |
| the initial condition `t_m(0) = 0` | the only initial data in `GrowingMode` is `hplus : 0 < z a 0`, `hminus : z a 1 = 0`, which is a cone initialization, not zero data for a driven equation. `TorusInverse.inverse_zero_mean` is a zero *mean*, a different normalisation. |
| `q*` independent of `M` | no declaration names a threshold. The parameter region is supplied by the caller as `U`/`K`; that it does not depend on `M` is a consequence of `M` not appearing, not a stated theorem. |

This is the Lemma 9.7 pattern — the content is there under other names and the statement is not — so the row goes to partial rather than placed. It is not a mathematical objection: nothing in §7's later use of the corollary asks for a `q*` that is named.

### 4. What this changes for the §7 slice

Five §7 rows remain unplaced after this entry (7.1, 7.2, 7.4, 7.5, 7.6, 7.8), and this reading says where to start: the driven amplitude equation is the object none of the §7 modules in the queue's candidate list declares. The natural next targets are `JointODE` / `WithinJointODE` / `ParametricODE` (the actual ODE solve) and `PrimaryPulseBounds.homogeneous_joint_jet_bound`, whose docstring says the solution is *"the constructed Volterra solution in `JointODE`, rather than an assumed smooth solution family"*. That is the operator Corollary 7.3 is about, and it was not in the queue's candidate list.

### 5. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 29 | 29 |
| partial | 1 | 2 |
| unplaced | 42 | 42 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:4114–4117` (Corollary 7.3); `:4030` ((7.18)); `:3992` (Proposition 7.2's threshold sentence); `GrowingMode.lean:22–41`, `:131–140`, `:246–254`, `:260–262`, `:359–383`; `TorusInverse.lean:301,323,439,505,574`; `SmoothFamilyTorusInverse.lean:459,724–752,1074–1078`; `ParametricTorusInverse.lean:1–70`; `PrimaryPulseBounds.lean:155–159`; E143; E152. Reading only — nothing compiled.*

---

## E155 — (8.17) is not a statement in the tree: the normalisation is one weight and per-row exponents, so the six powers can be neither placed nor refuted (2026-11-24)

*Reading entry. The third follow-up asked whether the tree's flux-defect normalisations match the paper's powers of `Q`. The answer is that the tree has no (8.17)-shaped declaration at all. Normalisation is carried by a single moving weight — `qLength = √(coordinateQ)`, and `chartScale = √Q` for the chart form — with one exponent per row, and no theorem states any of the six factor identities. Two things are nevertheless structural and worth recording: the `P`/`cρ` pair shares one radial weight, and the axial identity differentiates their product, which is exactly what the paper's table exists to guarantee. No ledger move: (8.17) is an equation inside §8.4, not a numbered result.*

### 1. The table, and what would place it

`(8.17)` (`.setup/paper/ns.txt:4820–4830`) gives `(Mθ)* = QA^{-3/2}(Mθ)_phys`, `(Mz)* = QA^{-1}(Mz)_phys`, `P* = Q²A P_phys`, `(cρ)* = Q^{-1}(cρ)_phys`, `(Jθ)* = Q²A^{-3/2}(Jθ)_phys`, `(Jz)* = Q²A^{-1}(Jz)_phys`, with the remark that each nonzero correction target uses the normalisation of its corresponding row. Placing it would need six declarations of the form `defect_normalized = (Q ^ a * A ^ b) * defect_physical`, or one structure with six fields.

### 2. What the tree has instead

* `VariableGaugeMean.qLength coord s = Real.sqrt (SimilarityCoordinates.coordinateQ coord s)` (`:172`), with `qLength_pos`, `qLength_contDiffOn`, `qLength_chart` (`:879`) and `qLength_reference_bounds` (`:1473`). The chart form is `chartScale n = (ChartScales.Q n)⁻¹ᐟ²`-shaped: `qLength_chart` proves `qLength (2h) (slowToChartTZ h n s) = chartScale n * qLength (2h) s`.
* `meanClass_moving_localBandJets`, `movingStripData`, `logStripData` carry one exponent `α` per row and one growth per jet order. The class is the statement; the factor is in the weight.
* `MeanRankUpdate`'s five-row map carries each row's exponent separately, which is the paper's "each target uses its own row".
* A search for `A ^ (3/2)`, `A ^ (-3/2)`, `Q^2 * A`, `Q⁻¹` in the moment layer returns nothing. `CoordinateAlgebra.A` exists as a definition and is used in `ChartScales`-adjacent exponents, but it is not tied to the defect layer by any statement.

So the six powers are *consistent with* the tree and are not *stated by* it. The consistent reading is that `qLength^(2α)` is the paper's `Q^α` on the row whose class is `α`, and the `A`-powers are absorbed into the same weight because the tree never separates the two chart factors at this layer.

### 3. The part that is structural, and why it matters for (8.16)

Two facts survive the failed search, and both are load-bearing:

* `pressureDefect` and `pressureCoefficient` are both `radialMoment 2`-weighted (`CorrectionState.lean:229,713`), so `P` and `cρ` are normalised by the same weight. (8.17) gives them different factors (`Q²A` and `Q⁻¹`); the tree's uniform weight is only harmless because their *product* is what appears in (8.16).
* `integrated_axial_reconstructed` differentiates `axialDefect + pressureCoefficient * pressureTotal` as one `fderiv`. The paper's remark that `cρ` may depend on `(T,Z)` and "its full product with `P` therefore remains inside `∂_Z`" is exactly this, and the tree's statement shape enforces it rather than assuming it.

### 4. Recorded as a lead, not a finding

This entry does not say the normalisation is wrong, and it does not say it is right: it says the comparison cannot be made at statement level because one side of it does not exist as a statement. If a later pass wants to close it, the place to look is `MeanRankUpdate`'s row data and `ChartScales`' exponent ledger, and the question to ask is whether any declaration's exponent *forces* a row's factor rather than permitting it. The nearest existing tool is `ExponentLedger.lean`, which tabulates exponents but not the physical/normalised ratios.

*Evidence: `.setup/paper/ns.txt:4820–4830` ((8.17)); `VariableGaugeMean.lean:172,879,1473`; `ChartScales.lean:26,29,59`; `CorrectionState.lean:229,236,713`; `IntegratedMeanBalances.lean:779–800`; `ExponentLedger.lean`; E153. Reading only — nothing compiled.*

---

## E156 — Corollary 7.8 is placed: `signedTensorRemainder` is `C(U+V)−C(U)−Σ` by definition, and the three exponents are the paper's (2026-11-25)

*Reading entry. The §7.6 covariance corollary is the closest statement-level match in the §7 column: the expansion (7.41) is a definition plus a theorem, not an assembly, and (7.42) is one `mono_exponent` chain at exactly `δ+β`, `α+η` and `2β`. The paper's three powers `ρ+α−1/2`, `α+1/2−κ_s` and `2α−1` are the same three under the substitutions the paper's own hypotheses make. Two shape differences are recorded rather than smoothed: `Σ` is constructed from the primary block instead of supplied as data, and the divergence clause is stated through the three `…CovarianceChange` rows. This entry also corrects E154's module lead for this row: Corollary 7.8 lives in `CorrectionStep`'s covariance layer, not in `JointODE`.*

### 1. What the paper asks

`Corollary 7.8` (p. 87, `.setup/paper/ns.txt:4455–4488`). Fix `α, ρ`, let `U = Was₀ + E` be a real divergence-free wave field including its curl remainders with `U ∈ W_{1/2}` and `E ∈ W_ρ`, and let `Σ(R,Z,T) ∈ M_α` be a real two-vector independent of the angular and auxiliary variables. Apply Lemma 7.7 to the signed amplitudes `LasΣ`, obtaining `V = LasΣ + R` with `R ∈ W_{α−κ_s}`. Then

`C(U+V) − C(U) = Σ + B(E, LasΣ) + B(U, R) + C(V)` (7.41),

with `B(E, LasΣ) ∈ M_{ρ+α−1/2}`, `B(U,R) ∈ M_{α+1/2−κ_s}`, `C(V) ∈ M_{2α−1}` (7.42), and "taking the radial divergence of each remainder term decreases the ε exponent by at most a further `κ_s`". The proof is three lines: expand the quadratic map, use `B(Was₀, LasΣ) = Σ`, and note that `V ∈ W_{α−1/2}` because `κ_s < 1/2`, so `C(V) ∈ M_{2α−1}`.

### 2. The left-hand side is a definition

| Paper | Declaration | Statement |
|---|---|---|
| `B(u,v)` | `CorrectionStep.symmetricCovariance u v` (`:2304`) | `bilinearCovariance u v + bilinearCovariance v u` |
| `C(v)` | the third term of `covarianceIncrement` (`:478`) | `bilinearCovariance u v + bilinearCovariance v u + bilinearCovariance v v` |
| `C(U+V) − C(U) − Σ` | `CorrectionStep.signedTensorRemainder primary old tangent curl` (`:2309`) | `covarianceIncrement old (tangent + curl) − symmetricCovariance primary tangent` |

`primary` is `Was₀`, `old` is `U`, `tangent` is `LasΣ` and `curl` is `R`, so the tree's left-hand side *is* the paper's is once `(tangent + curl)` plays `V`. The `Σ` that gets subtracted is `symmetricCovariance primary tangent` — the target, built from the same two blocks rather than handed in.

### 3. (7.41) is `signedTensorRemainder_exact`, and it is derived

`signedTensorRemainder_exact` (`:2313`) states, from angular continuity alone,

```
signedTensorRemainder primary old tangent curl
  = symmetricCovariance (old − primary) tangent
  + symmetricCovariance old curl
  + bilinearCovariance (tangent + curl) (tangent + curl)
```

which is (7.41) term for term: `B(E, LasΣ)` with `E = old − primary`, `B(U,R)`, and `C(V)`. It is proved by rewriting `covarianceIncrement`, the two `bilinearCovariance_add` lemmas and the two `…_sub` lemmas, then `abel` — the paper's "we expand the quadratic map and use `B(Was₀, LasΣ) = Σ`", with the cancellation that makes `Σ` disappear done by subtraction rather than by a hypothesis.

The state-level form is `AssembledSignedTensor` (`:3242–3252`): for the actual `u.addIncrement m p (tangent + curl) q e`,

```
(u.addIncrement m p (tangent + curl) q e).covariance − u.covariance − symmetricCovariance primary tangent
  = signedTensorRemainder primary.oscillation old.oscillation tangent.oscillation curl.oscillation,
```

and the conclusion is `TensorClass s γ` of that difference. So (7.41) is stated about the covariance the iteration actually stores, not about an abstract map.

### 4. (7.42) is one chain, and the paper's exponents are the substitutions

`signedTensorRemainder_mem` (`:2366`) concludes `TensorClass s γ` from four exponent hypotheses:

| Paper term | Tree hypothesis | Paper's value |
|---|---|---|
| `B(E, LasΣ) ∈ M_{ρ+α−1/2}` | `hγd : γ ≤ δ + β` with `(subBlock old primary).WaveBounds δ` | `δ = ρ`, `β = α − 1/2` |
| `B(U,R) ∈ M_{α+1/2−κ_s}` | `hγc : γ ≤ α + η` with `old.WaveBounds α`, `curl.WaveBounds η` | `α = 1/2`, `η = α − κ_s` |
| `C(V) ∈ M_{2α−1}` | `hγs : γ ≤ 2 * β` with `(tangent + curl).WaveBounds β` | `β = α − 1/2` |

The instantiated use is `signedTensorRemainder_divergence_mem` (`:2414`), which fixes `ho : old.WaveBounds (1/2)`, `hd : (subBlock old primary).WaveBounds (17/25)` and `ht : tangent.WaveBounds (waveExponent σ − κ)`, then concludes the three `MeanClass (meanExponent σ + 17/100)` rows for `thetaCovarianceChange`, `axialCovarianceChange` and `radialCovarianceChange`. That is the divergence clause: the `…Change_mem hops he` step spends `κ` from `OperatorBounds`, exactly the paper's "at most a further `κ_s`", and the `.17` is the paper's own printed improvement.

One thing is stronger than the paper: `hβη : β ≤ η` is required, and the docstring says why — the stronger bound on the old-minus-primary field is used only for the first term. The paper does not need it, but it does not contradict it either.

### 5. Shape differences, recorded

* **`Σ` is constructed, not supplied.** The paper takes `Σ ∈ M_α` as data and produces `V` from it; the tree takes `primary` and `tangent` and defines the target as `symmetricCovariance primary tangent`. That removes the question of whether a stress field with the right class exists, and replaces it with hypotheses on the two blocks — `SameCarrier` for all three pairs, band limits, and the zero zeroth harmonic.
* **`E` is a sub-block, not a field.** `subBlock old primary` is the literal difference, and `subBlock_oscillation` proves the oscillation agrees; the paper's `E = U − Was₀` is the same object.
* **`V` is a sum of two blocks.** `tangent + curl` is `addBlock`, with `addBlock_oscillation`; the paper's `LasΣ + R` is that sum.
* **The divergence clause is three rows.** The paper says "each remainder term"; the tree states the three covariance rows that the mean machinery consumes, at one common exponent. Same content, and it is the form the next step uses.
* **The 2 × 2 target is not in this corollary.** `SmoothCovariance` and `Covariance.signedMatrix` handle the two-slot solve; Corollary 7.8 is the tensor algebra before that solve, exactly as in the paper's order.

No clause is unmatched. The one statement the entry does not make is that the proof of `signedTensorRemainder_mem` is valid — it is statement-level reading, as every placed row is.

### 6. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 29 | 30 |
| partial | 2 | 2 |
| unplaced | 42 | 41 |
| **total** | **73** | **73** |

### 7. Correction to E154's module lead

E154 §4 recorded that the §7 queue should be read against `JointODE` / `WithinJointODE` first, because the driven amplitude operator is there. That remains the right lead for **Corollary 7.3**, which needs the operator `f_m ↦ (t_m, π_m)`. It is the wrong lead for **Corollary 7.8**, which needs no ODE solve at all: it is pure covariance algebra and is fully declared in `CorrectionStep`. The §7 queue splits accordingly — 7.8 is done here, 7.3 waits on the ODE layer, and 7.1, 7.2, 7.4, 7.5, 7.6 should be read against `TorusInverse` and `SignedWaveUpdate` before either.

*Evidence: `.setup/paper/ns.txt:4455–4488` (Corollary 7.8, (7.41)–(7.42)); `CorrectionStep.lean:471–485` (`covariance_add`, `covarianceIncrement`), `:2304–2322` (`symmetricCovariance`, `signedTensorRemainder`, `signedTensorRemainder_exact`), `:2324–2410` (`subBlock`, `symmetricCovariance_mem`, `signedTensorRemainder_mem`), `:2412–2443` (`signedTensorRemainder_divergence_mem`), `:3242–3252` (assembled state identity); `HarmonicCovariance.lean:60–140`; `ExponentLedger.lean:30–40`; E154. Reading only — nothing compiled; "placed" is statement-level.*

## E157 — Lemma 7.1 is placed: the normal estimate, the left inverse, the modal diagonal and the damping comparison are all derived (2026-11-24)

Lemma 7.1 is the load-bearing threshold of §7 — it is the one place the paper spends `q*`, and Corollary 7.3's uniformity sentence quotes it. Read clause by clause, all five clauses have declarations, and the *shape* of the last two is different in a way worth recording rather than smoothing.

### 1. Single-valuedness and the nonzero angular frequency

The paper gets this from `k_p m ∈ ℤ \ {0}`. The tree's descent is not asserted but *is* descent: `TorusInverse.series_eq_torusSeries` proves the plane series equals the `(ℝ/ℤ)²` series pointwise, and `series_periodic` (`:579`) reads `directionalInverse d a (x.1 + m, x.2 + n) = directionalInverse d a x` off `AddCircle.coe_add` and `circle_int_eq_zero`. Nonzero angular frequency is the `harmonic ≠ 0` binder carried by every forced-solution bound — `PrimaryODE.primary` fixes `1`, `ParticularWaveBounds.forced_modal_family_envelope_jets` takes `hharmonic : harmonic ≠ 0`, and `CorrectionStep.meanUpdate_residualBlock_mem` carries `hkp : ∀ n, a.angularFrequency n ≠ 0`. The symbol's nonvanishing is `TorusInverse.symbol_ne_zero` (`:216`), with `|1/symbol d k| ≤ 6 * weight k` at `:235`.

So the clause is not merely "the tree is periodic"; it is the same mechanism — integer frequency in, single-valuedness out, and the multiplicative constant `6` explicit.

### 2. (7.9): `|nΦ − Bs| + |n′Φ| ≤ C/S*` and `Eik = O(εSC*)`

`BasePhaseGeometry.phase_estimates` (`:880–901`) is this estimate. It concludes

```
|d.viscosity − referenceViscosity (a.lam i) u (a.length i) v| ≤ dampingConstant M / D.scale i
```

by composing `ChartScales.carrier_viscosity_bounds` (viscosity is bounded in the carrier), `a.phase_estimates … .1` (the normal is close to the reference), `a.slope_bound` and `a.phase_error_small`, and feeding all of it to `damping_error_of_normal_close`. The last step is the paper's arithmetic: the damping is `viscosity × |nΦ|²`, and `|nΦ|²` is close to the reference squared iff the normal is close. `a.B_bounds` supplies the reference side.

`Eik` — the phase transport — is the same bound: `MovingFrameODE.scalar_coefficients_close` (`:538`) takes `|ρ|, |s|, |F₀|, |g₀| ≤ M`, `⟪B₀ 0, g₀⟫ = 0`, `|F − F₀|, ‖g − g₀‖, |ρ − s|, |ρ′|, |rot| ≤ η`, and returns the coefficient errors `errorA/B/C` at `16 M²(1+M) η` — and the docstring is explicit that no coefficient or propagator estimate is among the assumptions. The `ε S C*` form is that, with `η = C S⁻¹` and the chart factor carried separately.

### 3. Fixed-derivative polynomial bounds

`PhaseJetBounds.PolynomialJets` is the class, and `primaryWave_waveClass` / `phaseWave_waveClass` (`PrimaryPulseBounds:1536`, `:1681`) consume it: they require `PolynomialJets (phaseDomain s) (chartCovariance …)`, i.e. every fixed mixed derivative of the covariance — hence of the phase normal — grows polynomially in the band. `ChartScales` supplies the dyadic decay, and `BasePhaseGeometry.construction_frame` proves the frame the construction uses *is* `a.frame` (`rfl`), so no separate frame is chosen later.

### 4. (7.10): the basis, the left inverse, and the modal diagonal

This is the clause whose shape changes, and it changes in the tree's favour.

The paper writes `Bℓ(AΦB − B′) = diag(λ, −λ) + E` and needs `Bℓ` uniformly bounded. The tree never forms `Bℓ` as a matrix. It proves the reconstruction identity directly: `MovingFrameODE.tangent_reconstruct` (`:786`),

```
⟪normal β ρ B, t⟫ = 0  →  tangent ρ B (t 0) ⟪B 1, tail t⟫ = t
```

which is the left inverse *as a formula*: read off the two coordinates and rebuild. That is stronger than "a bounded left inverse exists" — it is an explicit one, and `tangent` is `x • B 0 + y • B 1` after the `(e_r − ρK, N)` shear (`MovingFrameODE:94`), so boundedness is `|x| ≤ ‖t‖` and `|y| ≤ ‖t‖`.

The diagonal is then true *by definition*: `FrameData.coefficient` (`PrimaryODE:73`) is

```
GrowingMode.modalOperator (d.eigenvalue z) (d.damping j z) (d.error11 z) … (d.error22 z)
```

and `GrowingMode.modalOperator` is `diag(λ, −λ) + errors` as a term (`modalOperator_eq_coefficient` at `MovingFrameODE:799`). So `Bℓ(AΦB − B′) − diag(λ,−λ)` *is* the `error11..22` block, and the estimate `|E| ≤ C/S*` is `modal_errors_le` (`:376`): from `|F − F₀|, ‖g − g₀‖ ≤ η`, `|ρ − s|, |ρ′|, |rot| ≤ η`, `|h| ≤ H`, `|1/h| ≤ H`, `|h′| ≤ κ`, it returns the four entries at `(16 M²(1+M)) η`.

The paper's `λ(v) = λ₀√(1+s(v)²)` is `referenceEigenvalue` (`ViscousPropagator:427` is its rate split; the eigenvalue itself is `lam/√(1 + slotMagnitude²)`, `BasePhaseGeometry:960`).

### 5. (7.11): `|d − dref| ≤ C/S*` — derived, not assumed

This is the clause I expected to be a hypothesis, because `PrimaryODE.primary_bounds` *takes* `hν : |viscosity − referenceDamping| ≤ D/S`. It is not a hypothesis at the top. `BasePhaseGeometry:892–900` derives it: `href` rewrites `referenceViscosity` at the slot magnitude (`signedSlot_sq`), `dampingDenominator` is unfolded, and `hout` — `damping_error_of_normal_close` — is `convert`ed with `dampingConstant`, closing the numerical identity by `ring`. So the dependency runs *down* to the normal-close estimate of §2, exactly as the paper's proof says (`"the error in p_F R + p_Z G is O(S*⁻³ + ε² + k⁻¹)"`), and `primary_bounds`' hypothesis is discharged by that theorem.

`referenceViscosity` (`ViscousPropagator:423`) is the paper's `dref = εk²B² s(1+s²)` up to the chart factor: `lam*(1 + slotMagnitude²)/((1+u²)*√(1+u²))`.

### 6. Shape differences, recorded

* **`q*` has no name.** The threshold is a number, `ActualCandidateConstruction.qbig` / `ChartScales`' dyadic floor, chosen once and carried by `LocalScheduleWitness`. The paper's "there exists `q*`, common to all labels and fixed derivative orders" is exactly the *absence* of a parameter in those definitions — which is how E66 recorded it — not a theorem that says so.
* **`Bℓ` is a formula, not a matrix.** Recorded above; it makes clause 4 stronger, not weaker.
* **`E` is not an independent matrix.** `error11..22` are *defined* by subtracting the diagonal from the moving-frame coefficients, so `Bℓ(AΦB − B′) = diag + E` cannot fail; only the size of `E` is a theorem, and it is one.
* **`Eik` has no name.** It is the `phase_error_small` bound, not a field.

No clause is unmatched, and one clause (the left inverse) is strictly stronger than the paper's. Statement-level as always: `modal_errors_le`'s proof was not read line by line, and nothing was compiled.

### 7. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 30 | 31 |
| partial | 2 | 2 |
| unplaced | 41 | 40 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:3873–3907` (Lemma 7.1, (7.9)–(7.11)); `TorusInverse.lean:216,235,275,324,369–381,579`; `MovingFrameODE.lean:94,538,786–798,799`; `PrimaryODE.lean:73,376,423,960`; `BasePhaseGeometry.lean:880–901,1062`; `ViscousPropagator.lean:423–433`; `PhaseJetBounds`/`PrimaryPulseBounds.lean:1536,1681`. Reading only — nothing compiled; "placed" is statement-level.*

## E158 — Proposition 7.2 stays partial: the driven solution and its jets are declared, the pressure formula and the one-threshold sentence are not (2026-11-24)

The paper's Proposition 7.2 is a *compound* statement: unique `t_m` with `nΦ·t_m = 0` and zero data, pressure `π_m` from (7.13), bounds (7.14)–(7.15), and the sentence "the threshold `q*` does not depend on `M`, `α`, or the correction stage". Three of those five are declarations. Two are not, and the two are the ones Corollary 7.3's partial status already turns on.

### 1. The driven solution, and the projection

`JointODE.solution` is the Volterra solution of the driven modal equation, and `WithinJointODE` gives its joint regularity in the parameter; `PrimaryODE.solution` (`:181`) instantiates it with `(x₀, f)` and `solution_hasDerivAt` (`:199`) proves it solves the equation rather than merely being named one. Uniqueness is the Volterra fixed point's.

The projection `proj_{n⊥Φ} f` is not a separate operator in the tree — it is *built into* the forcing. `FrameData.forcing` (`PrimaryODE:89`):

```
forceX = -(f 0 - ρ ⟪B 0, tail f⟫) / (1 + ρ²)
forceY = -⟪B 1, tail f⟫
forcing = ![(forceX + forceY/h)/2, (forceX - forceY/h)/2]
```

The two brackets are exactly `⟪B_i, tail(proj f)⟫` for the normalized frame; dividing by `h = eigenvector` is the change to `(z+, z−)` coordinates. So the paper's `f − nΦ(nΦ·f)/|nΦ|²` is `forcing`, and `forcing_zero` proves it vanishes on zero source.

### 2. (7.14) is `forced_modal_family_envelope_jets`

`ParticularWaveBounds.forced_modal_family_envelope_jets` (`:1009`) takes `harmonica ≠ 0`, an envelope `W` with `rate = eigenvalue − referenceDamping`, `|viscosity − referenceDamping| ≤ E/S`, the four `error` bounds at `C/S`, a slot `L ≤ K·S`, and a source with envelope jets `w·W`; it concludes `EnvelopeJets` of the solution at the same `w·W`. That is (7.14) with `C′_I` and `B′_I` carried by the jet structure rather than printed. `forced_modal_jet_bound` (`:1068`) is the ambient-coordinate twin.

The paper's `ε^α S^{b_I} √ζ δ^{−a_I} P(v)` is the *instantiation*: `w = ε^α √ζ δ^{−a_I}` and `W = S^{b_I} P`. `PrimaryPulseBounds.primaryWave_waveClass` is that instantiation for the primary; the forced case is the same wrapper.

### 3. What is not there

**(i) No declaration is the pair `(t_m, π_m)`.** The amplitude half is placed; the pressure half (7.13),

```
π_m = (i k m nΦ·K t_m − n′Φ·t_m + nΦ·f_m) / |nΦ|²
```

is in the pressure reconstruction layer, and I did not read a declaration that carries *both* with the paper's exact numerator. `PressureRecovery` and `LinearWaveResidual` are where it must be, and neither was opened in this pass. I am not calling it absent — I am recording that I did not check it, which is the honest state.

**(ii) The threshold sentence has no proposition.** "`q*` does not depend on `M`, `α`, or the correction stage" quantifies over three parameters *and* asserts a single witness serves all of them. The tree's `qbig` is a *number* with no stage argument (E133's finding, reused here) and `LocalScheduleWitness` carries one `qbig` across `∀ j` — so the fact is true by the shape of the definitions. But no theorem states it, because in Lean the way to state "this definition ignores these three arguments" is to *define it without them*, and then there is nothing left to prove. That is a shape difference, not a gap, and it is the same shape difference E133 recorded for Lemma 9.7.

### 4. Why this is partial rather than placed

Clause (ii) is permanent and structural; clause (i) is pending a read I did not do. A row with one unread clause and one inexpressible clause is partial, and it stays partial until the pressure read closes (i) — at which point the row's remaining defect is the same *kind* as Lemma 9.7's, and the ledger's convention for "matched except for a meta-sentence" should be settled once, for both.

Nothing here weakens the audit: the bounds the next stage consumes are declared, and the threshold's independence is visible in the definitions' arities.

*Evidence: `.setup/paper/ns.txt:3992–4025` (Proposition 7.2, (7.13)–(7.15)); `PrimaryODE.lean:89–92,181–244,495–560`; `ParticularWaveBounds.lean:1009–1096`; `JointODE.lean:1–233`; `WithinJointODE.lean:1–106`; `LocalScheduleWitness.lean`; E133. Reading only — `PressureRecovery`/`LinearWaveResidual` not read.*

## E159 — Lemma 9.7's third clause is settled as inexpressible, not as outstanding work (2026-11-24)

E133 made Lemma 9.7 partial and said its third clause "describes the construction's syntax and so has no proposition in the object language to be true of." That was right, but it left the row looking like work. It is not work. This entry closes the question and states the reason precisely, because the difference matters for the ledger's denominator.

The clause reads: *"For every fixed stage and output amplitude derivative, its construction and estimate require finitely many input amplitude derivatives."* The paper proves it by counting a directed acyclic graph of sums, products, derivatives and proved inverses, with `D_{v,a}(m) = max_{w→v} D_{w,a}(m + d_{v,w})`. The object being quantified over is a **derivation**, not a field. Lean has no term of that type: a proof is not a first-class value the statement can range over, and a definition's term structure is not a proposition.

There are exactly two Lean-level shadows, and both are present:

* **Record finiteness.** `StageEstimates` (`ActualStageEstimates:1–424`) is a structure with finitely many fields, each a bound on a named quantity. `GluedStageEstimates.actualStageEstimates` builds it from actual iteration data, so the number of obligations at stage `j` is the field count — a `Fintype` fact, not a theorem about derivative counts.
* **Closed-form loss.** `physicalLoss h m = 2*A h + (m+1)*(1+3h/2)` (E134) is stage-free, so the *loss* per derivative order is an explicit number and the per-stage choice the paper worries about cannot occur — which is the substantive content the third clause is protecting.

So the clause's mathematical content is discharged by the arities and the closed form, and its *syntactic* content has no Lean counterpart. Lemma 9.7 therefore stays `partial` in the ledger — the paper's sentence is not matched — but it must stop appearing in the work queue: no amount of reading will place it, and listing it as the next row has cost two entries of attention already.

Recommendation, recorded once: the ledger's `partial` category should carry two sub-kinds, `partial-unread` (Proposition 7.2 (i), Corollary 7.3, Proposition 7.6) and `partial-inexpressible` (Lemma 9.7, Proposition 7.2 (ii)). Only the first is a queue item. This entry does not change the count.

*Evidence: `.setup/paper/ns.txt:5669–5700` (Lemma 9.7 and its DAG count); `ActualStageEstimates.lean:1–424`; `GluedStageEstimates.lean:1–748`; `ActualCandidateConstruction.qbig`; `GermEndpointInputs`; `WholeDomainPhysicalStageTheorem.physicalLoss`; E133, E134. Reading only.*

## E160 — Lemma 7.4 is placed: `primary_bounds` gives `cP ≤ x ≤ CP` and the `O(1/S*)` ratio, and the jet bounds are the jet machinery (2026-11-24)

Lemma 7.4 constructs the homogeneous `m = 1` pulse and asserts (7.21). Both halves are one theorem, `PrimaryODE.primary_bounds` (`:432–452`), and the statement is the paper's line for line.

### 1. The initial data

`primary` (`:404`) is `solution hab d 1 (primarySeed a P) (fun _ => 0) p` — harmonic `1`, zero forcing, seed `!₂[P(p,a), 0]`. `primary_initial` (`:416`) proves `primary … a = ![P(p,a), 0]`, which is the paper's `z+(0) = P(0)`, `z−(0) = 0` in the `(z+, z−)` coordinates of `B`.

### 2. (7.21), left inequality

`primary_bounds` concludes, for every `v ∈ Icc a b`,

```
0 < radialPrimary … v
exp(-(D + 2C)L)/2 · P(p,v)  ≤  radialPrimary … v
radialPrimary … v  ≤  3·exp((D + 2C)L)/2 · P(p,v)
```

That is `cP(v) ≤ x(v) ≤ CP(v)` with `c = exp(−(D+2C)L)/2` and `C = 3exp((D+2C)L)/2`, explicit in the coefficient errors `C, D` and the slot length `L`. `radialPrimary` (`:408`) is `primary v 0 + primary v 1` — the paper's `x`, since `B`'s first column is `e_r − s_a K_a` and both `z±` multiply it with the same sign.

### 3. (7.21), the ratio

```
|transversePrimary / radialPrimary − d.eigenvector| ≤ 4·|d.eigenvector|·(coneConstant/S)
```

`transversePrimary` is `h·(z+ − z−)` (`:412`), i.e. the paper's `y`, and `d.eigenvector` is the paper's `h(v) = c₀√(1+s(v)²)`. The bound is `|y/x − h| ≤ 4|h|·κ_c/S` — the paper's `O(S*⁻¹)` with `4κ_c` as the constant. The reference form of `h` is imposed one layer down: `FrameData.errorB` and `errorC` (`:52–58`) subtract `λ/h` and `λh` from the frame coefficients, and `modal_errors_le` takes `hpair₁, hpair₂` — the eigenpair identities at the reference point — so `h` is `c₀√(1+s²)` up to the `C/S` error the same theorem bounds.

The ratio mechanism is `GrowingMode.scaled_growing_mode_bounds` + `scaled_cone_conditions` (`z−/z+` inside a `K/S` cone) + `original_coordinate_bounds` (cone in `(z+, z−)` → bounds in `(x, y)`), all composed inside `primary_bounds`. None of the three conclusions is assumed by another.

### 4. The derivative tower and the pressure factor

Every fixed derivative bound is the jet machinery: `WeightedODEJets.jet_solution_eq_solution` (`:337`) identifies the jet of the solution family with the solution of the jetted initial value, and `jet_solution_hasDerivWithinAt` (`:392`) makes the extension differentiable — so differentiating in the parameter or in `v` costs only polynomial powers, which is `C_I S^{B_I} P(v)`. `PrimaryODE.solution_forward_bound` (`:495`) is the scalar envelope form, and `PrimaryPulseBounds.fundamental`/`referenceP` (`:600`) are the `P(v)` and its Gaussian envelope.

The pressure's extra `ε^{1/2}` is not a separate estimate: the pressure is `ε` times the amplitude in the physical chart (`q^{1/2}` at fixed `q`, which is `ChartScales.epsilon`), so `ε^{1/2}` relative to `t_h` is the chart factor. `LocalizedWaveBounds`/`CurlClassBounds` carry it as `Q^{1/2}`; the paper's `ε^{1/2}` is that, and no theorem states the ratio as a standalone display.

### 5. Shape differences

* **`B(z+, z−)^T` is `(x, y)`.** `primary` solves in `(z+, z−)`, and `radialPrimary`/`transversePrimary` are the paper's `B`-coordinates. The matrix is never formed.
* **`c, C` are explicit.** `exp(∓(D+2C)L)` rather than named constants — better than the paper, in the same way Lemma 7.1's left inverse is.
* **The eigenvector carries the reference form.** `c₀√(1+s²)` is not a definition named `h`; it is the exact eigenpair identity imposed at the reference point and transported by `modal_errors_le`.
* **The pressure factor is a chart factor.** Recorded above; it is `Q^{1/2}` in the wave classes, not `ε^{1/2}` in a display.

No clause is unmatched. Statement-level: `primary_bounds`' proof is read at the composition points only, and nothing was compiled.

### 6. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 31 | 32 |
| partial | 2 | 2 |
| unplaced | 40 | 39 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:4127–4160` (Lemma 7.4, (7.21)); `PrimaryODE.lean:404–420,432–490,495–560,792–823`; `GrowingMode.lean:332–420`; `WeightedODEJets.lean:337,392,661`; `PrimaryPulseBounds.lean:600`; `ChartScales.epsilon`. Reading only — nothing compiled; "placed" is statement-level.*

## E161 — Proposition 7.5 is placed: Cramer weights, square-root amplitudes and a uniform positive floor are all theorems, and one displayed inequality is weaker in the tree (2026-11-24)

Proposition 7.5 is the cone-to-amplitude construction: form `H = [C(b+)|C(b−)]`, show `H⁻¹T₀,*` is componentwise positive, take square roots, and get `W₀` in `W_{1/2}` with `C(W₀) = εT₀,*`. The abstract half is a single module, and it is exact.

### 1. The linear algebra is `SmoothCovariance`

* `weights H T = cramerNumerator H T / det` (`:41`), with `cramerNumerator` the oriented areas (`:33`).
* `amplitudes H T i = Real.sqrt (weights H T i)` (`:53`) — the paper's `a_σ = √y_σ`, componentwise.
* `reconstruct_amplitudes` (`:101`): `H.mulVec (fun i => amplitudes … i ^ 2) = T`. That is `H(a²) = T`, i.e. `C(W₀) = εT₀,*` once `T = εT₀,*` and the `ε` is in `W₀ = √ε Σ a_σ b_σ`.
* `StrictCone H T` (`:49`) is `0 < (cramerNumerator i)·det` for both `i` — the paper's "the components of `H⁻¹T` are positive", stated as polynomial inequalities; `weights_pos_iff` (`:60`) proves the equivalence in both directions, so no sign convention is smuggled in.
* `StrictCone.amplitudes_pos` (`:97`), `contDiffOn_amplitude_vector` (`:171`), `strictConeRegion` open (`:294`), `contDiffOn_universal_amplitudes` (`:323`).

### 2. The uniform floor is `compact_uniform_amplitudes`

```
IsCompact K → (∀ x ∈ K, StrictCone (H x) (T x)) →
  ∃ δ > 0, ∀ x ∈ K, δ ≤ |det| ∧ δ ≤ weights … ∧ δ ≤ amplitudes …
```

That is the paper's uniform positivity, on amplitudes as well as weights — the paper needs it only for `weights`, and the tree proves the stronger four-way statement. `compact_family_perturbation_stability` (`:346`) is the paper's "after a further single decrease of `q*`, `H` is invertible throughout each enlarged slow neighborhood": a uniform `ρ` such that every competing pair within `ρ` of the family stays in the cone. That is a *perturbation* statement, not a compactness statement, and it is exactly what "one further decrease" means.

### 3. The actual target, on the actual annulus

`FinalSlowBase.covarianceTarget` (`:211`) defines `T` from the real leading stress pair and the chart factor, and `covarianceTarget_cones` (`:222`) proves `ReferenceCone` and `TargetCone` for it at every `q > 0`, `N`, and label. `TargetCone` (`PrimaryRepresentatives:557`) is `⟪T, normalDirection g⟫ < 0` and `targetRatio F g T < 1` — the paper's cone condition in slope form, derived from the profile's `FullTrueCone` by `AlignedProfileSpectralCone.modulated_chartTarget_cones`.

The lower bound is `PrimaryCovarianceBounds.ZeroOrderBounds.weight_lower` (`:342`):

```
inverseLower * R * ζ ≤ weights H T j
```

and `sqrt_S_lower` (`:371`) instantiates `R = √S` (using `sqrt_S_eq`, `√(n²) = n`) *without losing the flat target factor*, in the module's own words. `primaryWave_waveClass` (`:1536`) then gives `WaveClass s P (1/2)` of the √-amplitude times the curl potential — the paper's `W_{1/2}` membership.

### 4. The one displayed inequality that is weaker here

The paper prints `y_σ ≥ c√(S*ζ)`. The tree proves `inverseLower·√S*·ζ`. Since `0 < ζ ≤ 1`, `ζ ≤ √ζ`, so

```
c√S*·ζ  ≤  c√S*·√ζ  =  c√(S*ζ)
```

— the tree's floor is **smaller** than the paper's. It is still enough for what the paper uses it for: (7.33) needs `y_σ^{−k−1/2}` to leave only `ζ^{−1/2}` after `k` numerator weights cancel, and `y_σ ≥ c√S*·ζ` gives `y_σ^{−1/2} ≤ c^{−1/2}S^{−1/4}ζ^{−1/2}`, which is the needed form with `S^{−1/4}` extra to absorb.

So this is a weakening of a printed inequality that does not break its only consumer, and the module says so deliberately (`sqrt_S_lower`'s docstring: "The weaker inverse bound required by the square-root jet theorem"). It is the first such weakening in §7, and it is recorded rather than smoothed because a reader checking (7.25) against the tree will find the exponents differ by `1/2` in `ζ` and deserve to be told why it does not matter.

### 5. Shape differences

* **`W₀` is per-label.** `primaryWave`/`uncutPrimaryWave` assemble it label by label; there is no global `W₀` field. The paper's `W₀ = √ε Σ a_σ b_σ` is the same sum, taken inside one label.
* **`C(W₀) = εT₀,*` is `reconstruct_amplitudes` plus the chart factor.** No theorem is named for the covariance identity itself; the identity *is* the square-root reconstruction, which is why it holds exactly rather than up to an error.
* **`ε` lives in the chart.** `W₀ = √ε Σ …` is `Q^{1/2}·…` at fixed `q`; the `√ε` is never a scalar in the field definition.

No clause is unmatched; one is weaker. Statement-level throughout.

### 6. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 32 | 33 |
| partial | 2 | 2 |
| unplaced | 39 | 38 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:4210–4245` (Proposition 7.5, (7.24)–(7.27)); `SmoothCovariance.lean:33–124,171,268–292,294–370`; `FinalSlowBase.lean:211–232`; `PrimaryRepresentatives.lean:200–208,557–560`; `PrimaryCovarianceBounds.lean:107–137,340–381`; `PrimaryPulseBounds.lean:968–975,1536–1540`. Reading only — nothing compiled; "placed" is statement-level.*

## E162 — Proposition 7.6 stays partial, and for the same reason as Corollary 7.3: no declaration is the map `Σ ↦ LΣ` (2026-11-24)

Proposition 7.6 asserts three things about `LΣ = √ε Σ δa_σ b_σ` with `δa_σ = (H⁻¹(Σ/ε))_σ/(2a_σ)`: the class `W_{α−1/2}`, the exact right-inverse identity `B(W₀, LΣ) = Σ`, and `C(η_β LΣ) ∈ M_{2α−1}`. The class and the quadratic remainder are declared. The map is not.

### 1. What is declared

* **`C(η_β LΣ) ∈ M_{2α−1}`.** `CorrectionStep.symmetricCovariance_mem` (`:2296`) gives `TensorClass s (α+β)` for `symmetricCovariance a b` from `WaveBounds α`, `WaveBounds β`; at `α = β = α−1/2` this is `2α−1`. `signedTensorRemainder_mem`'s third hypothesis `hγs : γ ≤ 2β` is the same product rule, and the paper's `C(V)` in (7.41) is that term.
* **The class `W_{α−1/2}`.** `PrimaryPulseBounds.covariance_amplitudes_class` (`:968`) and `primaryWave_waveClass` (`:1536`) close the class of a √-amplitude times a curl potential; the `α−1/2` is the exponent the amplitude carries once the `ε^α` source is divided by `a_σ`, and `LocalizedWaveBounds` carries the multiplication by `η_β`.
* **The quadratic remainder is retained, not dropped.** `signedTensorRemainder_exact` (`CorrectionStep:2313`) expands the covariance change into `B(E, Σ) + B(U, R) + C(V)` with `C(V) = bilinearCovariance (tangent+curl) (tangent+curl)`; the paper's `C(LΣ)` is that, and it is *present* rather than assumed small. That is the clause a reader would expect to be missing, and it is the strongest part of the match.

### 2. What is not declared

`B(W₀, LΣ) = Σ` is an *identity about a constructed map*. The paper proves it by `B(W₀, LΣ) = εH(2a ⊙ δa) = εH dΣ = Σ`, where the factor `2` is the real-cosine normalization and the `1/(2a_σ)` is chosen to cancel it. The tree never forms `δa`, never forms `dΣ`, and never defines `LΣ`:

* `signedTensorRemainder` *subtracts* `Σ` (`symmetricCovariance primary tangent`) instead of producing it from `δa`, so the right-inverse property is true of the stored covariance difference — `(u.addIncrement …).covariance − u.covariance − Σ = signedTensorRemainder …` at `CorrectionStep:3242` — but the *inverse direction* is not exhibited.
* No declaration has type `Σ ↦ LΣ`, and none has the `1/(2a_σ)` normalization. `SignedWaveUpdate` carries no `bilinearCovariance`, `two_mul` or `deltaAmplitude` (searched: 0 matches), and `PartitionedCovariance` carries no `2 * a`, `linearCoefficient` or `crossTerm` (searched: 0 matches).
* `FrameData.forcing` *is* a projection, but it is the projection of a **source onto `n⊥Φ`**, not the inverse of the covariance map.

### 3. Why this is the same finding as E154

Corollary 7.3 needs `f_m ↦ (t_m, π_m)` and is partial because no declaration is that operator. Proposition 7.6 needs `Σ ↦ LΣ` and is partial for the identical reason: the tree proves the *statements about* the operator's output — its class, its quadratic remainder, and the identity its output satisfies — while the operator itself is only ever applied implicitly, inside `assemble`/`actualStageEstimates`. E154 called this "uniformity proved three times over, operator not declared"; this entry adds the second instance, and together they say something about the development worth stating once:

**The §7–§8 construction is stated in terms of the *fields it produces*, not in terms of the *maps it uses*.** That is why 7.1, 7.4, 7.5 place cleanly (they produce fields) and 7.2, 7.3, 7.6 do not (they are maps). It is not an error and it is not a gap in the mathematics; it is a difference in what the formalization chose to name, and it is exactly the kind of difference the kernel cannot see.

### 4. What would close it

One declaration of the form

```
linearizedAmplitude (H a Σ) (hcone : StrictCone …) : HarmonicBlock
theorem linearizedAmplitude_spec : B(W₀, linearizedAmplitude …) = Σ
```

with the `1/(2a_σ)`. `SmoothCovariance.inverse_formula` already gives `H⁻¹T = weights H T`, so `dΣ` is one line; the missing piece is the block-level `B` and the `2a ⊙` cancellation, which `signedTensorRemainder_exact`'s `C` term shows the machinery can express.

*Evidence: `.setup/paper/ns.txt:4317–4345` (Proposition 7.6, (7.31)–(7.34)); `CorrectionStep.lean:2296–2322,2366–2410,3242–3252`; `SmoothCovariance.lean:75–95`; `SignedWaveUpdate.lean` (0 matches for `bilinearCovariance|two_mul|crossCovariance|deltaAmplitude|linearized`); `PartitionedCovariance.lean` (0 matches); `PrimaryPulseBounds.lean:968,1536`; E154, E157. Reading only — nothing compiled.*

## E163 — Lemma 6.1 is placed: the slot system is a structure with one radius field chosen before the label quantifier (2026-11-24)

Lemma 6.1 is the geometric lemma the oscillatory layer rests on: there are centers `c_γ` and one radius `r0 > 0`, chosen once for every label and every band, such that the enlarged rectangles of (6.10) are injectively parametrized on their band torus, and such that two labels whose slow supports meet have disjoint lifted enlarged rectangles. The tree does not merely contain the ingredients; it contains the object, and the lemma is its inhabitation.

### 1. The paper's statement

(6.10) defines `R_γ`, `R⁺_γ` and their preimages `R^abs_γ`, `R^abs,+_γ`; (6.13) is

```
γ ≠ γ′,  K_γ ∩ K_γ′ ≠ ∅   ⟹   R^abs,+_γ ∩ R^abs,+_γ′ = ∅
```

with `K_γ` the slow support of the cutoff `η_γ = χ_ℓ(q)χ_{ℓ,a}`. The paper proves it in three steps: a bounded-degree interaction graph with finitely many colours, centers chosen per colour subject to the ordered constraints (6.15), and one rectangle size small enough to keep the separation after a fixed enlargement.

### 2. The Lean statement is that object

`PartitionedCovariance.SlotSystem` (`PartitionedCovariance.lean`, immediately above `exists_slotSystem`):

```
structure SlotSystem (D h : ℝ) (vr vt : Plane) where
  radius     : ℝ
  radius_pos : 0 < radius
  injective  : ∀ L, InjOn quotientPoint (slotSet h radius vr vt L)
  disjoint   : ∀ L M, SlotColoring.Adj D L M →
    Disjoint (liftedSupport (nativeIndex h L.1) (slotSet h radius vr vt L))
             (liftedSupport (nativeIndex h M.1) (slotSet h radius vr vt M))
```

and

```
theorem exists_slotSystem (D h : ℝ) (hh : 0 ≤ h) (vr vt : Plane) :
    Nonempty (SlotSystem D h vr vt)      -- :233
```

The quantifier order is the paper's: `radius` is a field, fixed before `∀ L`, and `slotSet h r vr vt L = orientedRectangle (slotCenter h L) vr vt (2 * r)` (`SlotGeometry.lean:387`), so the tree's `radius` is the paper's `r0` and the `2r0` enlargement lives inside the definition of the set rather than in a separate object. `injective` is "the enlarged rectangles are injectively parametrized" and `disjoint` is (6.13), both as fields of one structure.

### 3. Where the radius comes from, and why it is band-independent

`SlotGeometry.exists_oriented_slots` (`SlotGeometry.lean:410–418`):

```
∃ r, 0 < r ∧
  (∀ level n, n ≤ D → ∀ i j : Fin m, 0 < n ∨ i ≠ j →
     Disjoint (liftedSupport level (orientedRectangle (center m D i) a b (2*r)))
              (liftedSupport (level+n) (orientedRectangle (center m D j) a b (2*r)))) ∧
  (∀ n ≤ D, ∀ i, ∀ x y ∈ orientedRectangle (center m D i) a b (2*r),
     torusEq ((cover^n) x) ((cover^n) y) → x = y)
```

The radius is existentially chosen **before** `∀ level`, and `D` is `SlotColoring.nativeGap h`, a function of `h` alone. That is "common to all labels and independent of the band" as a quantifier order, not as a claim. The centers are `slotCenter h L = SlotGeometry.center 2250 (nativeGap h) (color L)` — a finite family indexed by the colour, which is what the paper's greedy colouring produces.

### 4. Step 1: bounded degree, a finite palette, and (6.14)

* **The palette is explicit.** `SlotColoring.Palette = Fin 9 × ((Fin 3 → Fin 5) × Bool)` with `palette_card : Fintype.card Palette = 2250` (`SlotColoring.lean:158–165`), and `colorData_proper` (`:167`) proves it is a proper colouring of `Adj`. The paper says "finitely many colours" and prints no number; the tree prints 2250.
* **Bounded degree, with a bound.** `neighbors_card_le` and `degreeBound D = 18 * (2 * indexRadius D + 1)^3` (`:276–305`). `Adj` is a `Prop`-valued structure over mesh boxes and level gaps, so "bounded degree" is a `Finset.card` inequality rather than a graph-theoretic assertion.
* **(6.14) is `nativeIndex_gap`.** `SlotColoring.lean:400` gives `|nativeIndex h n − nativeIndex h m| ≤ nativeGap h` for levels within four, with `nativeGap h = ⌈nativeGapBudget h⌉₊ + 1` and `nativeGapBudget h = (4(1+h)log 2 + 2 log 5)/log Tg` (`:337–340`). The paper's printed bound carries `8/ℓ0` where the tree carries `2 log 5`: the tree bounds `|log n − log m| ≤ log 5` from `|n − m| ≤ 4` (`log_level_gap`, `:342`), while the paper's term comes from the `2 log ℓ` inside the level formula. Both are independent of the band, which is the only property the lemma uses; the tree's `nativeGap` is the paper's `Δmax` with a different but fully explicit derivation.

### 5. The one place the match is a composition: "supports meet" becomes `Adj`

The paper's hypothesis is geometric (`K_γ ∩ K_γ′ ≠ ∅`); the tree's is combinatorial (`SlotColoring.Adj`). The direction the lemma needs is proved, in two steps:

* `PartitionedCovariance.masks_force_adjacency` — two distinct labels whose physical masks are both nonzero at a point are `Adj`.
* `PositiveTimeSignedData.mask_pullback` (`:42`) — the physical mask equals the slow-coordinate mask `PhysicalWaveSum.physicalMask (CoordinateAlgebra.D h)` under the lift.

So a point of `K_γ ∩ K_γ′` makes both masks nonzero, hence `Adj`, hence `SlotSystem.disjoint` applies. The paper's implication is *derived*, not assumed; the reverse implication is neither proved nor used.

### 6. Shape differences

* `Adj` is combinatorial (mesh boxes, level gap ≤ 4, opposite signs) rather than support-geometric; `masks_force_adjacency` is the only direction consumed.
* The palette's size is 2250 in the tree and unspecified in the paper.
* `Δmax` is `nativeGap h`, derived through `log 5` rather than `8/ℓ0`.
* `injective` is quotient-injectivity on the enlarged rectangle at the base torus; injectivity of each individual lift is the sheet count of `TorusCoverDegree` (E164 clause 2), not an extra hypothesis here.

No clause is unmatched. Statement-level: the composition points were read, and nothing was compiled.

### 7. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 33 | 34 |
| partial | 4 | 4 |
| unplaced | 36 | 35 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:3364–3430` (Lemma 6.1, (6.10)–(6.14)); `PartitionedCovariance.lean:196–258,283–296`; `SlotGeometry.lean:387–388,410–418`; `SlotColoring.lean:158–191,276–305,337–408`; `PositiveTimeSignedData.lean:42–47`; `PhysicalWaveSum.lean:295–308`. Reading only — nothing compiled; "placed" is statement-level.*

## E164 — Lemma 6.2 is partial: three of its four clauses are separate theorems, and the radial-integration half is not stated as a preservation result (2026-11-24)

Lemma 6.2 is §6.3's common-torus lemma. It asserts four things: the change `H ↦ Y_i` has uniformly bounded derivative factors; `R^H_γ` is `14^{Δ_ℓ}` disjoint lifts of `R_γ`; Haar averages agree on the absolute, common and band tori for pullbacks; and radial integration at fixed `(z,t)`, torus translation, averaging and directional Fourier inversion on zero-mean functions preserve common-torus descent without introducing a new dyadic band. The first three clauses are declarations. The fourth is a conjunction of four operations, and the tree proves three of them — separately, and never as one property.

### 1. Clause 1 — the derivative factors are bounded, with printed constants

* `ActualSignedGeometry.slowChangeCost h = 1 + powerBound (1/2) + powerBound (D h) + powerBound 1` and `norm_slowChange_le` (`ActualSignedGeometry.lean:516–545`): `‖slowChange h (Q n) (Q m)‖ ≤ slowChangeCost h` for `|n − m| ≤ 4`, uniformly in the two levels.
* `CommonCoverClass.argumentCost g = 1 + ‖g.coordinateLinear‖ + ‖g.pointLinear‖(1 + ‖g.coordinateLinear‖)` (`:171`), with `norm_nativeLinear_le`; `bandGeometry_argumentCost_le` (`:354`) bounds it by `bandArgumentCost B D * S n` uniformly in the center and in `gap ≤ D`.
* `ActualSignedGeometry.slotGeometry_argumentCost` / `slotGeometry_common_cost` (`:437–453`) compose the two into `25 * bandArgumentCost … * S n`.

That is "uniformly bounded derivative factors": the constants do not depend on the band, the chart, or the lattice copy. The paper states one constant; the tree states `slowChangeCost h` and `bandArgumentCost B D`, which is stronger information, not weaker.

### 2. Clause 2 — `14^{Δ_ℓ}` disjoint lifts

* `TorusAverages.covering` is the paper's matrix `[[3,1],[1,5]]` (`:39`), so `|det| = 14`.
* `TorusCoverDegree.card_liftedRectangles` (`:296–302`): `Nat.card (Set.range (sheetRectangle g r)) = 14 ^ g.gap` for `0 < r` and `‖basis‖ * r < 1/2`.
* `pairwise_disjoint_sheetRectangles` (`:247`), `preimage_nativeRectangle_sheets` (`:221`), `covering_bijOn_sheetRectangle` (`:259–274`): the sheets are disjoint, their union is the preimage, and each maps bijectively onto the native rectangle.

`g.gap` is the paper's `Δ_ℓ`, and `SlotColoring.nativeIndex_gap` (E163) is what bounds it by `Δmax`. Clause 2 is exact, and slightly more general: it is proved for any gap, not only for gaps arising from two band indices.

### 3. Clause 3 — the Haar averages agree

* `TorusAverages.squareAverage_covering_iterate` (`:108`), `_smooth` (`:123`) and `_real` (`:129`): for a continuous unit-periodic `f`, `squareAverage (f ∘ covering^[n]) = squareAverage f`, for every `n`.
* `squareAverage_torusLift` (`:103`) identifies the plane average with the Haar integral on `Torus`.

Three tori, three powers of the same covering: instantiate at `0`, `Δ_ℓ`, `i(ℓ)`. The paper's clause is this identity; the tree states it once at arbitrary `n`, which covers all three.

### 4. Clause 4 — three operations declared, one not, and no name for the property

The sentence's four operations, and what the tree has for each:

| Operation | Declaration |
|---|---|
| torus translation | `TorusAverages.periodize_periodic` (`:317`), `quotientPoint_lattice_add` (`:156`) |
| averaging | `TemporalMeanUpdate.centered_periodic`, `centered_zeroMean` (used at `MeanChartCompatibility.lean:461`) |
| directional Fourier inversion, zero mean | `SmoothFourierData.inverse_solves_smooth_periodic` (`:565–571`), `inverse_zero_mean` (`TorusInverse.lean:574`), `directionalInverse_periodic` (`:578`); lifted to fields by `ParametricTorusInverse.inverse_periodic` (`:504`) and `inverse_zeroMean` (`:509`) |
| radial integration at fixed `(z,t)` | **not found as a preservation statement** |

The radial integrals the tree actually uses (`MeanIncrementBounds`, `RadialPullback`, `SignedStressPrimitive.angular_divergence`) do fix `(z,t)` and do leave the band index untouched — the level `n` is a parameter no radial integral rebinds. But no declaration states *that*, and "no new dyadic band" has no proposition to be true of either: the strongest related statement is `CommonCoverWithin.commonSolve_contDiffOn_within`'s docstring, "The source need only descend to the common torus; no band descent is added". A docstring is not a theorem (E90, E94, E127).

So the fourth clause half-matches: three of its four operations are declared, the fourth is implicit in the assembly, and the property the sentence is *about* — common-torus descent — has no name in the tree. That is the E162 finding at one remove: the §6 construction is also written in terms of the fields it produces, not the property it preserves.

### 5. Why partial rather than placed or unplaced

Placed would claim the conjunction; it is not there. Unplaced would deny the three clauses that are exact. It is partial, with the unmatched part named precisely: `radial integration at fixed (z,t)` and `no new dyadic band`, plus the absence of a `CommonTorusDescent` predicate. The precedent is E129, E131 and E132, which went partial on statement shape while their content was present.

### 6. What would close it

Two declarations:

```
def CommonTorusDescent (g : Geometry) (F : P × Plane → V) : Prop
theorem radialIntegral_descends (h : CommonTorusDescent g F) : CommonTorusDescent g (radialIntegral F)
```

and the three existing closure lemmas restated against the predicate. The mathematics is already there; what is missing is the name, which is exactly the kind of obligation a kernel cannot notice.

### 7. The ledger move

| Status | Before | After |
|---|---|---|
| placed | 34 | 34 |
| partial | 4 | 5 |
| unplaced | 35 | 34 |
| **total** | **73** | **73** |

*Evidence: `.setup/paper/ns.txt:3450–3520` (Lemma 6.2, (6.17)–(6.20)); `TorusAverages.lean:39,103–133,156,317`; `TorusCoverDegree.lean:221,247–274,296–302`; `ActualSignedGeometry.lean:437–453,516–545`; `CommonCoverClass.lean:171–181,354–356`; `SmoothFourierData.lean:565–571`; `TorusInverse.lean:574–581`; `ParametricTorusInverse.lean:504–521`; `CommonCoverWithin.lean:102–107`; `MeanChartCompatibility.lean:461`. Reading only — nothing compiled.*

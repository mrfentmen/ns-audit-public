# Working notes — 2026-11-21

Provisional reading notes. **Not** audit entries; nothing here has been published or
independently reproduced. Source read at `f9e8bc5`.

Scope: statement fidelity against the comparator, the load-bearing stage-estimate
chain, and the pressure-flux proof bodies. Reading only; no builds during this pass.

---

## 1. Build status (separate attempt, for context)

- `lake build NavierStokes`: 9,580 jobs, exit 0, 20 min 17 s, 817 modules,
  peak RSS 7.46 GB. Run in a Linux VM.
- `#print axioms` on `breakdownStatement`, `theorem_1_1`,
  `theorem_1_1_with_initial_rest`, `theorem_1_1_with_dissipation`: only
  `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`.
- Not built: `Euler/`, `ComparatorChallenges/`.
- Native macOS: `lake` aborts with SIGTRAP in `libmalloc` at worker-thread teardown
  (3/3). The VM is a workaround, not a fix.

---

## 2. Statement fidelity — CLOSED

### What the comparator asks

`ComparatorChallenges/NavierStokes.lean` (adapted from DeepMind Formal Conjectures),
with `NavierStokes.json` permitting exactly `propext`, `Quot.sound`,
`Classical.choice`. Alternative (C), for every `ν > 0`, asks for `(u₀, f)` with:

- `InitialVelocityConditionDecay u₀` — smooth, divergence-free, every derivative
  decays faster than any polynomial;
- `ForceConditionDecay f` — smooth on `t ≥ 0`, every derivative decays faster than
  any polynomial in space and time;
- no `(v, p)` smooth on `R³ × [0,∞)`, divergence-free, satisfying the PDE for **all**
  `t ≥ 0` (`derivWithin` at the boundary), matching `u₀`, with `L²` slices and a
  uniform energy bound.

### The bridge, read end to end

`ComparatorSolution.navier_stokes_breakdown_R3` → `ComparatorBridge.navier_stokes_breakdown_R3`
→ `theorem_1_1` + `comparator_of_breakdown`.

`comparator_of_breakdown` (R3/ComparatorBridge.lean) supplies `u₀ := 0` and
`f := toComparator f`, and proves both admissibility conditions rather than assuming
them:

- `zero_initial_condition_decay` — the zero datum satisfies the decay condition;
- `forceConditionDecay_of_compact h.force_smooth h.force_support.1` — decay is
  **derived** from `C^∞` plus compact spacetime support.

Refutation direction: any comparator solution `hv` is converted by
`globalSolutionOfComparator` into a `GlobalFiniteEnergySolution ν f`, contradicting
the paper's non-existence clause.

### All translation lemmas read (NavierStokes/ComparatorBridge.lean)

| Lemma | Content | Status |
|---|---|---|
| `toComparator` / `fromComparator` | argument swap `(t,x) ↔ (x,t)` | definitional |
| `divergence_eq` | `spatialDivergence` = trace of `fderiv` (sum over basis) | proved |
| `gradient_eq` | `pressureGradient` = Mathlib `gradient` | proved |
| `laplacian_eq` | `spatialLaplacian` = `Δ`, given a `C²` spatial slice | proved |
| `temporalDerivative_eq` | `derivWithin (Ici 0) t = fderiv` at `0 < t`, via `derivWithin_of_mem_nhds` | proved |
| `fromComparator_smooth` | smoothness transfers under the swap | proved |
| `comparator_equation_Rn` | comparator PDE at `t ≥ 0` ⇒ paper residual at `t > 0` | proved |
| `normalized_solution_Rn` | viscosity rescaling (other bridge path) | proved |

The `derivWithin` boundary subtlety is exactly `temporalDerivative_eq`: at `t > 0`,
`Ici 0` is a neighbourhood, so the one-sided derivative is the ordinary one. No gap.

**Conclusion: no fidelity gap between the verified paper statement and the comparator
encoding.** The remaining caveat is the encoding itself (Formal Conjectures'
adaptation of the Clay wording), not the bridge.

---

## 3. Stage estimates — load-bearing chain is deeper than E67

### Which branch is load-bearing

`ActualCandidateAssembly.lean:1094` calls `GluedStageEstimates.actualStageEstimates`
(:684). That is the real chain.

`ActualStageEstimates.stageEstimates_of_representations` is a **parallel branch**,
not called by the assembly. Its `WaveInputs` parameter carries 8 exponent/shift
fields as hypotheses and has **no construction site** in the tree (the field
`particularPotential_exponent` occurs only at its declaration and at its use).
Likewise `ActualEndpointInputs.actual_stage_endpoints` and `endpointInputs_of_run`
have no callers. These are an unused alternate route, not a hole in the proof.

### The real chain, all read

```
ActualCandidateAssembly:1094
  → GluedStageEstimates.actualStageEstimates                :684
  → GluedStageEstimates.stageEstimates_of_component_bounds  :402
  → GluedStageEstimates.represented_raw_bounds              :350
  → raw_of_positive_bounds + potential_bound/direct_bound/pressure_bound
```

`represented_raw_bounds` (Glued, :350) takes as hypotheses:

- `hsA/hsP` — smoothness of the *particular* components;
- `hbA/hbP` — pointwise derivative bounds `Bound qbig (particularA j) m (gain (j+1) − LA m)`.

Those two families are **discharged, not assumed**, by `actualStageEstimates`
supplying `current_potential_bound` and `current_pressure_bound` (:640+), which are
themselves proved from `glued_bound_of_local` plus per-mode bounds.

Exponents are proved, not chosen: `gain_le_current_exponent` and
`current_potential_loss_le` / `current_pressure_loss_le` are `linarith` consequences
of the iteration ledger.

### The mode bounds, read

`current_potential_mode_bound` (:873) and `current_pressure_mode_bound` (:939) each
produce `∃ C ≥ 0` bounding every physical jet of the literal current mode by

```
C · physicalQ(w) ^ (h·((1/2 + σ) + 1/2) − currentLoss(…) m)
```

uniformly over every label, every dyadic band `n ≥ 4`, and every point of the band.
The proof has three parts: `actual_native_potential_bound` gives the native chart
jet with amplitude `A` and exponent `p`; `vector_chart_physical_bound` /
`scalar_chart_physical_bound` transfers it to the physical jet; and the germ identity
`localPotentialMode_germ` transfers the result to the physical mode. Outside the
annulus, the mode is supported away and the estimate is trivial.

Nothing physical is assumed: the only hypothesis is
`H : ActualParticularCycleData.Invariant σ x` plus the geometric floor `hN`.

### The true floor, read

`actual_native_potential_bound` (:543) and `actual_native_pressure_re_bound` (:599)
each take exactly one quantitative hypothesis:

```
H : LabelSumBounds.UniformWaveClass nativeStrip nativeEnvelope α
      (ActualParticularStageControls.currentSource x j)
```

and produce native jet bounds `C · Q(n)^(h(α+1/2) − 2hm) · S(n)^p`, with `C` and the
integer `p` chosen. The other inputs are only `PreservesCarriers`, `InputSupport`, and
the geometric floor `hN`. The pressure version passes through `Complex.reCLM`, using
`‖reCLM‖ ≤ 1`.

So the floor is **one wave-class membership statement about the actual source**, not a
physical derivative estimate. `Invariant` supplies it via
`ActualParticularCycleData.native_source_class H j hj`, and `Invariant` is
`CycleAnalyticInvariant` (`ActualParticularCycleData.lean:38`), initialized and
preserved by the cycle.

**Chain complete:** source wave class → native jet bounds → chart transfer →
current mode bounds → current component bounds → `RawStageBounds` → `StageEstimates` →
candidate → `breakdownStatement`.

### Status of E67

E67's "existential constants, not evaluated" remains true: `raw_of_positive_bounds`
extracts witnesses with `choose`. The refinement is that the fields feeding it are
derived one layer lower than E67 recorded, and that the alternative `WaveInputs`
branch is not part of the proof.

---

## 4. Pressure flux — interface and bodies read

`PressureRecovery.Hypotheses` (`R3/PressureRecovery.lean:33`) has exactly ten fields:
`0 < T`; smoothness of `u`, `v`, `p`, `q`; `div u`, `div v`; residual equality;
uniform finite energy of `u` and of `v`. **No pressure bound, decay, or growth
assumption.**

Proof bodies read in `R3/PressureFlux.lean`:

- `actual_flux_integrable_and_le_canonicalNorm` reduces the physical flux to
  `canonicalCutoffFlux`, via `actual_flux_eq_canonicalCutoffFlux` →
  `ActualPressureFlux.pressure_flux_eq_canonical`;
- `pressure_flux_eq_canonical` (`R3/ActualPressureFlux.lean:38`) uses only
  `H.tensor_bound`, divergence-free `u − v`, and `gradient_recovery`, concluding the
  canonical Riesz pairing identity;
- `canonicalCutoffFlux_bound` is built from `cutoff_pressurePair_bound` plus a
  commutator estimate: Hölder `6/5`–`6`, a Riesz-test Sobolev constant, a Lipschitz
  cutoff bound, and an explicit commutator constant. The envelope printed in the
  theorem statement matches the one consumed by `eq_of_pressure_flux_bound`.

### The last two pressure steps, read — CLOSED

`gradient_recovery` (`R3/PressureRecovery.lean:407`) derives, at every interior time,

```
∫ ∂ₖ(p − q)·ψ = −Σᵢⱼ pressurePair i j (tensorDiff u v t i j) (∂ₖ ψ)
```

from the equation and uniform finite energy only. The route is genuine analysis:
`time_test_gradient_difference_zero` shows every compact temporal test annihilates the
difference between the physical pressure-gradient pairing and the canonical tensor
pairing; `averaged_value_zero` obtains that from an `H³` bound plus harmonicity on
compact tests (`eq_zero_of_compact_harmonic`); `TemporalTestUniqueness` then upgrades
the vanishing integrals to pointwise equality in time.

`pressure_flux_eq_of_gradient_identification` (`R3/PressureFluxIdentity.lean:114`) is
integration by parts: it splits the flux test into `Σₖ ∂ₖ(χ·wₖ)` using divergence-free
`w`, applies the gradient identification to each component, and reassembles the
canonical pairing.

**No pressure hypothesis anywhere in the path.** The remaining inputs are exactly the
ten fields of `PressureRecovery.Hypotheses`.

---

## 5. Open leads, ranked

1. **`CycleAnalyticInvariant.source_class` and its preservation** — the last place a
   quantitative property could be assumed rather than derived. The mode bounds consume
   it as a hypothesis; the question is whether `ActualCyclePreservation` proves it at
   every cycle.
2. **Comparator axioms** — `#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3`
   would verify the adapter itself, not just the paper statement. **Closed**: run in CI (E73);
   the footprint is `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
3. **Periodic option (D)** — bridged, compiled, audited by reading (E70), and its axiom
   footprint printed on a clean clone (E73). Remaining: the external nanoda re-check, which
   is a different tool and was not run.
4. **Dead-branch note** — `WaveInputs`, `actual_stage_endpoints`,
   `endpointInputs_of_run` are unused alternates; worth an explicit line in the log so
   a later reader does not mistake them for the proof path.

---

## 6. What this pass implies for existing entries

- **E50** ("no oleans, no build") is superseded: crash real and reproducible, build
  succeeds on Linux.
- **E67** stands, refined to the floor: constants existential, exponents proved, and
  the chain continues below `RawStageBounds` through `current_*_bound` →
  `current_*_mode_bound` → `actual_native_*_bound` → a single wave-class hypothesis on
  the actual source, carried by `CycleAnalyticInvariant`. The `WaveInputs` branch is
  not load-bearing.
- **Pressure flux** is closed end to end: hypothesis interface, gradient recovery,
  integration by parts, and the explicit constant. No unread pressure step remains.
- **Statement fidelity** is closed at the bridge; only the encoding's fidelity to the
  Clay PDF remains outside Lean.

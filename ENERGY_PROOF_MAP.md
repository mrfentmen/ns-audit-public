# ENERGY PROOF MAP — Lemma 10.4

**Theorem.** `NavierStokesR3.CompactEnergy.candidate_energy_estimates`
**Source.** `NavierStokes/R3/IntegratedDissipation.lean:279`, upstream `openai/NavierStokesAndEuler@f9e8bc5`.
**Paper row.** Lemma 10.4 (`ns.txt:6115`), the kinetic-energy and finite-dissipation estimate for the localized candidate.

**Status.** Statement-and-consumer reading, not a recompilation. I read the declarations and the named proof steps; I did not replay the proof term. Step 4 (`sqrt_energy_le_integral`) was read through: its statement, its ε-regularization, and every hypothesis it consumes.

Paths beginning `R3/` are relative to `NavierStokes/`; all line numbers are into `f9e8bc5`.

## The argument in one paragraph

Test the Navier–Stokes equation against the velocity itself and integrate over space. The advection term vanishes because the flow is divergence-free and compactly supported, the pressure term vanishes for the same reason, and the viscous term becomes minus twice the dissipation. This leaves the exact identity `½ d/dt ‖u‖² + ν‖∇u‖² = ⟨f,u⟩`. Cauchy–Schwarz bounds the force work by `‖u‖ ‖f‖`. Dividing by `‖u‖` and integrating from the zero datum gives `‖u(t)‖ ≤ F(t)`, where `F(t) = ∫₀ᵗ ‖f(s)‖ ds` is the accumulated force norm. Returning to the exact identity and integrating once more gives `‖u(t)‖² + 2ν∫₀ᵗ ‖∇u‖² ≤ F(t)²`. The force is compactly supported and smooth, so `F(1)` is finite. An exhaustion of `[0,1)` then proves the total dissipation is genuinely integrable, not merely bounded on each shorter interval. There is no hidden multiplicative constant in this lemma: the coefficient in front of `F(t)²` is exactly one.

## The map

| # | Step in plain words | Lean declaration / file | Hypotheses used | Constant status |
|---|---|---|---|---|
| 1 | **Test the equation against the velocity.** The advection and pressure terms integrate to zero; viscosity becomes `-2ν` times the dissipation. | `CompactEnergy.energy_balance` (`R3/CompactEnergy.lean:202`) and `energy_balance_viscosity` (`R3/ViscousEnergyBalance.lean:22`); differentiated form `hasDerivAt_energy_balance_viscosity` (`R3/ViscousEnergyBalance.lean:56`). | Smooth spatial slices of `u` and `p`; continuous force slice; compact support of the velocity slice; divergence-free; residual equals `f`. | None. |
| 2 | **Integrate the identity over time.** The fundamental theorem of calculus and the zero datum remove the boundary term. | `IntegratedDissipation.integrated_energy_balance` (`R3/IntegratedDissipation.lean:27`). | `0 < T`; compact spatial support in `K`; smooth `u, p`; continuous `f`; zero initial velocity; divergence-free; residual equals `f`. | None. |
| 3 | **Bound the force work.** Young/Cauchy–Schwarz gives `2∫⟨u,f⟩ ≤ ‖u‖² + ‖f‖²`; the sharper square-root form gives `∫⟨u,f⟩ ≤ ‖u‖ ‖f‖`. | `IntegratedDissipation.force_work_le` (`R3/IntegratedDissipation.lean:52`); `SpatialCauchySchwarz.work_le_sqrt_l2Sq` (`R3/SpatialCauchySchwarz.lean:22`). | Continuous slices; compact support of `u`; `‖f(t)‖²` integrable. | None. The coefficient is `1`; no Young constant is introduced. |
| 4 | **Get the sharp square-root bound.** With `E = ‖u‖²`, the identity gives `E' ≤ 2√E ‖f‖`. The proof regularizes to `√(E+ε²)`, where the derivative is `E'/(2√(E+ε²))`; since `√E ≤ √(E+ε²)` and `q ≥ 0`, that derivative is at most `q`. Integrating `(√(E+ε²))' ≤ q` from `0` where `√(0+ε²) = ε`, then letting `ε ↓ 0` with `le_of_forall_pos_le_add`, gives `√(E T) ≤ ∫ q`. | `SharpEnergyBound.sqrt_energy_le_integral` (`R3/SharpEnergyBound.lean:20`); squared form `energy_le_integral_sq` (`R3/SharpEnergyBound.lean:56`). | `T ≥ 0`; `E` continuous, nonnegative, `E(0)=0`; `q` continuous, nonnegative on the interior; interior derivative `HasDerivAt E (E' t) t`; the interior bound `E' ≤ 2√E q`. | The only coefficient is the `2` that the chain rule puts in front of `√E · q`; it is fixed by calculus, not chosen. Nothing else enters, and no `ε` survives the limit. |
| 5 | **Square and restore the dissipation.** `‖u(T)‖ ≤ F(T)`, so `‖u(T)‖² ≤ F(T)²`. Returning to the exact balance and using `F' = ‖f‖` gives the full inequality. | `IntegratedDissipation.candidate_l2Norm_le_cumulativeForceNorm` (`R3/IntegratedDissipation.lean:143`); `candidate_energy_dissipation_le` (`...:203`); identity `ForceL2Norm.integral_l2Norm_cumulative_eq_sq` (`R3/ForceL2Norm.lean:80`). | Candidate properties; `T ∈ [0,1)`; zero datum; compact support; the PDE and divergence-free clauses. | None. `F` is `cumulativeForceNorm`, the integral of the spatial `L²` norm, not a hidden constant. |
| 6 | **Pass to the singular endpoint.** Prove dissipation integrable on `[0,T]` for every `T < 1`, then exhaust the interval; the total bound follows by continuity from below. | `IntegratedDissipation.candidate_integrable_dissipation` (`R3/IntegratedDissipation.lean:73`); `candidate_total_dissipation_le` (`...:248`). | Candidate properties; `ν > 0`; the uniform energy bound and the compact-force `L²` bound. | The force bound `C` is existential (`∃ C ≥ 0` from `CompactForceBound.exists_uniform_l2sq_bound`). Only finiteness and nonnegativity are used; the dissipation bound is `(2E+C)/(2ν)`, with no smallness condition on `C`. |
| 7 | **Bundle the conclusions.** `F(1)` finite, genuine total dissipation integrability, the sharp inequality on every shorter interval, and its endpoint version. | `IntegratedDissipation.candidate_energy_estimates:279`; consumed by `R3/Theorem.lean:66` (`theorem_1_1_with_dissipation`). | One candidate at positive viscosity. | None. |

## What is not assumed

- **No pressure condition.** The pressure appears only through the term `∫⟨u, ∇p⟩`, which vanishes by compact support and `div u = 0`. No pressure decay, growth, or integrability is assumed.
- **No extra force decay.** The force is the paper's compactly supported smooth force. `F(1) < ∞` is proved from compact support and continuity, not assumed.
- **No hidden Gronwall constant.** The scalar comparison is the sharp `√E ≤ ∫‖f‖`; the coefficient in the final inequality is one. Step 4 is read, not merely named: the ε-regularization, the monotonicity `√E ≤ √(E+ε²)`, and the limit `ε ↓ 0` are visible in the proof script, and no constant is chosen anywhere in it. This is the part of the paper where the audit's constant concern does **not** bite.

## The constant audit

| Constant | Introduced by | Is its size used? |
|---|---|---|
| `E` | the candidate's `UniformFiniteEnergy` field (`R3/ProblemStatement.lean:81`) | No. Only `0 ≤ E` and finiteness. |
| `C` | `CompactForceBound.exists_uniform_l2sq_bound` (`R3/CompactForceBound.lean:25`) | No. Only `0 ≤ C` and finiteness; it bounds the force, not the conclusion. |
| `ν` | the theorem's positive-viscosity parameter | It appears explicitly in `2ν`; no numerical value is chosen. |
| coefficient `2` in `E' ≤ 2√E · q` | the derivative of `E ↦ √E` in step 4 | Yes, and it is exactly right: `(√(E+ε²))' = E'/(2√(E+ε²))`. A different coefficient would rescale the conclusion, and nothing chooses it. |
| `F(1)` | `cumulativeForceNorm f 1` | No. Finiteness is the interval-integrability conjunct, not a smallness hypothesis. |

The only inequality used is Cauchy–Schwarz/Young with coefficient one and the sharp square-root comparison. No `Classical.choose` constant appears in the final statement, and no step asks for a constant to be less than a threshold.

## Source anchors for the row names

| Declaration | Path:line |
|---|---|
| `force_work_le` | `NavierStokes/R3/IntegratedDissipation.lean:52` |
| `work_le_sqrt_l2Sq` | `NavierStokes/R3/SpatialCauchySchwarz.lean:22` |
| `energy_le_integral_sq` | `NavierStokes/R3/SharpEnergyBound.lean:56` |
| `candidate_l2Norm_le_cumulativeForceNorm` | `NavierStokes/R3/IntegratedDissipation.lean:143` |
| `candidate_energy_dissipation_le` | `NavierStokes/R3/IntegratedDissipation.lean:203` |
| `integral_l2Norm_cumulative_eq_sq` | `NavierStokes/R3/ForceL2Norm.lean:80` |
| `candidate_integrable_dissipation` | `NavierStokes/R3/IntegratedDissipation.lean:73` |
| `candidate_total_dissipation_le` | `NavierStokes/R3/IntegratedDissipation.lean:248` |
| `exists_uniform_l2sq_bound` | `NavierStokes/R3/CompactForceBound.lean:25` |
| `cumulativeForceNorm` | `NavierStokes/R3/ForceL2Norm.lean:23` |
| `theorem_1_1_with_dissipation` | `NavierStokes/R3/Theorem.lean:66` |
| `UniformFiniteEnergy` | `NavierStokes/R3/ProblemStatement.lean:81` |

## What this map establishes and what it does not

**Establishes.** A reader can follow Lemma 10.4 from the PDE to the exact inequality, and can see why the audit's "constant barrier" is not present in this lemma. The force norm is the paper's `F`, the coefficient is one, and the endpoint integrability is proved by exhaustion. The scalar comparison is now read at the proof-script level: its only coefficient is the chain-rule `2`, and there is no free constant to be small.

**Does not establish.** This is not a recompilation or an independent proof. It reads the statements, binder order, and named proof steps. The scalar comparison in step 4 was read through, but it was not recompiled; the proof terms of steps 1–3 and 5–7 were not replayed line by line.

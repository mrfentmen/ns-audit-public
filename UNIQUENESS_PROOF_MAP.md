# UNIQUENESS PROOF MAP — `classical_uniqueness_on_Icc`

**Theorem.** `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`
**Source.** `NavierStokes/R3/WholeSpaceUniqueness.lean:30`, upstream `openai/NavierStokesAndEuler@f9e8bc5`.
**Paper row.** Lemma 10.5 (`ns.txt:6143`), the comparison half of Theorem 1.1.

**Status.** This is a statement-and-consumer reading, not a recompilation and not an independent proof. Every declaration named below was read in the pinned source. I did not replay the proof term or verify the internal harmonic-functional argument line by line; the pressure-recovery chain, where the harmonic-vanishing step is the largest remaining unexpanded step, is boxed in `PRESSURE_RECOVERY_MAP.md`.

Paths beginning `R3/` are relative to `NavierStokes/`; all line numbers are into `f9e8bc5`.

## The argument in one paragraph

Take two smooth divergence-free flows on `ℝ³ × [0,T]` with the same zero initial velocity and the same Navier–Stokes residual. One flow is the constructed candidate: it is compactly supported in space and has finite energy. The other flow is an arbitrary competitor with uniformly bounded kinetic energy. Subtract them and test the difference equation against the difference times a smooth cutoff that is one on a ball of radius `R` and zero outside a ball of radius `2R`. The pressure can only be paired with the cutoff gradient, not with the velocity difference, so no pressure decay is needed. The equation then identifies that pressure pairing as a canonical Riesz functional of the velocity tensor difference. The pressure, transport, and cutoff-Laplacian terms are bounded by the weighted energy, the weighted dissipation, and the cutoff `L⁶` norm. Sobolev and Young absorb every radius-independent constant into one number `D`, leaving the differential inequality `E'(t) ≤ 2G E(t) + D/R`. Gronwall from zero initial energy gives `E(t) ≤ N/R`. As `R → ∞`, the weighted energy increases to the whole-space `L²` norm, so the norm is zero; continuity gives `u = v` everywhere. This is a genuine uniqueness argument. It is not an assumption that the competitor agrees.

## The map

| # | Step in plain words | Lean declaration / file | Hypotheses used | Constant status |
|---|---|---|---|---|
| 1 | **Subtract the two flows.** With `w = u - v` and `π = p - q`, the equal residuals cancel the force. The difference solves the linear equation with coefficients from `u` and `v`. | `NavierStokes.PeriodicUniqueness.difference_equation` (`NavierStokes/PeriodicUniqueness.lean:112`), used by `LocalizedDifferenceEnergy.difference_energy_balance` (`R3/LocalizedDifferenceEnergy.lean:102`); consumed by `classical_uniqueness_on_Icc:30`. | Both fields `C^∞` on the slab; both divergence-free; equal `navierStokesResidual` at every interior point; equal initial velocity. | None. |
| 2 | **Test against a compact cutoff.** Multiply the difference equation by `χ_R w` and integrate over `ℝ³`. `χ_R` is one on `\|x\| ≤ R` and zero outside `\|x\| ≤ 2R`. The energy estimate itself uses only this cutoff's compact support; the reference flow's compact support is a separate hypothesis of the theorem. | `LocalizedDifferenceEnergy.difference_energy_balance` (`R3/LocalizedDifferenceEnergy.lean:102`); `weightedEnergy_hasDerivAt` (`R3/LocalizedDifferenceEnergy.lean:74`); `ComparisonCutoffs.weight` (`R3/ComparisonCutoffs.lean:35`). | Smooth compactly supported cutoff; smooth spatial slices; time differentiability at an interior time. | None. `χ_R` is an explicit bump; `weight R = cutoff R ^ 8`. |
| 3 | **Never pair the pressure with the difference.** Integrate by parts to move the pressure gradient onto the cutoff: `∫ χ w·∇π = -∫ π ∇χ·w`. The pressure is tested only against a compact gradient, so no decay or global representative is required. | `LocalizedDifferenceEnergy.integral_weighted_pressure` (`R3/LocalizedTransport.lean:83`), used inside `difference_energy_balance`. | `div w = 0`; smooth `π`; compact `χ`. | None. |
| 4 | **Recover the pressure pairing from the equation.** The physical pressure-gradient pairing equals a canonical Riesz pairing of the velocity tensor difference. Recovery uses time averaging and the vanishing theorem for compactly supported harmonic functionals; it does not assume a pressure normalization. | `PressureRecovery.gradient_recovery` (`R3/PressureRecovery.lean:407`); `ActualPressureFlux.pressure_flux_eq_canonical` (`R3/ActualPressureFlux.lean:38`); `PressureFluxIdentity.pressure_flux_eq_of_gradient_identification` (`R3/PressureFluxIdentity.lean:114`). | Smooth `p, q` on the slab; same residual; divergence-free; uniform finite energy of both flows; compact spatial test only. | None. No pressure norm, decay, or growth is used. |
| 5 | **Bound the pressure flux uniformly in `R` and `t`.** The bound is `CP · ((B^(1/2)+1)(A/R+1/R^2) + R^(-7/4) B^(3/4))`, where `A` is the weighted dissipation root and `B` is the cutoff `L⁶` norm. | `PressureFlux.exists_uniform_actual_pressure_flux_bound` (`R3/PressureFlux.lean:576`). | `L²` bound on `w`, `L³` bound on `u`, `L¹` bound on `tensorDiff`, all from energy and compact support; no pressure bound. | `CP` is introduced by `∃ CP ≥ 0` after `M, U, G₀`. Any finite `CP` works; its numerical value is never used. |
| 6 | **Bound the transport and cutoff terms.** Advection against `u` is `≤ G E`; the cutoff Laplacian is `≤ (weightLaplacianConstant / R²) M²`; the cutoff transport is `≤ (8 · derivativeConstant 1 / R) M^(3/2) B^(3/2)`. The reference gradient bound `G` comes from compact support, not from a competitor hypothesis. | `LocalizedFluxEstimates.neg_coupling_le_weightedEnergy` (`R3/LocalizedFluxEstimates.lean:37`), `weight_laplacian_flux_bound` (`...:258`), `transport_flux_bound` (`...:90`); `CompactComparisonBounds.exists_gradient_bound` (`R3/CompactComparisonBounds.lean:33`). | `G` bounds `∇u`; `χ` compact; `w ∈ L²`; `v` smooth; `∇χ_R · u = 0` for all large `R`. | `derivativeConstant 1` and `weightSecondDerivativeConstant` are fixed chosen constants (`Classical.choose` of an explicit existence lemma); `weightLaplacianConstant = 3 · weightSecondDerivativeConstant`. They are independent of `R` and `t`; only positivity and finiteness are used. Their size feeds `D`, never a smallness condition. |
| 7 | **Sobolev, Young, Gronwall.** `B ≤ S (A + M/R)`; absorbing all radius-independent constants gives `E' ≤ 2G E + D/R`; Gronwall from `E(0) = 0` gives `E(t) ≤ N/R`. | `WeightedSobolev.cutoffL6_le` (`R3/WeightedSobolev.lean:237`); `ComparisonRateBound.exists_uniform_rate_bound` (`R3/ComparisonRateBound.lean:127`); `ComparisonGronwall.le_div_radius_of_deriv_le` (`R3/ComparisonGronwall.lean:105`). | Nonnegative constants; the Sobolev bound; weighted energy differentiable with the stated rate; zero initial energy. | `S = weightedSobolevConstant` is fixed. `D` is introduced by `∃ D ≥ 0` from the absorption lemma, which fixes the Young parameter at `1/2`; any finite `D` works. `N = D · T · exp(2GT)`; Lean's `C` is the `D/R` input. |
| 8 | **Let the radius go to infinity.** The weighted energy increases to the whole-space `L²` norm. A uniform `N/R` bound forces that norm to be zero; continuity gives `w = 0` pointwise. | `WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound` (`R3/WholeSpaceEnergyLimit.lean:70`); `eq_zero_of_radius_bound` (`...:53`); `integral_weight_tendsto` (`...:25`). | Square-integrable slice; continuity; zero initial energy; the `N/R` rate bound. | None beyond finite `N`; the limit is taken in `R`, not in a constant. |
| 9 | **Consume uniqueness.** The candidate agrees with every global finite-energy competitor before `t = 1`. The candidate's speed is unbounded on its compact support; a smooth global competitor is bounded there. Contradiction. | `WholeSpaceUniqueness.candidate_global_agrees_before_one` (`R3/WholeSpaceUniqueness.lean:104`); `CandidateProperties.not_global_agreement` (`R3/CandidateBreakdown.lean:18`); `no_global_solution_one` (`R3/CandidateBreakdown.lean:43`). | Candidate compact support and speed unbounded; competitor smooth on the future domain with uniform finite energy. | None. |

## What is not assumed

- **Pressure.** `PressureRecovery.Hypotheses` (`R3/PressureRecovery.lean:33`) has exactly two pressure fields, `smooth_p` and `smooth_q`; the remaining fields are the comparison hypotheses. There is no pressure assumption beyond smoothness: no `L^p` bound, no decay at infinity, no growth condition, and no pressure normalization. The only pressure input to the flux estimate is the canonical tensor pairing produced by `gradient_recovery`.
- **Competitor.** `GlobalFiniteEnergySolution` (`R3/ProblemStatement.lean:125`) contains smoothness, zero datum, divergence-freeness, the same residual, and a uniform finite-energy bound on all nonnegative times. It contains no support, periodicity, decay, derivative-growth, or pressure condition.
- **Reference energy.** The reference `u` has compact spatial support in `K`. Its finite energy and its gradient bound are *derived* by `uniformFiniteEnergy_of_compact_slab` and `exists_gradient_bound`; neither is assumed.
- **Time.** `classical_uniqueness_on_Icc` holds for every `T > 0`. The candidate application uses `T < 1`, because the candidate is only smooth before the singular time.

## The constant audit

This is the answer to the narrower question: does any step in this section depend on a constant being small, or on its numerical value being right?

| Constant | Introduced by | Is its size used? |
|---|---|---|
| `M`, `U`, `G₀` | uniform energy / compact-support bounds | No. Only nonnegativity and finiteness. |
| `CP` | `∃ CP ≥ 0` in the pressure-flux bound | No. Any finite value gives the same `1/R` rate. |
| `derivativeConstant n` | `Classical.choose` of a fixed bump-derivative bound | No. It is independent of `R` and `t`; only positivity is used. |
| `weightSecondDerivativeConstant` | `Classical.choose` of a fixed weight-derivative bound | No. Same role; it becomes part of `D`. |
| `S` | `weightedSobolevConstant` | No. A fixed multiplicative constant absorbed by Young. |
| `D` | `∃ D ≥ 0` from the absorption lemma | No. The conclusion needs only `D/R → 0`. |
| `G` | gradient bound on the compactly supported reference | No. It sets `K = 2G`; any finite `G` works. |
| `N` in `E(t) ≤ N/R` | `ComparisonGronwall.le_div_radius_of_deriv_le` (`R3/ComparisonGronwall.lean:105`) | No. `N = D · T · exp(2G·T)`; Lean's `C` is the `D/R` input. Finite for each fixed `T` and grows with `T`. That growth is why the theorem fixes `T`; it is not a smallness condition. |

**The conclusion** uses only that each constant is finite, has the required sign, and is independent of `R` and `t`. No hypothesis in this chain requires a constant to be small: `exists_uniform_rate_bound` fixes the Young parameter at `1/2` internally. No inequality asks for a constant to be less than one, greater than a threshold, or chosen for a numerical value. The only quantitative *scaling identity* used is the explicit `R^(-n)` behaviour of the cutoff derivatives, and that is *derived* in `cutoff_iteratedFDeriv_le`, not assumed.

## Source anchors for the row names

| Declaration | Path:line |
|---|---|
| `difference_energy_balance` | `NavierStokes/R3/LocalizedDifferenceEnergy.lean:102` |
| `weightedEnergy_hasDerivAt` | `NavierStokes/R3/LocalizedDifferenceEnergy.lean:74` |
| `ComparisonCutoffs.weight` | `NavierStokes/R3/ComparisonCutoffs.lean:35` |
| `integral_weighted_pressure` | `NavierStokes/R3/LocalizedTransport.lean:83` |
| `exists_gradient_bound` | `NavierStokes/R3/CompactComparisonBounds.lean:33` |
| `integral_weight_tendsto` | `NavierStokes/R3/WholeSpaceEnergyLimit.lean:25` |
| `not_global_agreement` | `NavierStokes/R3/CandidateBreakdown.lean:18` |
| `no_global_solution_one` | `NavierStokes/R3/CandidateBreakdown.lean:43` |
| `derivativeConstant` | `NavierStokes/R3/ComparisonCutoffs.lean:151` |
| `weightSecondDerivativeConstant` | `NavierStokes/R3/LocalizedFluxEstimates.lean:184` |
| `weightLaplacianConstant` | `NavierStokes/R3/LocalizedFluxEstimates.lean:237` |
| `PressureRecovery.Hypotheses` | `NavierStokes/R3/PressureRecovery.lean:33` |
| `GlobalFiniteEnergySolution` | `NavierStokes/R3/ProblemStatement.lean:125` |

## What this map establishes and what it does not

**Establishes.** A reader can follow the uniqueness half without Lean: each step names the declaration that performs it, the hypotheses it consumes, and the constants it introduces. Within this section, the audit's "constant barrier" observation has a sharp answer: the constants are existential or chosen, but the proof never uses their values.

**Does not establish.** This is not a recompilation, not a re-proof, and not evidence of a mathematical defect. It reads the statements, binder order, and named proof steps. The internal proof of `gradient_recovery` — the time-averaging and harmonic-functional machinery — is named but not expanded here. A wrong proof term inside one of these declarations would not be caught by this map.

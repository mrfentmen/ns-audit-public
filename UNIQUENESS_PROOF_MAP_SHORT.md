# UNIQUENESS, IN TWO PAGES

**Theorem.** `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`
**Source.** `NavierStokes/R3/WholeSpaceUniqueness.lean:30`
**Upstream.** `openai/NavierStokesAndEuler@f9e8bc5`
**Paper.** Lemma 10.5 (`ns.txt:6143`), the comparison half of Theorem 1.1.

**Read this first.** This is the front door. The detailed nine-row map is `UNIQUENESS_PROOF_MAP.md`; its 5-page landscape PDF is the appendix. The energy estimate is in `ENERGY_PROOF_MAP.md`; the pressure-recovery chain is in `PRESSURE_RECOVERY_MAP.md`. Each checkpoint keeps its central anchor; full anchors are in the appendix.

**Plain terms.** A *cutoff* is a smooth radius cap. *Dissipation* is viscous energy loss. A *Riesz functional* is a pairing represented by an inner product. *Gronwall* is the one-dimensional comparison lemma that turns a differential inequality into a bound. *Sobolev* bounds a function's size by its gradient's size; *Young* splits a product so one part can be absorbed. `L⁶` is the standard sixth-power norm.

## The whole argument

Suppose two smooth divergence-free flows on `ℝ³ × [0,T]` have the same zero initial velocity and the same Navier–Stokes residual. One is the constructed candidate: compactly supported in space and finite-energy. The other is an arbitrary competitor with uniformly bounded kinetic energy. Subtract them and test the difference equation against the difference times a smooth cutoff (a radius cap) that is one on `|x| ≤ R` and zero outside `|x| ≤ 2R`. The pressure can only be paired with the cutoff gradient, not with the velocity difference. The equation then identifies that pressure pairing as a canonical Riesz functional of the velocity tensor difference (a pairing represented by an inner product). The pressure, transport, and cutoff-Laplacian terms are bounded by the weighted energy (energy with a radius weight), the weighted dissipation (viscous energy loss), and the cutoff `L⁶` norm. Sobolev and Young estimates absorb every radius-independent constant into one `D`, leaving `E'(t) ≤ 2G E(t) + D/R`. Gronwall's comparison lemma, from zero initial energy, gives `E(t) ≤ N/R`. As `R → ∞`, the weighted energy increases to the whole-space `L²` norm, so the norm is zero; continuity gives `u = v` everywhere.

## Seven checkpoints

1. **Subtract and test.** `w = u - v`, `π = p - q`; equal residuals cancel the force. The difference solves the linear equation with coefficients from `u` and `v`. The localized energy identity is `LocalizedDifferenceEnergy.difference_energy_balance` (`NavierStokes/R3/LocalizedDifferenceEnergy.lean:102`).

2. **Move the pressure onto the cutoff.** `∫ χ w·∇π = -∫ π ∇χ·w` is `LocalizedDifferenceEnergy.integral_weighted_pressure` (`NavierStokes/R3/LocalizedTransport.lean:83`). Only the cutoff is compact; the pressure is never paired with `w` itself. No pressure decay is used.

3. **Recover the pressure pairing from the equation.** `PressureRecovery.gradient_recovery` (`NavierStokes/R3/PressureRecovery.lean:407`) proves the physical gradient pairing equals the canonical Riesz pairing. Compact integration by parts then turns that pairing into the cutoff pressure flux.

4. **Bound the pressure flux.** `PressureFlux.exists_uniform_actual_pressure_flux_bound` (`NavierStokes/R3/PressureFlux.lean:576`) gives `CP · ((B^(1/2)+1)(A/R + 1/R²) + R^(-7/4) B^(3/4))`, with `A` the weighted dissipation root and `B` the cutoff `L⁶` norm. `CP` is existential; only finiteness is used.

5. **Bound the other terms.** `LocalizedFluxEstimates.neg_coupling_le_weightedEnergy` (`NavierStokes/R3/LocalizedFluxEstimates.lean:37`) gives the advection bound `≤ G E`. The other cutoff bounds are in the appendix. The reference gradient `G` comes from compact support, not from a competitor hypothesis.

6. **Sobolev, Young, Gronwall.** The cutoff Sobolev bound and the absorption lemma turn the estimates into `E' ≤ 2G E + D/R`; `ComparisonGronwall.le_div_radius_of_deriv_le` (`NavierStokes/R3/ComparisonGronwall.lean:105`) then gives `E(t) ≤ N/R`, with `N = D · T · exp(2G · T)`. The numerator grows with `T`; it is finite for each fixed `T`. That is why the theorem fixes `T` and why the candidate application only uses `T < 1`.

7. **Let `R → ∞` and consume uniqueness.** `WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound` (`NavierStokes/R3/WholeSpaceEnergyLimit.lean:70`) forces `u = v`. `candidate_global_agrees_before_one` then gives agreement before time one. `CandidateProperties.not_global_agreement` and `no_global_solution_one` turn that into the contradiction: the candidate's speed is unbounded on its compact support, while a smooth global competitor is bounded there.

## What is not assumed

- **Pressure.** In `PressureRecovery.Hypotheses` (`NavierStokes/R3/PressureRecovery.lean:33`), the only pressure fields are `smooth_p` and `smooth_q`. There is no pressure assumption beyond smoothness: no `L^p` bound, decay, growth, or normalization.
- **Competitor.** `GlobalFiniteEnergySolution` (`NavierStokes/R3/ProblemStatement.lean:125`) contains smoothness, zero datum, divergence-freeness, the same residual, and uniform finite energy. It contains no support, periodicity, decay, derivative-growth, or pressure condition.
- **Reference energy.** The reference flow's finite energy and gradient bound are derived from compact support, not assumed.

## The constant audit

| Constant | Status | Does its size matter? |
|---|---|---|
| `CP` | `∃ CP ≥ 0` in the pressure-flux bound | No. Any finite value gives the same `1/R` rate. |
| `derivativeConstant`, `weightSecondDerivativeConstant` | `Classical.choose` of fixed bump/weight derivative bounds (`NavierStokes/R3/ComparisonCutoffs.lean:151`, `NavierStokes/R3/LocalizedFluxEstimates.lean:184`) | No. They are independent of `R` and `t`; only positivity and finiteness are used. |
| `D` | `∃ D ≥ 0` from the absorption lemma | No. The conclusion needs only `D/R → 0`. |
| `N = D · T · exp(2G · T)` (`N`, written `C` in `le_div_radius_of_deriv_le`) | derived Gronwall numerator | No. It is finite for each fixed `T` and grows with `T`. It is large but harmless; no smallness condition is imposed. |

**The conclusion** uses only that each constant is finite, has the required sign, and is independent of `R` and `t`. That independence is the content: `CP`, `D`, and `G` may depend on the viscosity `ν`, the reference flow, and the fixed data; the claim is not that they are universal. No hypothesis in this chain requires a constant to be small: the absorption step fixes its Young parameter at `1/2` internally. The only quantitative scaling identity used is the derived `R^(-n)` behavior of the cutoff derivatives.

## What this is not

This is a statement-and-consumer reading, not a recompilation or independent proof. It reads declarations, binder order, and named proof steps; it does not replay proof terms. No mathematical defect is claimed.

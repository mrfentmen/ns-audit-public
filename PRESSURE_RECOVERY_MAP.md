# PRESSURE RECOVERY MAP — inside `gradient_recovery`

**Theorem.** `NavierStokesR3.PressureRecovery.gradient_recovery`
**Source.** `NavierStokes/R3/PressureRecovery.lean:407`, upstream `openai/NavierStokesAndEuler@f9e8bc5`.
**Role.** This is the internal chain behind step 4 of `UNIQUENESS_PROOF_MAP.md`: it turns the actual pressure-gradient pairing into a canonical Riesz pairing of the velocity tensor difference.

**Status.** Statement-and-consumer reading, not a recompilation. I read the declarations and the named proof steps; I did not replay the harmonic-functional proof term.

## The argument in one paragraph

The pressure is never differentiated globally and never assumed to decay. Test the difference equation against a compact smooth scalar function. Integration by parts moves the Laplacian onto the test, moves the tensor divergence onto the test, and leaves the pressure gradient paired with the compact test. Replacing the test by one more derivative gives the differentiated Poisson identity. Average that identity over time against a smooth cutoff supported strictly inside the slab. The averaged physical-minus-canonical pressure functional is then harmonic: it annihilates the Laplacian of every compact test. Its velocity and tensor coefficients give a uniform Fourier `H³` bound, so it has a weighted `L²` representative. A compactly supported harmonic functional with such a representative vanishes, because the only harmonic distribution supported at the origin is zero and Lebesgue volume has no atom there. Removing the time average with the distributional fundamental lemma recovers the gradient identity at every interior time. Compact integration by parts then identifies the actual cutoff pressure flux with the canonical Riesz pairing.

## The map

| # | Step in plain words | Lean declaration / file | Hypotheses used | Constant status |
|---|---|---|---|---|
| 1 | **Test the difference equation against a compact scalar function.** Move the Laplacian and tensor divergence onto the test; the pressure is paired only with a compact test. | `ConservativeDifference.weak_pressure_gradient` (`R3/ConservativeDifference.lean:223`); slab form `weak_pressure_gradient_on_slab:281`. | Smooth spatial slices; both divergence-free; equal residual; compact smooth test. | None. |
| 2 | **Differentiate the pressure Poisson identity.** Replace the test by `∂ₖψ`; the result is `∫ ∂ₖπ Δψ = Σᵢⱼ ∫ Tᵢⱼ ∂ᵢ∂ⱼ∂ₖψ`. | `PressureRecoveryHelpers.gradient_poisson_test` (`R3/PressureRecoveryHelpers.lean:116`), using `ConservativeDifference.weak_pressure_poisson:431`. | Same as step 1, plus the differentiated compact test; no pressure normalization. | None. |
| 3 | **Average over time.** Integrate against a smooth temporal cutoff `a` supported in `(0,T)`; Fubini moves `a` inside the compact spatial pairing. | `PressureRecovery.averaged_gradient_poisson` (`R3/PressureRecovery.lean:188`) and `averaged_gradient_poisson_complex:229`; `averaged_value_realTest:173`. | `a` smooth and compactly supported in `(0,T)`; the slab hypotheses of step 1. | None. |
| 4 | **The averaged functional is harmonic.** The physical pairing and the tensor pairing have the same Laplacian test, so their difference annihilates `Δψ` for every compact real `ψ`. | `PressureRecovery.averaged_value_real_harmonic:259`. | The two Poisson identities of steps 2–3; compact test. | None. |
| 5 | **Kill the compact harmonic functional.** The coefficients give a uniform Fourier `H³` bound. The functional is represented in weighted `L²`; a harmonic representative vanishes, and volume has no atom at the origin. | `PressureFunctionals.averagedPressureDifference_bound` (`R3/PressureFunctionals.lean:279`); `PressureRecoveryHelpers.compact_harmonic_of_real:101`; `HarmonicTestFunctionals.eq_zero_of_compact_harmonic:100`; `PressureRecovery.averaged_value_zero:286`. | `L²` averages of the velocity difference; integrable averaged tensor; compact real tests. | `C` is introduced by `∃ C ≥ 0` in the `H³` bound. Only finiteness and nonnegativity are used; its size is never compared to another constant. |
| 6 | **Remove the time average.** If every compact temporal test annihilates a continuous function on `(0,T)`, the function is zero at every interior time. | `PressureRecovery.time_test_gradient_difference_zero:353`; `TemporalTestUniqueness.eq_zero_on_Ioo_of_setIntegral_tests` (`R3/TemporalTestUniqueness.lean:40`); `gradient_recovery_complex:391`. | Continuity on the interior; the set-integral test identity; compact temporal tests. | None. |
| 7 | **Recover the gradient and the flux.** The physical gradient pairing equals the canonical Riesz pairing; compact integration by parts turns that pairing into the actual cutoff pressure flux. | `PressureRecovery.gradient_recovery:407`; `PressureFluxIdentity.pressure_flux_eq_of_gradient_identification` (`R3/PressureFluxIdentity.lean:114`); `ActualPressureFlux.pressure_flux_eq_canonical` (`R3/ActualPressureFlux.lean:38`). | Same slab hypotheses; compact spatial test or cutoff. | None. |

## What this chain does not assume

- **No pressure decay, growth, or global integrability.** The pressure appears only in compact spatial pairings. The proof recovers the gradient from the equation; it does not choose a pressure representative at infinity.
- **No pressure normalization.** The canonical pairing is built from `tensorDiff u v` and the divergence-free condition, not from a chosen mean or a boundary condition.
- **No competitor support.** Only the compactness of the test (or the cutoff) is used. The velocities and pressures may be arbitrary smooth fields on the slab.

## The constant audit

| Constant | Introduced by | Is its size used? |
|---|---|---|
| `C` in `averagedPressureDifference_bound` | `∃ C ≥ 0` from the Fourier `H³` estimate | No. It bounds the functional; any finite value gives the same representative and the same zero conclusion. |
| Fourier weight `(1 + ‖ξ‖²)²` | `FourierSobolevWeights` | Fixed by the `H³` norm, not chosen for smallness. |

## What this map establishes and what it does not

**Establishes.** The uniqueness argument's pressure step is not a black box and not a decay assumption. It is a six-stage recovery: compact weak identity, differentiated Poisson identity, time average, harmonicity, harmonic-functional vanishing, and un-averaging. The audit's claim that no pressure decay is used has a declaration-level answer.

**Does not establish.** This is not a recompilation or an independent proof of the harmonic-functional theorem. It reads the statements and the proof structure. The Fourier representation and the compact-support approximation inside `eq_zero_of_compact_harmonic` are named, not expanded.

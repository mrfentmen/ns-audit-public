# PRESSURE RECOVERY MAP — inside `gradient_recovery`

**Theorem.** `NavierStokesR3.PressureRecovery.gradient_recovery`
**Source.** `NavierStokes/R3/PressureRecovery.lean:407`
**Upstream.** `openai/NavierStokesAndEuler@f9e8bc5`
**Role.** This is the internal chain behind step 4 of `UNIQUENESS_PROOF_MAP.md`. It is the largest remaining unexpanded step in the uniqueness chain.

**Status.** Statement-and-consumer reading, not a recompilation. I read the declarations and the named proof steps; I did not replay the harmonic-functional proof term.

## The argument in one paragraph

The pressure is never differentiated globally and never assumed to decay. Test the difference equation against a compact smooth scalar function. Integration by parts moves the Laplacian onto the test, moves the tensor divergence onto the test, and leaves the pressure gradient paired with the compact test. Replacing the test by one more derivative gives the differentiated Poisson identity. Average that identity over time against a smooth cutoff supported strictly inside the slab. The averaged physical-minus-canonical pressure functional is then harmonic: it annihilates the Laplacian of every compact test. Its velocity and tensor coefficients give a uniform Fourier `H³` bound, so it has a Hilbert-space representative in weighted `L²` on the Fourier side. The compact-test hypothesis is first upgraded to all Schwartz tests; the representative then vanishes. Removing the time average with the distributional fundamental lemma recovers the gradient identity at every interior time. Compact integration by parts then identifies the actual cutoff pressure flux with the canonical Riesz pairing.

## The map

Paths are relative to the repository's `NavierStokes/` directory.

| # | Step in plain words | Lean declaration / file | Hypotheses used | Constant status |
|---|---|---|---|---|
| 1 | **Test the difference equation against a compact scalar function.** Move the Laplacian and tensor divergence onto the test; the pressure is paired only with a compact test. | `ConservativeDifference.weak_pressure_gradient` (`R3/ConservativeDifference.lean:223`); slab form `weak_pressure_gradient_on_slab` (`R3/ConservativeDifference.lean:281`). | Smooth spatial slices; both divergence-free; equal residual; compact smooth test. | None. |
| 2 | **Differentiate the pressure Poisson identity.** Replace the test by `∂ₖψ`; the result is `∫ ∂ₖπ Δψ = Σᵢⱼ ∫ Tᵢⱼ ∂ᵢ∂ⱼ∂ₖψ`. | `PressureRecoveryHelpers.gradient_poisson_test` (`R3/PressureRecoveryHelpers.lean:116`), using `ConservativeDifference.weak_pressure_poisson` (`R3/ConservativeDifference.lean:431`). | Same as step 1, plus the differentiated compact test; no pressure normalization. | None. |
| 3 | **Average over time.** Integrate against a smooth temporal cutoff `a` supported in `(0,T)`; Fubini moves `a` inside the compact spatial pairing. | `PressureRecovery.averaged_gradient_poisson` (`R3/PressureRecovery.lean:188`) and `averaged_gradient_poisson_complex` (`R3/PressureRecovery.lean:229`); `averaged_value_realTest` (`R3/PressureRecovery.lean:173`). | `a` smooth and compactly supported in `(0,T)`; the slab hypotheses of step 1. | None. |
| 4 | **The averaged functional is harmonic.** The physical pairing and the tensor pairing have the same Laplacian test, so their difference annihilates `Δψ` for every compact real `ψ`. | `PressureRecovery.averaged_value_real_harmonic` (`R3/PressureRecovery.lean:259`). | The two Poisson identities of steps 2–3; compact test. | None. |
| 5 | **Upgrade compact tests, then kill the representative.** The coefficients give a uniform Fourier `H³` bound. Compact-test harmonicity is upgraded to all Schwartz tests by density; the weighted-`L²` representative then vanishes, because volume has no atom at the origin. | `PressureFunctionals.averagedPressureDifference_bound` (`R3/PressureFunctionals.lean:279`); `PressureRecoveryHelpers.compact_harmonic_of_real` (`R3/PressureRecoveryHelpers.lean:101`); `HarmonicTestFunctionals.eq_zero_of_compact_harmonic` (`R3/HarmonicTestFunctionals.lean:100`); `PressureRecovery.averaged_value_zero` (`R3/PressureRecovery.lean:286`). | `L²` averages of the velocity difference; integrable averaged tensor; compact real tests. | `C` is introduced by `∃ C ≥ 0` in the `H³` bound. Only finiteness and nonnegativity are used; its size is never compared to another constant. |
| 6 | **Remove the time average.** If every compact temporal test annihilates a continuous function on `(0,T)`, the function is zero at every interior time. | `PressureRecovery.time_test_gradient_difference_zero` (`R3/PressureRecovery.lean:353`); `TemporalTestUniqueness.eq_zero_on_Ioo_of_setIntegral_tests` (`R3/TemporalTestUniqueness.lean:40`); `PressureRecovery.gradient_recovery_complex` (`R3/PressureRecovery.lean:391`). | Continuity on the interior; the set-integral test identity; compact temporal tests. | None. |
| 7 | **Recover the gradient and the flux.** The physical gradient pairing equals the canonical Riesz pairing; compact integration by parts turns that pairing into the actual cutoff pressure flux. | `PressureRecovery.gradient_recovery` (`R3/PressureRecovery.lean:407`); `PressureFluxIdentity.pressure_flux_eq_of_gradient_identification` (`R3/PressureFluxIdentity.lean:114`); `ActualPressureFlux.pressure_flux_eq_canonical` (`R3/ActualPressureFlux.lean:38`). | Same slab hypotheses; compact spatial test or cutoff. | None. |

## Box: the harmonic-vanishing step

This is the step that was previously left unexpanded. **The idea.** A harmonic functional bounded by a Fourier `H³` norm has a Hilbert-space representative `q` in weighted `L²` on the Fourier side. Harmonicity says `‖ξ‖² q = 0`. The origin has measure zero, so `q = 0` almost everywhere, hence `F = 0`. No polynomial argument is needed, and no compact support is assumed on `F`; “compact” refers to the test functions.

**What the Lean code does.** It does not introduce a separate distribution API. It works with `ComplexTest`, the Schwartz space, and the weighted Fourier embedding `B`. The upgrade from compact tests to all Schwartz tests happens first, by density; the representative vanishes second.

1. `averagedPressureDifference_bound` (`R3/PressureFunctionals.lean:279`) gives `∃ C ≥ 0` such that `‖F ψ‖ ≤ C · sqrt (fourierHNormSq 3 ψ)` for every Schwartz test `ψ`.
2. `eq_zero_of_compact_harmonic` (`R3/HarmonicTestFunctionals.lean:100`) is the entry point. Its hypothesis is harmonicity only on compactly supported tests. `SchwartzCompactApproximation.continuous_zero_of_compactSupport` (`R3/SchwartzCompactApproximation.lean:213`) upgrades that hypothesis to all Schwartz tests, but it requires continuity of `ψ ↦ F(Δψ)`. The `H³` bound supplies that continuity: `continuous_of_fourierHNormSq_bound` (`R3/HarmonicTestFunctionals.lean:42`) turns `hbound` into continuity of `F`, which is composed with `laplacianCLM.continuous`. After the upgrade the lemma calls `eq_zero_of_harmonic` (`R3/HarmonicTestFunctionals.lean:84`).
3. `eq_zero_of_harmonic` applies `exists_inner_representation_of_fourierHNormSq_bound` (`R3/HarmonicTestFunctionals.lean:29`), which turns the `H³` bound into a Hilbert-space representative `q` in weighted `L²` on the Fourier side, with `F ψ = ⟪q, B ψ⟫`.
4. `representative_eq_zero_of_harmonic` (`R3/HarmonicTestFunctionals.lean:53`) tests `q` against Fourier transforms. Harmonicity leaves the factor `‖ξ‖²`; `WeakFourierUniqueness.eq_zero_of_integral_weight_normSq_test_eq_zero` (`R3/WeakFourierUniqueness.lean:75`) proves `q = 0` in `L²`. The key point is that Lebesgue volume has no atom at the origin. With `q = 0`, the representation gives `F = 0`, which `eq_zero_of_harmonic` returns to the compact-test lemma.

**Which parts are classical, which are Lean-specific.** The Fourier-multiplier argument and the fact that `‖ξ‖² q = 0` forces `q = 0` almost everywhere are classical. The Lean-specific bookkeeping is the choice of `ComplexTest` as Schwartz space, the weighted Fourier embedding `B`, the Hilbert-space representative `q` in weighted `L²` on the Fourier side, and the cutoff approximation that upgrades compact-test harmonicity to all Schwartz tests. No distribution theory beyond this is assumed.

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

**Establishes.** The uniqueness argument's pressure step is not a decay assumption. It is a seven-stage recovery: compact weak identity, differentiated Poisson identity, time average, harmonicity, harmonic-functional vanishing, un-averaging, and flux identification. The audit's claim that no pressure decay is used has a declaration-level answer.

**Does not establish.** This is not a recompilation or an independent proof of the harmonic-functional theorem. It reads the statements and the proof structure. The weighted Fourier representation and the compact-support approximation are named, not expanded line by line.

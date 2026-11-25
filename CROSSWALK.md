# CROSSWALK — the paper against the Lean development

**Status: first pass complete, second pass under way.** Section level throughout, plus two
slices of result-level mapping. Read the limits at the bottom before quoting anything here.

## What this file is for

OpenAI published the prose account alongside the formalization: *Finite time blowup for
Navier–Stokes*, 166 pages, linked from the repository's own README and named as the source
in `formalization.yaml`. The Lean tree is the machine-checked version of it — 816 modules,
429,279 lines under `NavierStokes/`.

Until now the audit checked two things: the **statements** (E76 against Fefferman's Clay
text, E80 for the Euler pair, E81/E82 for the Euler clauses) and a few **proof slices** by
reading (E67–E71, E85, E86, and the pressure-flux section of `LEADS.md`). Nothing joined the
paper's own argument to the modules that discharge it. That is what this table starts.

## Basis labels

Every row is tagged with what backs the mapping. The distinction matters, because two of the
three tags are much weaker than the first.

- **cited** — a Lean file names the paper's section number in a docstring. Strong; the
  author of the file asserted the correspondence.
- **object** — the module defines the object the section is about, or proves its headline
  statement, by name and docstring. Medium; the correspondence is obvious but not asserted.
- **family** — a module family covering the same subject. Weak; the specific correspondence
  has not been checked.

## The map

| Paper | Pages | What the section does | Lean modules | Basis |
|---|---|---|---|---|
| 1. Introduction | 1–3 | Theorem 1.1, history, alternative (C)/(D) | `R3/ProblemStatement`, `R3/Theorem`, `ComparatorBridge`, `ComparatorDefinitions` | object |
| 2. Physical description | 3–6 | inner core, annulus and pulses, exterior flow | `OutgoingProfile`, `OutgoingEntranceCone`, `OutgoingNegativeSlopeCone`, `BaseExterior`, `AxisProfile` | family |
| 3. Proof outline | 6–24 | concentrating leading field; background stress in four compatibility steps; oscillations and momentum transport; correction and summation; localization; notation | `ExponentLedger` (§8.1, §10.2 cited), `SeedConePaper`, `FiveRowRank`, `ActualCandidateAssembly` | cited + object |
| 4. Constructing the leading order flow | 24–45 | similarity variables, radial integration of the residual, cumulative integrals, cone on the leading stress, profile properties | `RadialSchedule` (§4.4 cited), `FlatCutoff` (§4.6 cited), `LeadingStress`, `NominalProfile`, `InitialPhysicalData` | cited |
| 5. Correcting the base flow | 45–62 | higher coefficients near the axis, cancelling total radial residual integrals, coefficient induction, divergence-preserving summation, realized base field | `CorrectionStep`, `CorrectionInitialization`, `CorrectionInitializationNoOptions`, `BaseResidual`, the 21 `Axis*` modules | object |
| 6. Auxiliary torus | 62–73 | dyadic charts, slow cutoffs, disjoint auxiliary rectangles, coefficient bounds | `PhysicalGraphBounds`, `LabelSumBounds`, `InitialDyadicSource`, `GraphRestriction`, `MixedPeriodicAssembly` | object |
| 7. Oscillatory realization | 73–88 | phase and orthogonal frame, pulse equation, covariance and its linearization, exact curls and retained tails | `PulseAmplitude`, `PrimaryPulseBounds`, `Covariance`, `SmoothCovariance`, `SignedCovariance` (§10.2 cited), `ErrorHarmonics`, `CurrentSignedCurl` | object |
| 8. Compactly supported mean corrections | 88–100 | conservative momentum equations, pressure reconstruction, three compatibility defects, auxiliary-time inversion, five-moment correction, chart recomputation | `GraphCalculus` (§8.1 cited), `GaussianTailFlat` (§8.2 cited), `MomentRepairPicard`, `FiveRowRank`, `PowerMomentMatrix`, `AngularMomentReset`, `MeanRankUpdate`, `ActualMeanExterior` | cited |
| 9. Residual improvement and the local field | 100–116 | residual estimates for curl-built velocities, retained sources and errors, iteration, local field | `ActualCycleResidualBounds`, `ActualBaseResidual`, `LocalResidualFlatness`, `JointResidualLimits`, `CandidateFromLimits`, `LocalPaperTheorem` | object |
| 10. Compact forcing and breakdown | 116–126 | compact forcing, local-to-global, Theorem 1.1, Corollary 10.6 (periodic) | `R3CompactCandidate`, `R3/PositiveTimeForce`, `R3/CandidateBreakdown`, `R3/WholeSpaceComparisonClosure`, `R3/Theorem`, the `Periodic*` family | object |
| A. Radial moments and the heat exterior | 126–144 | matching radial moments, constructing the heat exterior; Proposition A.4 | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential`, `PowerMomentMatrix` | object |
| B. Analytic profiles near the axis | 144–157 | analytic profiles and their continuation; Proposition B.2, Corollary B.10 | `AxisProfile`, `AxisAnalyticCoefficients`, `AxisAnalyticRadialSeries`, `AxisHolomorphic`, `AxisSeries`, `AxisContraction` | object |
| C. The admissible stress cone | 157–165 | realising the cone; Proposition C.2 | `ActivationCone`, `OutgoingNegativeSlopeCone`, `AlignedProfileSpectralCone`, `MatchingConeBounds` | object |

## What the paper's own outline names, and where it lands

Section 3.2 asks for four compatibility results, and names them. That is the cleanest spine
the paper offers, so it is worth recording separately:

| Paper's step | Paper's result | Lean side | Basis |
|---|---|---|---|
| exterior and axis pressure | Proposition A.4 | `AppendixHeatResults`: `rising`, `derivativeCoeff_eq_rising`, `gamma_add_nat`, `endpoint_derivatives`, `uniform_positive_derivative_bound` | object, declarations checked |
| inner solution | Proposition B.2 | `AxisProfile`: `radialOperatorCoeff`, `radialOperator_inverse`, `profileCoeff_recurrence`, `profileCoeff_scaled_equation`, `weighted_profileCoeff` | object, declarations checked |
| joining and moment matching | Corollary B.10 | `AxisSeries`: `bessel`, `bessel_eq_constant_add_tail`, `hasDerivAt_bessel`; `PowerMomentMatrix`: `powerEvaluationMatrix_det_ne_zero`, `expSum_coefficients_zero`, `exists_ordered_derivative_zeros` | object, declarations checked |
| enforcing the cone condition | Proposition C.2 | `MatchingConeBounds`: `shapeModel_uniform_lower`, `true_collar_of_errors`, `actual_shape_source_threshold`; `ActivationCone`: `ramp_cone_of_errors`, `errorTolerance_bounds`, `activation_uniform_collar` | object, declarations checked |

Those four rows are no longer name matches. The declarations are the right *kind* of
object for the step they are under: Pochhammer-type rising coefficients and derivative
endpoint bounds for the radial-moment problem; a proved inverse of the radial operator and
a coefficient recurrence for the inner profiles; Vandermonde nonsingularity and exponential
moment vanishing for the joining problem; collar and ramp bounds for the cone. What is still
missing is the clause-by-clause match — that each paper hypothesis appears as a Lean binder
and each Lean hypothesis is one the paper grants.

Section 3.4 lists four construction steps — solve the inhomogeneous wave-amplitude
equations, correct the angular average with zero auxiliary average, solve the five radial
moment equations of (8.25), then sum. The third is `FiveRowRank` (the file's own docstring:
"the five linear rows of the manuscript"), and the second is the `MeanRankUpdate` /
`AngularMomentReset` family. The first is the `PulseAmplitude` / `PrimaryPulseBounds` family.

## Explicit section citations found in the source

Five, and no more:

- `RadialSchedule.lean:76` — "Section 4.4"
- `FlatCutoff.lean:25` — "Section 4.6"
- `GraphCalculus.lean:141` — "§8.1"; also `ExponentLedger.lean:14`
- `GaussianTailFlat.lean:11` — "Section 8.2"
- `Covariance.lean:206` — "Section 8.3"; `SignedCovariance.lean:384` — "Section 10.2"

`ExponentLedger.lean:14` also records the paper's numeric choice: `κ = 10⁻⁵` fixed in §8.1
and again in §10.2, with the ledger proved uniformly for `0 ≤ κ ≤ 10⁻⁵` and `σ ≥ 1/5`, in
exact rationals.

## What is already checked, and where

- **Statements.** E76 (Clay (C) and (D), clause by clause, against Fefferman); E80 (Euler
  statements are the repository's own); E81/E82 (the two Euler clauses that drift from the
  paper's prose).
- **Proof, by reading.** E67–E71 (the stage-estimate chain down to the source wave class);
  E85 and E86 (periodic uniqueness and the integration-by-parts layer under it); `LEADS.md`
  §4 (the pressure-flux interface and bodies, closed).
- **Proof, everything else.** Not read at lemma level. Not one estimate inside the Euler
  development has been read at all.

## The gap this table exposes

The paper has numbered propositions and lemmas — A.4, B.2, B.10, C.2, 5.3, 9.1, and the
rest. The development has 816 modules. Nothing yet establishes that the paper's results map
one-to-one onto Lean declarations, or that no paper lemma is missing from the formalization.
That is the remaining job, and it is where a defect would hide if one exists: not in the
kernel, which has been checked, but in the distance between the argument as written and the
argument as formalized.

## Method for the next pass

For each numbered result in the paper: extract its statement; locate the Lean declaration by
object and conclusion shape; check the hypotheses clause by clause; record the pair as
`paper page → file:line`; and record the ones that cannot be found rather than omitting them.
At one section per day that is about two weeks for the Navier–Stokes paper, longer if the
unfound ones turn out to be real.

## Pass two, slice one: the paper's own labels are in the source

The paper uses internal labels (`heat:exterior`, `outgoing:moment-rank`, `seed:cone-test`,
...). Twenty of them appear verbatim in Lean docstrings. That is a much stronger anchor
than a section number: the file asserts, in its own words, that it is about that named
result. These are the only places where the correspondence is claimed by the development
rather than inferred by us.

| Paper label | Lean file:line |
|---|---|
| `axis:exit` | `NaturalExitBounds.lean:152` |
| `axis:model-positive` | `AxisModelBounds.lean:7` |
| `axis:model-series` | `AxisModelBounds.lean:6` |
| `geom:counting-bounds` | `LabelCounting.lean:147`, `:170` |
| `geom:label-counts` | `LabelCounting.lean:257` |
| `global:kernel-bound` | `R3PressureKernel.lean:112` |
| `global:localization` | `PaperLocalization.lean:10` |
| `heat:exterior` | `AppendixHeatResults.lean:4` |
| `heat:flat-primitive` | `FlatPrimitivePaper.lean:74` |
| `heat:small-argument` | `AppendixHeatResults.lean:141` |
| `iter:physical-loss` | `WholeDomainPhysicalStageTheorem.lean:150` |
| `join:reference` | `ReferenceUniformStocks.lean:412` |
| `join:scale-envelope` | `ReferenceEndpointRate.lean:273` |
| `outgoing:moment-rank` | `ExponentialMomentMatrix.lean:6`, `SmoothExponentialMomentMatrix.lean:7` |
| `outgoing:steering` | `ClosedIntervalCkOperators.lean:254` |
| `seed:cone-coordinates` | `SeedConePaper.lean:6` |
| `seed:cone-test` | `SeedConePaper.lean:36`, `:46` |
| `seed:profile-comparison` | `SeedHandbackJets.lean:353` |
| `sum:realization` | `GenericSummationRealization.lean:70` |

Twenty-two occurrences, twenty distinct labels. Fourteen further paper sections carry no
label citation at all.

## Two results placed at declaration level

These are the first rows where the *statement* was checked, not just the module name.

**Lemma 4.7** ("let $\alpha_1,\dots,\alpha_m$ be distinct real numbers ...", the
non-singular moment system). Placed on `PowerMomentMatrix`:
`expSum_coefficients_zero` (an exponential sum vanishing at $n$ ordered nodes has zero
coefficients), `expEvaluationMatrix\_det\_ne\_zero` (distinct exponents, ordered nodes),
and `powerEvaluationMatrix\_det\_ne\_zero` for the real-exponent case. The integrated form
is `ExponentialMomentMatrix.expIntervalMomentMatrix\_det\_ne\_zero`, whose own docstring
names the paper's clause `outgoing:moment-rank` and drops the sign restriction on the
endpoints. That is the lemma's content, clause for clause: distinctness becomes
`Function.Injective a`, the matrix is the same matrix, and the conclusion is
determinant-nonzero rather than "solvable", which is equivalent given the repair
construction below it.

**Section 8.6** (the five-dimensional correction of the moment constraints). Placed on
`FiveProfileMoments`, whose module docstring reads "Five actual profile moments on a
reserved positive patch", and on `MomentRepair`: `momentMatrix`, `coefficients`,
`coefficients_unique`, `repair`. `FiveProfileMoments` builds the five bumps (two axial,
three angular) in disjoint halves of the patch; `MomentRepair` is the general invertible
system that consumes them. `FiveRowRank` supplies the rank statement the paper's rows
need.

## Pass two, slice two: the paper as text, and a denominator that was wrong

The 166-page paper had been read in a viewer. It is now extracted to text in the
gitignored `.setup/paper/ns.txt` (`pypdf`, 166 pages, 485,170 characters, the PDF's own
page markers kept), so every row below can cite a page.

The first thing that changed is the count. E89 and E90 said "57 numbered results".
Counting distinct `(kind, number)` labels at line start gives **74** — 3 theorems, 26
propositions, 38 lemmas, 7 corollaries — 73 of which have at least one
statement-length occurrence. The 57 was a rough figure that was never checked against
the text. It is withdrawn, and the ledger below uses 74.

### Placed (one)

**Corollary 10.6**, p. 125. `PeriodicPaper.breakdownStatement` and `periodic_corollary`
(`PeriodicPaperTheorem.lean:148,155`): for every `ν > 0` a velocity, pressure and force
satisfying `CandidateProperties` — smooth on `preSingularDomain`, periodic on the cube,
compact spatial support inside `fundamentalInterior`, zero initial velocity,
divergence-free, residual equal to the force, `SpeedUnboundedAtOne` — together with
`¬ Nonempty (GlobalSmoothSolution ν f)`. That is the corollary clause for clause. It is
also the one numbered result the repository itself aligns: `formalization.yaml:122–126`
lists "Corollary 10.6 (Navier–Stokes on ℝ³/ℤ³)" →
`NavierStokes.Comparator.navier_stokes_breakdown_periodic`, status `proved`. Two
independent anchors, so this row is `cited` *and* checked.

### Placed (two)

**Theorem 4.6**, pp. 32–34, the paper's central existence claim. `NominalProfile.Witness`
(`NominalProfile.lean:2481`) is the bundled object — axis stage, controls, outgoing
specification, heat witness, separation bound, small debt — and it is produced, not
assumed: `assembly_exists` (`NominalConeAssembly.lean:1482`) and
`exists_assembly_threshold` (`NominalProfile.lean:2637`). All six parts have a named
declaration:

| Part | Paper | Lean |
|---|---|---|
| (i) smoothness, `E = √(2X)F > 0`, pressure (4.25) | p. 33 | `Witness.fields_smooth` :2523, `E_eq_sqrt_f` :2527, `E_positive` :2530, `pressure_canonical` :2543 |
| (ii) pressure balance and tangential residuals | p. 33 | `pressure_canonical` again (integrated form); stress support in `TerminalStress` / `LeadingStress` |
| (iii) cone margin (4.26) | p. 33 | `NominalConeAssembly.Certificate` :1362, `initial_cones` :1431, `activation_cone` :1251, `exists_nominal_cone` :1517 |
| (iv) flat weight `ζ`, `\|T₀\| ≥ cζ`, `\|∂^αT₀\| ≤ C_α ζ δ^{−m_α}` | p. 33 | `ActiveAnnulusWeight.weight`, `radialWeight`, `edgeDistance`; `weight_flat_left/right`; `LeadingStressWeights.stress_lower_bound` :1121, `physical_jet_bound` :1137 |
| (v) five vanishing moments (4.28), heat exterior (4.29), `U = V₀ = 0` past `Xb` | p. 33 | `five_moments` :2536, `moments_after` :2576, `heat_agreement` :2564, `U_outgoing` :2589, `mass_outgoing` :2594 |
| (vi) two reserved intervals `I_pos`, `I_mean` carrying (4.30) | pp. 33–34 | `ReservedPatches.Slot`, `offsets_separated`, `clean_fields`, `xAmplitude_shape`, `radialClosedPatch` |

Part (iv) closed in E93, which also corrects E92: the lower bound was recorded as
unstated, and it is not. `stress_lower_bound` is
`∃ c > 0, c · zeta v X ≤ ‖stress … (η, X)‖` on `activeLeft < X < activeRight`,
`η ∈ [−1, 1]` — the paper's display, with `ζ` the same flat weight and no `α` anywhere in
the statement. The constant is not the cone margin. It is `min ml (min mr mm)` from
`exists_global_lower_bound` (`ActiveAnnulusWeight.lean:424`): two edge-collar constants
plus `UniformCone.positive_uniform_margin` on the compact interior. The cone margin by
itself gives only nonvanishing (`stress_ne_zero` :462), which is where E92's reading
stopped. The derivative half bounds the whole `n`-th Fréchet derivative, which is at
least as strong as the paper's per-index `m_α`. Placement is statement-level: nothing was
recompiled.

### Partial (one)

**Proposition 10.1**, pp. 117–118. `R3CompactCandidate.Properties`
(`R3CompactCandidate.lean:24`): velocity and pressure smooth on `preSingularDomain`,
compact spatial supports, zero initial velocity, divergence-free, `navierStokesResidual
= f`, force with compact future time support. Built by `of_localized_fields` :248, with
the compact force as a cutoff product (`compactForce_smooth` :90, `compactForce_supported`
:94) — the paper's localization pattern, though the Lean assembly reaches it through the
periodic local model (`of_periodic_local_model` :179) rather than the paper's curl form
directly. Five of the proposition's six clauses are placed. The sixth, "`u(·,t) = p(·,t)
= 0` for all sufficiently small `t ≥ 0`", is not a field of the structure, which carries
only `zero_initial_velocity`; it follows from the time cutoff in the construction but no
named declaration states it. "Agrees with `u_loc`, `p_loc` near the origin near `t = 1`"
is `velocity_locally_eq` :231 / `pressure_locally_eq` :240 — stated for the periodic local
model and consumed inside `of_periodic_local_model`, not as a whole-space field.

### Partial (three)

Both rows this file formerly carried as "cited in a docstring, unchecked" are now read
(E127), and neither citation is the paper's statement.

`CurlClassBounds.lean:757` (`curlRemainder_waveClass`) proves `W_{α+1/2−κ}` for the curl
remainder. That is Lemma 7.7's weight — the paper states it on p. 102 — not Lemma 9.2's
transport product. Lemma 9.2's wave–wave clause is `transport_wave_class` /
`transport_mean_class` (`HarmonicWaveInteraction.lean:389–431`) at `α+α'−κ`, exact but
stated per harmonic and component; its label-separation clause is `labelCarrier_disjoint`
(`ActualCarrierGeometry.lean:342`). Its mean–wave clause is not matched: the tree's
`mean_wave_cmul` (`WaveInteractionBounds.lean:77–96`) gives `W_{α+µ}` with no `−1/2` loss and
no tangential/radial split `(M_µ, M_{µ+1})` — stronger in exponent, but a different statement.

E138 corrects the first half of that sentence. The `−1/2` loss is proved, in
`HarmonicMeanInteraction.meanCross_class`, for the term the paper calls `(v·∇*)w`
— under the name `meanCross`, not `mean_wave`. What remains open is only the
hypothesis: whether `MeanIncrementBounds.Triple`'s two exponent slots are the
paper's `(M_µ, M_{µ+1})` pair. The row stays partial for that reason alone.

E139 reads the split and closes the row. `IncrementBounds` carries three fields —
`radial : MeanClass (H + 1)`, `angular : MeanClass H`, `axial : MeanClass H` — which is
the paper's tangential `M_µ` / radial `M_{µ+1}` hypothesis with `µ = H`. Lemma 9.2 moves
to placed at 17 placed, 6 partial, 50 unplaced.

E140 re-read `FiveRowRank` past where E131 stopped and placed **Lemma 8.7**, which had been
recorded as a partial on three negatives that all turn out to be name misses. The block inverses
E131 called absent are `LocalizedMomentRepair.matrix` / `matrix_det_ne_zero`, with `coefficients`
defined *as* the inverse and `FiveRowRank.finite_jet_bound` supplying the constant; the
`S_α → M_α` sentence E131 called unwritten is the docstring and conclusion of
`MeanRankUpdate.rank_update_meanClass`; the (8.24) exhaustiveness E131 called underived is the
`hV`/`hG` hypothesis pair of `five_rows_on_patch`, discharged on the actual base by
`reserved_five_rows`. At E140 the ledger read 18 placed, 5 partial, 50 unplaced. Two shape differences
are recorded rather than smoothed: uniqueness is `det ≠ 0` plus an inverse in use rather than a
lemma named `unique`, and the class half lives in `MeanRankUpdate`, one module above the algebra.

E141 does the same to **Lemma 8.6**, E132's other §8 partial, and for the same reason: both of
E132's negatives are declarations one module away. Uniqueness is
`TemporalMeanUpdate.timeDerivative_unique` (`:126-145`), stated as `f = g` from equal temporal
derivatives and equal means — on the zero-mean class that is the paper's "unique smooth zero-mean
solution". The seminorm-to-`C^m` conversion E132 called undeclared is
`SmoothFourierData.coefficient_seminorm_bound` (`:368-395`), stated with `p+4` jets and the
explicit lattice constant `3^(p+4) * C * sum (weight k ^ 4)^{-1}`; composed with
`inverse_derivativeWord_bound` it becomes `ParametricTorusInverse.mixedJet_inverse_bound`, whose
constant `mixedLossConstant` is a closed expression. Clause (d) is sharper than the paper's
`c_i0^{-1} <= C S_*`: `temporalAtIndex` writes `-(Tg^i * Q^(1+h))^{-1}` as an identity, and the
(8.22) cancellation is `desiredIncrement_fastDerivative`, exact with remainder `centered f`. One
shape difference is recorded, not smoothed: the declared composite loss is `m+5` where the paper
prints `m+4`, because the seminorm index is `m+1` and the conversion spends four on top; the slack
is the tree's `weight^{-4}` summability where `weight^{-3}` would close the same two-dimensional
sum. The ledger reads 19 placed, 4 partial, 50 unplaced, and §8 has no partial left.

E142 and E143 place the two §10 rows whole. `Lemma 10.4`'s `F` is
`ForceL2Norm.cumulativeForceNorm`, the time integral of the `L²` norm rather than of its
square, and `IntegratedDissipation.candidate_energy_estimates` carries three of its four
clauses as conjuncts (`F(1)` finite, the `F(t)²` inequality at `ν = 1`, and
`IntegrableOn dissipation (Ico 0 1)`), with the uniform energy bound proved one module over
by `CompactEnergy.uniform_finite_energy` and carried as a field. `Lemma 10.5` is
`WholeSpaceUniqueness.candidate_unique_on_Icc`, whose competitor hypothesis
`UniformFiniteEnergy` is exactly `L∞_t L²_x` and whose pressure flux is derived rather than
assumed. Neither row was partial; both were unplaced. The ledger reads 25 placed, 3 partial,
45 unplaced.

E144 re-read **Proposition 9.3** against the periodized assembly and narrowed its reason without moving
it. The decomposition is `PeriodizedWaveBounds.common_cancellation` (residual plus source equals
`globalGood` plus `globalGaussian`), the supports are `globalGood_support` / `globalGaussian_support`
with `HarmonicSourceSupport.NonzeroSupportedOn`, the smooth zero extension is the `ComplementJets`
layer fed by `residualSource_zero_germ_on`, and (9.6) is the `CorrectionState` mean residual with
`MeanResidual.meanPressure_reconstruction` for the pressure split. Two clauses are still unmatched:
the paper's one finite harmonic set carried across bands (the tree bounds `|j|` per stage), and the
sign of the base-flat error, which the tree adds where the paper's display subtracts it.

`LinearWaveBounds.lean:896` (`constructed_linear_wave_with_flat_error`) is the proposition's
coefficient shadow, by its own docstring: the good class `α+1/2−3κ`, an all-order flat error,
and the pointwise `R = G + F` identity. Proposition 9.3's source supports `⊂ Ω_γ`, the `C^∞`
extensions, and the exact mean equations (9.6) are not in it.

**Proposition 6.6** (p. 73) is the §6 row (E129). Four of its six clauses are matched
outright: closure under finite sums (`window_sum_memClass`, `LabelSumBounds.lean:369`,
with the fixed overlap constant 2250 rather than the active set's cardinality); the two
product inclusions (6.30) (`MeanClass.bilinear`, `MeanClass.bilinear_wave`); the label
vanishing (6.31) in its operational form (`jet_zero_off_window`, `window_card_le`,
`labelCarrier_disjoint`); and preservation of band-independent harmonic sets (`Finset`
support fields throughout). Two are matched only by components: (6.31)'s "before cutoff, on
its labelled rectangle" qualifier lives in the locality layer (`MeanLocalCoefficient`)
rather than in a two-wave statement, and (6.32)'s five operator rows are present as binder
classes and one prefactor identity (`along_scaled_direction`), not as a single
class-preservation table.

**Proposition 9.1**, p. 102, the last row this file said it could not place. E94 places it.
The paper's conclusion is class membership — the normalized linear residual, after the
prescribed source is added, lies in `W_{α+1/2−3κs}`, and the pressure amplitude in
`W_{α+1/2}`. Both are in `LocalizedWaveBounds.lean:1014–1024`
(`common_bounds_from_native_local`, repeated at `PeriodizedWaveBounds.lean:1256–1260`),
as a five-part conjunction that also carries the curl correction at `α+1/2−κ`. The tree
calls the residual object `globalGood` (`PeriodizedWaveBounds.lean:799`: "assembled from
the cutoff-and-curl formula on each native copy"), never "linear residual"; that is the
whole reason two earlier passes missed it. The paper's tail qualifier is a theorem, not a
hypothesis: `FiniteHeadClass.waveClass_all_exponents` (`:119`) puts a finitely banded
class in *every* exponent with the identical weight. Statement-level only; the per-label,
per-harmonic form is not exposed as its own declaration.

E145 takes the §8.4 covariance-target row. Both of Corollary 8.5's displayed identities are
declarations, not components: `angular_divergence` (`SignedStressPrimitive.lean:342`) proves
`radialDivergence 2 (sigma 2 F) = −adjusted 2 F`, and `axial_divergence` (`:357`) the same at
`e = 1`. `radialDivergence 2` is `2σ/R + σ'`, so the weights are the paper's `D_r + 2/R` and
`D_r + 1/R` exactly, and the right-hand sides are `−F + (∂_r χ)·mass`, which is the paper's
`−⟨E⟩_Y + σ ε∂_Z J` with the cutoff bump carrying the second term. Support without `Z`
enlargement is `sigma_supported` (`:245`), `M_α` preservation is `meanClass_sigma` (`:424`),
and `⟨A_e⟩_Y = 0` is `bumpCorrection_moment` plus `adjusted_moment_zero` rather than an
estimate. Two shape differences are recorded: the tree's target is pointwise in `Y` and
inherits independence from a `Y`-independent source, and the paper's `T_e` prefactor is the
class index rather than a definition. This also corrects E141's prediction that the row would
be "carried by `MeanIncrementBounds` / `StateMomentBalances` for the increment class" — it is
stated one layer lower, in the primitive module.

E146–E148 close the whole §8 column's partials and add two unplaced rows. **Proposition 8.1**
is not a definitional restatement: `MeanResidual.reynoldsAngular_total_sub` (`:821`) and
`reynoldsRadial_total_sub` (`:837`) derive the decomposition from the averaged equations, and
`MeanIncrementBounds` supplies the paper's operators (`time`, `radialDiv e`, `dz`,
`viscosity c`) so that `thetaResidual`/`axialResidual`/`gr` (`:328-342`) are (8.3) term for term.
**Lemma 8.2**'s primitive is `SignedStressPrimitive`: `weighted_sigma_hasDerivAt` is (8.7) at
general `e`, and because `bumpCorrection_moment` gives the remainder the source's own moment,
the paper's flatness clause (8.8) is not needed — under its hypothesis the remainder is
identically zero. **Proposition 6.6** is reclassified rather than newly found: the pre-cutoff
rectangle is the hypothesis form of `LocalCoefficientBounds` (`MeanLocalCoefficient.lean:11-20`),
whose bounds are required only on `A n`, and the `Q^(1+h)N_abs` row is
`meanClass_chartPrefactor_all` (`TemporalMeanUpdate.lean:335`) for the prefactor the
development applies, `(Tg^i Q^(1+h))^{-1} = c_i0^{-1}`. E129's "components only" was right about
the absence of a single five-row table and wrong about the row's content; the reclassification
is recorded so a later reader can disagree on the record.

E149 and E150 finish the §9 partials. **Proposition 9.3** places, and both of E144's remaining
clauses turn out to be declarations. The band-independent harmonic set is `ActualCycleResidualBounds.modes
residualBand` (`:44,59`): one `Finset ℤ`, with the band `n` universally quantified inside the statement
and the set itself read off the construction — and the cycle doubles it once per stage
(`CorrectionStep.lean:6830`), which is exactly "depends on the finite construction, not on the band".
`HarmonicBlock.BandLimited`, `evaluate_over` and `iteratedAlong_wave` carry the finite display and its
stability under differentiation. Clause (9.6)'s sign is not a discrepancy: the tree writes
`⟨G*+F*⟩ = reduced + ⟨E_B*⟩` (`CorrectionState.lean:130`, `LiftedMeanResidual.angularMean_fullResidual`)
and the paper writes `⟨G*+F*−E_B*⟩ = reduced` — the base error crossed the equals sign, and the
docstring says so in words. **Lemma 10.2** stays partial, and this is the entry where rounding up would
have been easiest: `force_boundary_jets` (`CandidateFromLimits.lean:158`) identifies every terminal jet
with the limit family, so the `F_j` are the constructed force's own jets and `compactForce_supported`
gives their compact support. What is missing is one statement — that the *limit tensors* vanish off
that compact — without which `boundaryLimits_uniformOn_compact` does not upgrade to uniformity on
`ℝ³`. E136's first reason narrows to that single support statement, its second to a naming difference.

E151 places **Lemma 8.8**, the §8.6 gain lemma, and it is the closest match in the column: the
paper's `R_g` is `actualRadialError`, *defined* as `gr(new) − gr(old) − (2V/R)Δv` with
`leadingRadial = invRadius * (2 • (base.angular * h.angular))`; (8.26) is `actualRadialError_eq_formula`,
derived from `gr_change`; and (8.27) is `defects_after_solved_rows`, an identity `defects(new) =
remainders` that holds once `linearRows = −defects(old)` cancels the old rows. The three remainders are
the paper's three displays, including the `− ½ barMoment 2` in the axial flux. The gain is
`H + 9/10 − 2κ`, which is `α + 0.9 − 2κ_s` with `9/10 ≤ H`, and the two zero-mass constraints are
`fiveRows_mass_zero` and `fiveRows_preserve_masses`. Three shape differences are recorded: divergence
lives in the increment layer rather than in this lemma's binders, the base bounds are strip-wide rather
than local to the azimuthal support, and `S_α` is the moment-integrated `UnweightedClass`. Lemma 10.2
therefore leaves the partial column, and Lemma 9.7 is the only row left there: 27 placed, 1 partial.

E152 places **Proposition 8.3**, the §8.3 reconstruction. Part (i): `meanPressure_radial_residual_global`
is (8.13) with the bump mass `−ρP` and the cutoff alias `−A₀(g_r − ρP)` both displayed,
`meanPressure_bar_hasDerivAt` is the bar derivative derived from the integral representation,
`barMoment_mem` puts `P` in `S_α`, `meanClass_meanPressure` and `meanClass_meanPressure_change` put
`p_m` and its differences in `M_α`, `pressureAlias_mean_zero` kills the alias's auxiliary mean, and
`dividedAlias_superflat` gives every fixed derivative order a `Cε^N` bound. Part (ii): `streamPotential`
is literally `r⁻¹I_c(rγ_d)`, `streamGamma_eq_desired_sub_alias_global` is `γ_d − A₁γ_d`,
`reconstructed_divergence_zero` holds at the axis too, `streamGamma_bar_eq_desired` is the bar equality,
and the classes are `meanClass_streamPotential` and `meanClass_streamGamma` at `α` with
`meanClass_scaledRadialUpdate` at `α+1` — the `ε` is inside the direction the derivative is taken
along, which is where the paper's `Q^{1/2−D} = ε` puts it, and where `rankIncrement.radial` builds it.
The one shape difference recorded: the tree does not claim a bare axial derivative gains an exponent,
only the scaled direction it actually constructs. 28 placed, 1 partial.

E153 places **Proposition 8.4**, the §8.4 flux identities. The three defects of (8.15) are
`CorrectionState.pressureDefect`, `.thetaDefect` and `.axialDefect` — the axial one carrying the
`− ½ radialMoment 2 (gr c)` term — with `c_ρ` as `IntegratedMeanBalances.pressureCoefficient`.
Both identities of (8.16) are stated about the actual residual, not about a chosen balance:
`state_angular_moment` composes `averaged_thetaResidual` with `integrated_angular_balance`, and
`state_axial_moment` does the same with `axialDebtPotential = axialDefect + pressureCoefficient •
pressureDefect` and `pressureRecipe_moment`. The pressure half is `flux_pressure_moment`, i.e.
`∫R⟨p_m⟩ = −½∫R²⟨g_r⟩ + c_ρP` derived from `pressure_moment_reconstructed`, and
`constructed_pressure_moment` states it for the constructed primitive. `integrated_axial_reconstructed`
differentiates the sum `J_z + c_ρP` in one `fderiv`, so the moving `c_ρ` never has to be differentiable
on its own — the paper's own remark. One shape difference: `pressureCoefficient r` is a real number on
the state layer and a parameter function on the abstract layer, and the parameter form is the one the
`fderiv` statement uses. 29 placed, 2 partial.

E154 moves **Corollary 7.3** out of the unplaced column but not into the placed one. Its substance is
proved three times over: `GrowingMode.modalOperator` is (7.17) with the damping as a scalar parameter,
`growing_slot` / `scaled_growing_slot` give the cone and envelope with `coneConstant lamMin C / S`
containing no harmonic index, `TorusInverse.norm_directionalInverse_le` bounds the inverse by
`6‖ω⁻¹‖·coeffSeminorm 1 a` for the whole coefficient family, and
`SmoothFamilyTorusInverse.norm_jet_applyMultiplier_le` puts the jet order only in `n + l + 4`. What is
missing is the operator itself: the paper's `f_m ↦ (t_m, π_m)` for the driven equation with `t_m(0) = 0`
has no declaration of that type, the only initial data in `GrowingMode` is the cone initialization, and
no declaration names a threshold `q*` independent of `M`. That is the Lemma 9.7 shape — content under
other names, statement absent — so the row is partial with those three clauses named.

E155 answers the (8.17) question and does not move the ledger, because (8.17) is an equation inside
§8.4 rather than a numbered result. The tree has no declaration of the six factor identities; the
normalisation lives in one moving weight, `qLength = √(coordinateQ)` (and `chartScale = √Q` in chart
form), with one exponent per row. Two things survive the failed search and both matter: `P` and `c_ρ`
share one `radialMoment 2` weight, and `integrated_axial_reconstructed` differentiates their product.
So the table is consistent with the tree and not stated by it — recorded as a lead, not a finding.

E156 places **Corollary 7.8**, the §7.6 covariance expansion, and it is a definition plus one theorem:
`signedTensorRemainder primary old tangent curl` (`CorrectionStep.lean:2309`) *is*
`covarianceIncrement old (tangent + curl) − symmetricCovariance primary tangent`, i.e.
`C(U+V) − C(U) − Σ`; `signedTensorRemainder_exact` (`:2313`) rewrites it as
`symmetricCovariance (old − primary) tangent + symmetricCovariance old curl +
bilinearCovariance (tangent + curl) (tangent + curl)`, which is (7.41) term for term; and
`signedTensorRemainder_mem` (`:2366`) is (7.42) with the hypotheses `γ ≤ δ + β`, `γ ≤ α + η`,
`γ ≤ 2β` — the paper's `ρ+α−1/2`, `α+1/2−κ_s`, `2α−1` under `δ = ρ`, `β = α−1/2`, `α = 1/2`,
`η = α−κ_s`. The divergence clause is `signedTensorRemainder_divergence_mem` (`:2414`), three
`…CovarianceChange` rows at `meanExponent σ + 17/100`, with the `κ` spent by `OperatorBounds`.
The state-level form at `:3242–3252` states it about the covariance the iteration stores. Two shape
differences: `Σ` is constructed from `primary` and `tangent` rather than supplied, and `E` is
`subBlock old primary`. The entry also corrects E154's lead — this corollary needs no ODE solve and
lives in `CorrectionStep`, not `JointODE`. 30 placed, 2 partial.

### Unplaced (the rest)

Fifty-nine, and slice three moved five of them (below). They are sections 4–10 and the
appendices at result level. A grep for `2 * h * (N + 1)` returns nothing under that
spelling, which is why slice three stopped grepping for the paper's expressions and
started grepping for the shape: `slowOrder h n = 2 * n * h` was there all along, under a
name the paper does not use. The same lesson cost the 9.1 row two passes: the paper says
"normalized linear residual", the tree says `globalGood`.

Propositions 5.3, 9.5 and 9.6 are placed as of E97. 5.3's exponent is
`truncationResidual_rate` (`BaseResidual.lean:1440`), `2Nh − 2 − M` — the paper's
`2h(N+1) − K_m` at `K_m = m + 2 + 2h`, exact and `N`-independent — and its
divergence clause is `divergence_slowVelocity_eq_zero` (`SlowExpansionResidual.lean:915`),
stated for the actual Euclidean divergence of the finite sum, with
`divergence_slowVelocity` (`:885`) proving that divergence *equals* the finite
coefficient series. 9.5's `6/5` is `CorrectionState.MeanResidualBounds`, stated as
`1 + σ` for every admissible `σ` and evaluated at `sigma 0 = 1/5`; 9.6's cycle
output is `CorrectionStep.gaugeTemporalStage_next_mean` at `σ + 1/10`, with the
wave side at `gain h (j+1)`. The qualification carried: 9.6's four ordered
corrections exist as four declarations, not one composed step theorem. Two rows are partial again as of E127, Lemma 9.2 and Proposition 9.3, because their cited
declarations are components rather than the statements. Before that, E98 closed
Proposition 10.1's
short-time clause by finding `theorem_1_1_with_initial_rest` (`R3/Theorem.lean:31`), which
proves `u = p = 0` for `|t| ≤ 3/8` — stronger than the paper's "sufficiently small `t ≥ 0`".
The clause is load-bearing, not cosmetic: `R3/ParabolicScaling.compressedCandidate` consumes
it to keep the compressed field smooth across the new `t = 0` (E107).

### The ledger

| Status | Count | Which |
|---|---|---|
| placed, statement read | 33 | Proposition A.4, Proposition B.2, Corollary B.10, Proposition C.2, Lemma 4.7, Theorem 4.6, Corollary 10.6, Proposition 5.3, Proposition 9.1, Proposition 9.5, Proposition 9.6, Proposition 9.9, Proposition 10.1, Lemma 7.7 (E130), Lemma 9.8 (E134), Lemma 10.3 (E137), Lemma 9.2 (E139), Lemma 8.7 (E140), Lemma 8.6 (E141), Lemma 10.4 (E142), Lemma 10.5 (E143), Corollary 8.5 (E145), Proposition 8.1 (E146), Lemma 8.2 (E147), Proposition 6.6 (E148), Proposition 9.3 (E149), Lemma 8.8 (E151), Proposition 8.3 (E152), Proposition 8.4 (E153), Corollary 7.8 (E156), Lemma 7.1 (E157), Lemma 7.4 (E160), Lemma 6.1 (E163) |
| placed, weaker but sufficient | 1 | Proposition 7.5 (E161) |
| partial, unread | 5 | Corollary 7.3 (E154), Proposition 7.2 (E158), Proposition 7.6 (E162), Lemma 10.2 (E136, E150), Lemma 6.2 (E164) |
| partial, inexpressible | 1 | Lemma 9.7 (E133, E159) |
| cited in a docstring, unchecked | 0 | — |
| unplaced | 34 | Theorem 1.1, Theorem 3.1, Proposition 4.2, Lemma 4.1, Lemma 4.3, Lemma 4.4, Lemma 4.5, Lemma 4.8, Lemma 4.9, Proposition 4.10, Lemma 4.11, Lemma 5.1, Lemma 5.2, Lemma 5.4, Proposition 5.5, Lemma 6.3, Corollary A.3, Lemma A.1, Lemma A.2, Lemma A.5, Lemma A.6, Proposition A.7, Lemma A.8, Lemma A.9, Proposition A.10, Lemma B.1, Proposition B.3, Lemma B.4, Proposition B.5, Corollary B.6, Lemma B.7, Proposition B.8, Lemma C.1, Proposition C.3 |
| **total** | **74** | |

Section 8.6, counted in E90 as a placed result, is a section rather than a numbered
result; it leaves the numerator. The denominator itself is 74 (E165).

E133 adds the §9.4 threshold row, and it is the first partial here whose unmatched clause is
unmatched for a structural reason rather than a search failure. Lemma 9.7's first two clauses
are declarations — `ActualCandidateConstruction.qbig` has neither a stage nor a
derivative-order argument, and `GermEndpointInputs` carries one `qbig` across `∀ j` — while its
third clause, the finite count of input derivatives per stage, describes the construction's
syntax and so has no proposition in the object language to be true of.

E134 places the next §9 row whole, and for a reason worth separating from E133: Lemma 9.8's
`ℓ_m` is not merely stage-free in the tree, it is the paper's printed closed form —
`physicalLoss h m = 2*A h + (m+1)*(1+3h/2)`. `gain h j = h*j/10` supplies `g_j` verbatim, and
no definition between `physicalLoss` and `paperJetLoss` accepts a stage index. The tree is also
stronger than the paper here: the displayed `+ E_{j,m}` flat error is absent because all flat
remainders are absorbed.

E135 then *reduced* the denominator from 74 to 73, on a full-text scan that found 3/26/37/7 and
treated the labels 6.3–6.5 as section headings. E165 reverses that reduction. The scan's pattern
ended at `Lemma N.M.`; the paper also numbers a lemma with a title between the number and the
period, and

> **Lemma 6.3 (Number of relevant labels).** There is a constant `C`, independent of the band and
> point, such that `sup #{γ ∈ Γ : (r,z,t) ∈ K_γ} ≤ C` (`.setup/paper/ns.txt:3507–3514`)

is a statement with a displayed bound and a proof, not a heading. It is the thirty-eighth lemma,
so E91's 3/26/**38**/7 = 74 was right. The 73 ledger had also stopped listing Lemma 10.2, which
E150 left partial and later summaries dropped, and it counted Proposition 7.5 as an exact match
although E161 records a weaker inequality. E165 restores the denominator to **74** and splits the
statuses: 33 exact placements, 1 weaker-but-sufficient, 5 partial-unread, 1 partial-inexpressible,
34 unplaced.

E157–E162 finish §7 as far as statement-level reading can reach, and they split cleanly
into two groups that turn out to be the same finding twice. Lemma 7.1, Lemma 7.4 and
Proposition 7.5 place: the phase normal's closeness to its reference, the homogeneous pulse
with its two-sided envelope and `O(1/S*)` ratio, and the cone-to-amplitude solve all have
declarations whose statements are the paper's. Two of the three are stronger than the paper —
the left inverse in (7.10) is an explicit reconstruction formula rather than a bounded matrix,
and the pulse constants are printed exponentials rather than anonymous `c, C`. Proposition 7.5
carries the first *weaker* clause in §7: the paper's `y_σ ≥ c√(S*ζ)` is `c√S*·ζ` in the tree,
smaller by `√ζ`, and `sqrt_S_lower` says in its own docstring that this is the weaker form the
square-root jet theorem needs. The consumer (7.33) needs only `ζ^{-1/2}` after the numerator
weights cancel, which the weaker floor supplies. E165 therefore records the row as
`placed, weaker but sufficient`; the count of exact placements is 33, not 34.

Proposition 7.2 and Proposition 7.6 go to partial, and their unmatched clause is the same one
Corollary 7.3 has: neither the driven pair `f_m ↦ (t_m, π_m)` nor the linearised amplitude map
`Σ ↦ LΣ` is a declaration. The tree proves the bounds on those maps' outputs (7.14, `W_{α−1/2}`,
`C(η_βLΣ) ∈ M_{2α−1}`), and it proves the identity the output satisfies by *subtracting* the
target rather than constructing it from `δa`, so the right-inverse direction is never exhibited.
E162 records the generalisation: the §7–§8 construction is written in terms of the fields it
produces, not the maps it uses, which is why the rows that construct fields place and the rows
that are maps do not.

E159 settles Lemma 9.7's third clause as *inexpressible* rather than unread: the clause counts
input derivatives through a derivation, and the tree has no syntax representation of a derivation
for a proposition to quantify over. (E159's original wording said a proof is not a first-class
value; E165 corrects that — Lean does quantify over proof terms.) It stays partial — the paper's
sentence is unmatched — but it leaves the queue. E165 adopts the split E159 recommended, with a
fixed test: `partial-inexpressible` requires an argued reason that no Lean statement can carry the
clause, and only Lemma 9.7 passes it. Corollary 7.3, Proposition 7.2, Proposition 7.6, Lemma 10.2
and Lemma 6.2 are `partial-unread`: missing declarations or unread modules, not proven
impossibilities.

## Limits of this file

1. **Section level.** A row saying §5 lives in `CorrectionStep` does not say the section's
   eleven lemmas are all there.
2. **Eight of thirteen rows are `object` or `family`.** Only five paper sections are named
   in the source at all. Name agreement is not proof agreement.
3. **No page-level citations.** The paper's page numbers here come from its own table of
   contents; per-result page numbers are not yet recorded.
4. **The paper itself has not been read end to end.** Sections 1–3 were read; 4–10 and the
   appendices were mapped from their titles and from what the Lean files say they contain.
5. **This changes no verdict.** The audit's findings (existential constants, anisotropic
   weights, the Euler clause drift) are unchanged by the table, and the table does not
   support any claim that the paper's argument is wrong.

E163 and E164 open §6, and they split the same way §7 did. Lemma 6.1 is placed and is one of
the cleanest structure-level matches in the paper: `SlotSystem` carries `radius` as a field
before `∀ L`, so "one radius for every label and band" is quantifier order rather than a
claim, `injective` is (6.10)'s parametrization clause, and `disjoint` is (6.13). The bridge from
the paper's support-intersection hypothesis to the tree's combinatorial `Adj` is a composition,
not a declaration, and it is provisional: E166 corrects E163's first version, which cited
`masks_force_adjacency` although that theorem needs both masks nonzero at a common point, and a
point of a closed support need not satisfy that. The valid route is
`physicalSlowMask_tsupport_subset_physicalBox` for the box overlap plus the closed
`lineMask_tsupport` for the level gap. The palette is 2250 colours
(`SlotColoring.palette_card`) where the paper prints no number, and `Δmax` is `nativeGap h`,
obtained through `log 5` instead of `8/ℓ0`; both remain band-independent, which is all (6.13)
needs.

Lemma 6.2 is partial, and the reason is worth keeping: its first three clauses are exact —
`bandGeometry_argumentCost_le` for the derivative factors, `card_liftedRectangles` for
`14^{Δ_ℓ}` (`14 = |det [[3,1],[1,5]]|`), `squareAverage_covering_iterate` for the three-torus
Haar identity — and its fourth is a conjunction of four operations of which the tree declares
three (translation, averaging, directional inversion on zero mean) and leaves radial
integration at fixed `(z,t)` implicit. No declaration names the property the sentence is about,
so "no new dyadic band" has nothing to be true of. That is E162's field-versus-map distinction
reappearing as a name-versus-property distinction, and it is recorded rather than smoothed.

<!-- ledger: placed=33 weaker=1 partial_unread=5 partial_inexpressible=1 unplaced=34 total=74 -->

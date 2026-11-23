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

### Cited but unchecked (two)

`CurlClassBounds.lean:757` names "Lemma 9.2's curl remainder" (p. 102) and
`LinearWaveBounds.lean:896` names "Proposition 9.3 at the coefficient level" (p. 104).
That is the development asserting the correspondence, like the twenty labels in E90, but
neither statement was compared clause by clause.

### Unplaced (64)

Sixty, and slice three moved five of them (below). **Proposition 9.1** (p. 101) is the one
this file still cannot place: its conclusion is class membership, `W_{α+1/2−3κs}`, and no
declaration read states that membership. `ExponentLedger.signedBarGain` contains the
gain `1/2 − 3κ`, but an exponent in an arithmetic ledger is not a class statement. The
rest are sections 4–10 and the appendices at result level. A grep for `2 * h * (N + 1)`
returns nothing under that spelling, which is why slice three stopped grepping for the
paper's expressions and started grepping for the shape: `slowOrder h n = 2 * n * h` was
there all along, under a name the paper does not use.

### The ledger

| Status | Count | Which |
|---|---|---|
| placed, statement read | 8 | A.4, B.2, B.10, C.2, Lemma 4.7, Theorem 4.6, Corollary 10.6, Proposition 9.9 |
| partial | 4 | Proposition 10.1 (5 of 6 clauses), Proposition 5.3, Proposition 9.5, Proposition 9.6 |
| cited in a docstring, unchecked | 2 | Lemma 9.2, Proposition 9.3 |
| unplaced | 60 | the rest, including Proposition 9.1 |
| **total** | **74** | |

Section 8.6, counted in E90 as a placed result, is a section rather than a numbered
result; it leaves the numerator. That and the 74 are the corrections this slice makes to
the previous two entries.

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

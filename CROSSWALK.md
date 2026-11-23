# CROSSWALK — the paper against the Lean development

**Status: first pass. Section level, not lemma level.** Read the limits at the bottom
before quoting anything here.

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

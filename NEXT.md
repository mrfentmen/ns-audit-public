# NEXT — the queue for the remaining 50 numbered results

Generated from the paper's own text at `.setup/paper/ns.txt`. A grep of numbered statements
returns 85 lines; deduplicating by result name gives **73** distinct numbered statements in the
extracted text, of which eighteen are placed, five are partial, and **fifty are unplaced**.
The ledger in `CROSSWALK.md` carries the same **73** as its denominator and the same three
counts, so there is no discrepancy to record here.

This file is a work order, not a finding. Nothing here has been read yet, and no row below
carries any audit conclusion.

## The denominator, settled

The ledger and this file now agree on **73** numbered results: 18 placed, 5 partial, 50
unplaced. The earlier 74 came from E91's kind breakdown (3 theorems, 26 propositions, 38
lemmas, 7 corollaries); the text has 37 lemmas. The indices 6.3–6.5, 9.4 and B.9 are section
numbering, not results — 9.4 is the §9.4 heading. See E135. The fifty-two rows below are the
whole remaining queue, and none of them was ever a phantom.

## How to use it

Each row names the result, its page, the line where its statement begins in the extracted
text, and the module family that the section map says should realise it. Working a row means:
read the paper's statement clause by clause, locate a declaration whose *statement* is that
clause (not whose docstring names it — E90, E94 and E127 are three separate lessons), then
record the result in `AUDIT_LOG.md` and move the ledger row. A row that only half-matches
goes to partial with the unmatched clauses named, as E129, E131 and E132 did.

## The order, and why

The order follows what Theorem 1.1 consumes, not the paper's own numbering: the residual
chain (§9), then the forcing and comparison (§10), then the corrections that build the
residual (§8), the waves (§7), the chart algebra (§6), the base flow (§5), the leading order
(§4), and the two headline statements (§1, §3). The appendices come last because their
headline results — A.4, B.2, B.10, C.2 — are already placed; what is left there is the
supporting machinery.

## Queue

| Result | Page | Statement | Candidate modules |
|---|---|---|---|
| Lemma 10.4 | 121 | `ns.txt:6115` | `R3CompactCandidate`, `R3/PositiveTimeForce`, `R3/CandidateBreakdown`, `R3/WholeSpaceComparisonClosure`, `Periodic*` |
| Lemma 10.5 | 121 | `ns.txt:6143` | `R3CompactCandidate`, `R3/PositiveTimeForce`, `R3/CandidateBreakdown`, `R3/WholeSpaceComparisonClosure`, `Periodic*` |
| Corollary 8.5 | 95 | `ns.txt:4842` | `TemporalMeanUpdate`, `FiveRowRank`, `DefectIncrementBounds`, `StateMomentBalances`, `MeanRankUpdate` |
| Lemma 8.2 | 90 | `ns.txt:4620` | `TemporalMeanUpdate`, `FiveRowRank`, `DefectIncrementBounds`, `StateMomentBalances`, `MeanRankUpdate` |
| Lemma 8.8 | 98 | `ns.txt:5041` | `TemporalMeanUpdate`, `FiveRowRank`, `DefectIncrementBounds`, `StateMomentBalances`, `MeanRankUpdate` |
| Proposition 8.1 | 89 | `ns.txt:4536` | `TemporalMeanUpdate`, `FiveRowRank`, `DefectIncrementBounds`, `StateMomentBalances`, `MeanRankUpdate` |
| Proposition 8.3 | 92 | `ns.txt:4735` | `TemporalMeanUpdate`, `FiveRowRank`, `DefectIncrementBounds`, `StateMomentBalances`, `MeanRankUpdate` |
| Proposition 8.4 | 94 | `ns.txt:4795` | `TemporalMeanUpdate`, `FiveRowRank`, `DefectIncrementBounds`, `StateMomentBalances`, `MeanRankUpdate` |
| Corollary 7.3 | 80 | `ns.txt:4114` | `TorusInverse`, `CurlClassBounds`, `PrimaryPulseBounds`, `PhysicalParticularWave`, `WeightedClasses` |
| Corollary 7.8 | 87 | `ns.txt:4455` | `TorusInverse`, `CurlClassBounds`, `PrimaryPulseBounds`, `PhysicalParticularWave`, `WeightedClasses` |
| Lemma 7.1 | 75 | `ns.txt:3873` | `TorusInverse`, `CurlClassBounds`, `PrimaryPulseBounds`, `PhysicalParticularWave`, `WeightedClasses` |
| Lemma 7.4 | 80 | `ns.txt:4127` | `TorusInverse`, `CurlClassBounds`, `PrimaryPulseBounds`, `PhysicalParticularWave`, `WeightedClasses` |
| Proposition 7.2 | 77 | `ns.txt:3992` | `TorusInverse`, `CurlClassBounds`, `PrimaryPulseBounds`, `PhysicalParticularWave`, `WeightedClasses` |
| Proposition 7.5 | 82 | `ns.txt:4210` | `TorusInverse`, `CurlClassBounds`, `PrimaryPulseBounds`, `PhysicalParticularWave`, `WeightedClasses` |
| Proposition 7.6 | 84 | `ns.txt:4317` | `TorusInverse`, `CurlClassBounds`, `PrimaryPulseBounds`, `PhysicalParticularWave`, `WeightedClasses` |
| Lemma 6.1 | 65 | `ns.txt:3392` | `LabelSumBounds`, `PhysicalGraphBounds`, `SlotColoring`, `TorusCoverDegree` |
| Lemma 6.2 | 67 | `ns.txt:3462` | `LabelSumBounds`, `PhysicalGraphBounds`, `SlotColoring`, `TorusCoverDegree` |
| Lemma 5.1 | 47 | `ns.txt:2364` | `CorrectionStep`, `BaseResidual`, `ActualBaseResidual`, the 21 `Axis*` modules |
| Lemma 5.2 | 50 | `ns.txt:2518` | `CorrectionStep`, `BaseResidual`, `ActualBaseResidual`, the 21 `Axis*` modules |
| Lemma 5.4 | 57 | `ns.txt:2988` | `CorrectionStep`, `BaseResidual`, `ActualBaseResidual`, the 21 `Axis*` modules |
| Proposition 5.5 | 60 | `ns.txt:3100` | `CorrectionStep`, `BaseResidual`, `ActualBaseResidual`, the 21 `Axis*` modules |
| Lemma 4.1 | 25 | `ns.txt:1217` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Lemma 4.11 | 38 | `ns.txt:1891` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Lemma 4.3 | 28 | `ns.txt:1369` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Lemma 4.4 | 28 | `ns.txt:1389` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Lemma 4.5 | 31 | `ns.txt:1517` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Lemma 4.8 | 35 | `ns.txt:1706` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Lemma 4.9 | 36 | `ns.txt:1763` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Proposition 4.10 | 36 | `ns.txt:1787` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Proposition 4.2 | 27 | `ns.txt:1323` | `NominalProfile`, `LeadingStress`, `RadialSchedule`, `FlatCutoff`, `InitialPhysicalData` |
| Theorem 3.1 | 15 | `ns.txt:670` | `NominalConeAssembly`, `ExponentLedger`, `SeedConePaper` |
| Theorem 1.1 | 1 | `ns.txt:29` | `R3/ProblemStatement`, `R3/Theorem`, `ComparatorBridge` |
| Corollary A.3 | 128 | `ns.txt:6491` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Lemma A.1 | 126 | `ns.txt:6413` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Lemma A.2 | 127 | `ns.txt:6459` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Lemma A.5 | 133 | `ns.txt:6752` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Lemma A.6 | 138 | `ns.txt:6975` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Lemma A.8 | 140 | `ns.txt:7102` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Lemma A.9 | 141 | `ns.txt:7179` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Proposition A.10 | 142 | `ns.txt:7206` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Proposition A.7 | 139 | `ns.txt:7019` | `AppendixHeatResults`, `LocalHeatExterior`, `BaseExterior`, `TailGaugePotential` |
| Corollary B.6 | 153 | `ns.txt:7753` | `AxisProfile`, `AxisSeries`, `AxisHolomorphic`, `AxisAnalyticCoefficients` |
| Lemma B.1 | 145 | `ns.txt:7341` | `AxisProfile`, `AxisSeries`, `AxisHolomorphic`, `AxisAnalyticCoefficients` |
| Lemma B.4 | 150 | `ns.txt:7612` | `AxisProfile`, `AxisSeries`, `AxisHolomorphic`, `AxisAnalyticCoefficients` |
| Lemma B.7 | 154 | `ns.txt:7784` | `AxisProfile`, `AxisSeries`, `AxisHolomorphic`, `AxisAnalyticCoefficients` |
| Proposition B.3 | 148 | `ns.txt:7522` | `AxisProfile`, `AxisSeries`, `AxisHolomorphic`, `AxisAnalyticCoefficients` |
| Proposition B.5 | 151 | `ns.txt:7671` | `AxisProfile`, `AxisSeries`, `AxisHolomorphic`, `AxisAnalyticCoefficients` |
| Proposition B.8 | 155 | `ns.txt:7837` | `AxisProfile`, `AxisSeries`, `AxisHolomorphic`, `AxisAnalyticCoefficients` |
| Lemma C.1 | 158 | `ns.txt:7989` | `ActivationCone`, `OutgoingNegativeSlopeCone`, `MatchingConeBounds` |
| Proposition C.3 | 163 | `ns.txt:8233` | `ActivationCone`, `OutgoingNegativeSlopeCone`, `MatchingConeBounds` |

## The next three, concretely

*Worked from this queue: Lemma 9.7 partial (E133), Lemma 9.8 placed (E134), Lemma 10.2 partial
(E136), Lemma 10.3 placed (E137). Both §10 placements came from modules already in the assembly;
the two partials are partial on statement shape, not on content.*

1. **Lemma 10.4** (p. 121) — the next §10 row, and §10 is now the least read of the load-bearing
   sections.
2. **Lemma 10.5** (p. 121) — completes the pair behind the compact assembly.
3. **The §8 mean-correction rows** (Proposition 8.1, Lemma 8.2, Corollary 8.5, pp. 90–95) — the
   compatibility defects feeding the mean correction. Lemma 8.7 left the partial column in
   E140; Lemma 8.6 is now the only §8 partial, and reading these rows is what would finish it.

## Standing limits

- Reading only. Nothing in this queue can be compiled on this machine; any new kernel
  evidence has to go through `kernel-check.yml` on Actions.
- "Placed" is statement-level. It says a declaration exists whose statement is the paper's,
  not that the proof of that declaration is valid.
- The five partials are where the algebra is stated and the bounds are assembled. That is
  the most likely place for a real defect, because the kernel never weighs the bounds.

# BUZZWORD AUTOPSY — `MANUSCRIPT.tex`

Complete vocabulary pass. Every term gets a definition, a location, and an honest status.

**Hard counts** (measured, not estimated):

| Quantity | Count |
|---|---|
| Source | 79,953 chars, ~9,041 words of prose |
| Sections / subsections | 10 / 33 |
| Distinct `\ct{}` identifiers | **203** (322 occurrences) |
| Distinct file citations | 105 (137 occurrences) |
| Distinct emphasised phrases | **65** |
| Quoted claims | **16** |
| Headings in `AUDIT_LOG.md` | **167** |

**Page count.** There is no TeX engine on this machine (`lualatex`, `xelatex`, `pdflatex`, `tectonic`, `latexmk` all absent), so the paper could not be compiled. At ~9,000 words plus dense display math, code listings, a table of contents and a 35-row appendix table, the compiled article is roughly **30–40 pages**. Not 200. The vocabulary is dense per page, not spread thin.

**Method.** I extracted every `\ct{}`, `\file{}`, `\emph{}`, `\subsection{}`, quoted string and capitalised run, then searched for definitional language (`we call`, `we term`, `by X we mean`, `is defined to be`). **Zero hits.** No coinage in this paper is introduced by a definition sentence.

**§H is a different list.** The sections above are about invented or stretched vocabulary. §H is a plain-language glossary of the *real* technical vocabulary — 70 words a non-specialist is unlikely to know, all of them used correctly in the paper.

**Honesty note.** Authorship cannot be proven from the file. What can be shown is which terms are non-standard, undefined, or used exactly once.

---

## A. RHETORICAL COINAGES — 50

Labels that carry argumentative weight and no formal definition. This is the real buzzword list.

| # | Term | Where | Plain meaning | Defined? |
|---|---|---|---|---|
| 1 | **Statement-Design Arbitrage** | title | The result is easy because of how the claim was *worded*, not because hard analysis was done | **No** — title only, never used in the body |
| 2 | **Verification Limits** | title | The edge of what a proof assistant checks: logic yes, numbers no | **No** — title only |
| 3 | **Non-Evaluated Constant Barrier** | §3 | Constants exist but are never computed; the kernel checks that a number exists, not what it is | Implicitly — three exhibits + a mechanism |
| 4 | **Anisotropic Viscous Scaling** | §4 title | The Laplacian is two pieces with different weights, not one | Implicitly — Prop. 4.1 |
| 5 | **the generalized cone** | §4.1 | The surface `|z| = q^D(h)` | Implicitly, by formula |
| 6 | **the exponent ledger** | 21× | A table of which exponent each term carries | By code (`ExponentLedger.lean`) |
| 7 | **a ledger entry** | §1.3, §3.5 | One line of that table; "three entries" = three jobs | No — accounting metaphor |
| 8 | **the ledger reads** | §1.3 | "The accounting comes out as follows" | No |
| 9 | **the container** | §4.4 | The cone-shaped box the profile lives in | No — metaphor |
| 10 | **the container absorbs the mismatch** | §4.4 | The measure factor `q^(1+D)` cancels the scaling | No — metaphor |
| 11 | **proof closure** | abstract | "The proof is finished" | No — "closure" borrowed from logic |
| 12 | **logical closure, numerical opacity** | §7.4 | Logic complete; numbers hidden | No — paired antithesis |
| 13 | **numerical opacity** | §7.4 | No number can be extracted | No |
| 14 | **epistemic, not logical** | §3.3 | Limits what we *know*, not what is *true* | No — philosophical framing |
| 15 | **instrumental, not constitutive** | §7.3 | Used to build the object, not stated in the theorem | No |
| 16 | **naming the force is free** | §1.3 | `f` is defined as the residual, so the equation holds by definition | Claim proved; slogan not defined |
| 17 | **two halves, of very different cost** | §1.3 | The claim is a conjunction; one half is cheap | No |
| 18 | **what the artifact certifies** | abstract, §1.1 | What the proof guarantees | No — "certify" from proof-carrying code |
| 19 | **macroscopic caveats** | abstract, §1.5 | The big obvious objections | No |
| 20 | **structural findings** | §1.4, §8.1 | The two mechanism-level observations | No — "structural" does no work |
| 21 | **rest margin** | §5.2 | The flat interval `|t| ≤ 3/8` | No |
| 22 | **rest interval** | §1.2 | Same interval, different noun | No |
| 23 | **pre-singular domain** | passim | Space-time before `t = 1` | No — never pinned to a set |
| 24 | **forensic code audit** | title | Careful reading of source | No — "forensic" = legal evidence |
| 25 | **premise correction** | §1.6, PHASE2 | The task asked about something that does not exist | No — methodology coinage |
| 26 | **vacuous by dependency** | PHASE2 C.2 | The question has no object, so no answer | No |
| 27 | **schema map** | PHASE2 §0 | Table of where things actually live | No — borrowed from databases |
| 28 | **forensic payload** | PHASE2 title | The findings | No |
| 29 | **closure ledger** | E10.9 | Summary of what got closed | No — second accounting metaphor |
| 30 | **κ-budget** | E4 | The allowance for κ | No — accounting metaphor |
| 31 | **foundational hygiene** | §1.1 | Absence of axioms, `sorry`, `unsafe`, etc. | No |
| 32 | **proof engineering** | §1.1 | Writing large formal proofs | No — industry metaphor |
| 33 | **transitive dependency closure** | §1.1 | Everything Mathlib needs, recursively | Semi-standard (dependency closure) |
| 34 | **proof root** | §1.1 | The top-level theorem a build starts from | No |
| 35 | **reachable `sorry`** | §1.1 | A `sorry` the proof can actually get to | No — but precise enough to check |
| 36 | **statement-level caveat** | §10 | An objection to the wording, not the proof | No |
| 37 | **quantitative content** | §3.6 | The numbers in the estimates | No |
| 38 | **effective bounds** | §3.3 | Bounds you could actually compute | Semi-standard (effective = computable) |
| 39 | **machine dimension analysis** | abstract | Checking units by machine | No — and the paper says it is impossible |
| 40 | **exponent bookkeeping** | §3.3 | Tracking which power of q each term carries | No |
| 41 | **the join** | §6.3 | Where a conditional hypothesis is discharged | No |
| 42 | **the halving** | §6.2 | `timeWidth (n+1) ≤ timeWidth n / 2` | Shorthand for a proved theorem |
| 43 | **compression** | §6 | Shrinking packet time windows | No — and §6.5 says what it is *not* |
| 44 | **the scale regime** | §7 | The chosen record `(J, D, X, δ)` | No |
| 45 | **grading** | §6.4 | The derivative/jet order of a stage | No |
| 46 | **recoverability** | §7.4 | Whether a number can be extracted | No |
| 47 | **structural opacity** | §7.4 | The hiding is built in, not accidental | No |
| 48 | **the arithmetic reflected into types** | abstract, §3.2 | Arithmetic the kernel can see because it sits in a type index | No — but it is the paper's one real idea |
| 49 | **positive position** | §3.2 | A constant appearing only on the right of `≤` | Semi-standard (monotonicity) |
| 50 | **meta-argument** | §3.2, §10 | An argument about the proof scripts, not in them | Standard logic term, used correctly |

### The five that matter most

**1. `Statement-Design Arbitrage`** — used twice, both in the title. The body never says what the arbitrage is, never measures it, never refers back. Delete it and nothing changes. Strongest tell in the document.

**2. `Non-Evaluated Constant Barrier`** — the one coinage with content: three exhibits, a stated mechanism (indices unified vs. terms inhabited), and a scope limit. Still, "barrier" is rhetorical: it is an absence of mechanism, not an obstruction.

**3. The `ledger` family** — `exponent ledger`, `ledger entry`, `closure ledger`, `κ-budget`. Four accounting metaphors for "a list". They organise real content, but import false precision: ledgers balance, and nothing here balances.

**4. `bar-residual`** — a genuine undefined term of art. The paper says "the `17/100` bar-residual bound" (§3.5) and never says what a *bar* is. The repo's doc comments do: the **average over the auxiliary torus** (`PressureStream.lean:69`; "angular mean", `CorrectionStep.lean:1802`). A paper-only reader cannot recover this.

**5. `the container absorbs the mismatch`** — metaphor stacked on metaphor. Plain: the measure factor `q^(1+D)` makes the norm's scaling cancel, so the two different derivative degrees do not break the estimate.

---

## B. OPERATIONAL COINAGES — 32

Defined well enough by use or code. Working terms, not buzzwords — but still the authors' inventions.

| Term | Source | Meaning |
|---|---|---|
| **particularGain** `(σ, κ)` | `ExponentLedger.lean:33` | Binding exponent margin: `min(min(min(½−3κ, ½−κ), waveExponent σ − κ), 2/5)`; proved `= 2/5` on `σ ≥ 1/5, κ ≤ 10⁻⁵` |
| **signedGain** `(σ, κ)` | `:38` | Minimum of four listed gains (`½−4κ`, `2/5−κ`, `½−2κ`, `waveExponent σ − 3κ`); equals `2/5 − κ` on the manuscript's range |
| **gain** | §3.4 | Exponent margin: room before a term breaks the ledger |
| **signed correction** | §3.4 | The correction carrying a sign, not just a magnitude |
| **bar** | repo only | Average over the auxiliary torus (never defined in the paper) |
| **bar-residual** | §3.5 | Residual after that average |
| **bar margin** | `old_difference_bar_margin_iff` | The `17/100` bound; exact threshold `κ < 1/200` |
| **wave exponent** | `waveExponent σ = 1/2 + σ` | The exponent of the wave part |
| **mean exponent** | `meanExponent σ = 1 + σ` | Target exponent for mean and defect |
| **mean-update exponent** | §3.4 | Exponent after one mean update |
| **correction** | §3.4 | The perturbation added to the profile |
| **defect** | §3.4 | The part of the residual that must be cancelled |
| **scale record** | §7 | The structure holding `J, D, X, δ` |
| **packet** | §6.1 | The shrinking construction object; explicitly *not* a "pulse" |
| **grade** | §6.4 | Derivative/jet order being cancelled |
| **guard** (`StageGuards`) | §6.3 | Record of side conditions a stage must satisfy |
| **stage** | §7.2 | One packet-construction step |
| **source time ratio** | `sourceTimeRatio` | Series term bounding the width ratio |
| **cost series** | §6.2 | The summable series controlling the ratio |
| **guarded sequence** | `exists_guarded_sequence` | A sequence satisfying the guards uniformly |
| **width ratio** | §6.2 | `timeWidth(n+1) / timeWidth(n)` |
| **time width** | `timeWidth` | The packet's duration |
| **horizon time** | `horizonTime` | End time of a packet's interval |
| **base horizon** | `baseHorizon` | `6J²X^(−498)`; the global time budget |
| **support scale** | `supportScale` | Spatial radius, exponential at exponent `7/2` |
| **previous shear** | `previousShear` | Exponential factor at exponent 7 |
| **neighbour error** | `neighborError` | Coupling error carrying `X^(cD)` |
| **previous frequency** | `previousFrequency` | Frequency at index zero |
| **actual bounds** | `ActualBounds` | The witness record `(J, D, X, δ)` |
| **inner cube** | `innerCube(r)` | `{x : |x_i| < 1−r}`; at `r=1/4`, `(−3/4, 3/4)³` |
| **plateau** | `plateau` | Region where the cutoff equals 1 |
| **support cylinder** | `supportCylinder` | `{radialSquare ≤ 1/16, |x₂| ≤ 1/4}` |

---

## C. REPO IDENTIFIERS — 69 defined, 203 extracted

Lean names, not prose coinages. They read as jargon because camel-case is unreadable, but each is a function.

**C.1 Statement layer**

| Identifier | Meaning |
|---|---|
| `breakdownStatement` | The headline claim as a Lean `Prop` |
| `CandidateProperties` | 12-field checklist the candidate must satisfy |
| `velocity_smooth`, `pressure_smooth` | `C^∞` on the pre-singular domain |
| `speed_unbounded` | `limsup ‖u(t)‖∞ = ∞` at `t ↑ 1` |
| `zero_initial_velocity` | `u(0,·) ≡ 0` |
| `divergence_free` | `∇·u = 0` |
| `navier_stokes` | The forced equation itself |
| `force_smooth`, `force_support` | `f ∈ C^∞`; time support in `t > 0` |
| `theorem_1_1` | Constant-free restatement |
| `theorem_1_1_with_initial_rest` | Same, plus `u ≡ p ≡ 0` for `|t| ≤ 3/8` |
| `GlobalFiniteEnergySolution` | A competitor running forever with finite energy |
| `CompactPositiveTimeSupport` | Force compact in `x`, zero for `t ≤ 0` |
| `originalResidual` | `f` defined as the residual of the constructed fields |
| `force_nonzero_of_no_global_solution` | Such an `f` must be nonzero at `t > 0` |

**C.2 Constants layer**

| Identifier | Meaning |
|---|---|
| `sobolevConstant` | Whatever Mathlib's proof produced; `noncomputable` |
| `weightedSobolevConstant` | `4 · sobolevConstant + 1` |
| `exists_weight_second_derivative_bound` | ∃ `C > 0` bounding `‖D² baseWeight‖` |
| `weightSecondDerivativeConstant` | `Classical.choose` of that; opaque |
| `averagedPressureDifferenceValue` | The pressure functional being bounded |
| `exists_uniform_test_bound` | The operator-norm constant `B` |
| `fourierHNormSq` | Fourier `H^s` norm squared |
| `norm_num`, `decide` | Evaluation tactics — unavailable on `choose`n terms |

**C.3 Similarity layer**

| Identifier | Meaning |
|---|---|
| `forwardScalar`, `coordinateQ_spec` | `q` solving `q − z²q^{2h} = τ` |
| `coordinateEta`, `coordinateX` | `η = z/q^D`, `X = s/q` |
| `pullback` | `Φ f = q^b f(X, η)` |
| `D`, `d`, `L` | `D = ½−h`, `d = 1−η²`, `L = 1−2hη²` |
| `qTime`, `etaTime`, `xTime` | Time chain coefficients |
| `qAxial`, `etaAxial`, `xAxial` | Axial chain coefficients |
| `time_chain_coefficient`, `axial_chain_coefficient` | Identifications of those coefficients |
| `partialS_pullback`, `partialZ_pullback` | First-order weight transport |
| `partialS_partialS_pullback` | `∂s²` transports weight by `−2` |
| `partialZ_partialZ_pullback` | `∂z²` transports by `−2D(h)` |

**C.4 Interface layer**

| Identifier | Meaning |
|---|---|
| `cutPotential` | `χ · A` |
| `cutVelocity` | `∇ × (χA)` — a curl, hence divergence-free |
| `periodicPotential` | Lattice sum of cut potentials |
| `periodicVelocity` | `∇ × periodicPotential` |
| `spatialDivergence_spatialCurl_on` | `∇·(∇×) = 0` |
| `periodicVelocity_eventuallyEq` | Germ equality to the uncut field on the plateau |
| `activatedVelocity`, `activatedPressure` | `λ(t)·u`, `λ(t)·p` |
| `timeSwitch` | The smooth scalar `λ(t)` |
| `PositiveTimeForce.force` | `θ(t)·f` |
| `compactForce_smooth` | Smooth spatial cutoff times `f` |
| `force_tsupport_subset` | `tsupp f ⊆ [1/16, 21/16] × K` |
| `classical_uniqueness_on_Icc` | The comparison theorem |
| `exists_uniform_rate_bound` | `∃D≥0` chosen **before** `∀R≥1` |
| `eq_of_pressure_flux_bound` | Closure by dominated convergence |
| `actual_flux_eq_canonicalCutoffFlux` | Riesz identity eliminating pressure |

**C.5 Packet / root layer**

| Identifier | Meaning |
|---|---|
| `timeWidth` | Packet duration formula |
| `scaleSequence` | Geometric: `X`, then `(J+n)²·prev` |
| `actualWidths_contract` | Proves widths halve each stage |
| `actualTimeRatio_le` | Bounds the ratio by `sourceTimeRatio` |
| `horizonTime_antitone` | Horizons shrink; **carries halving as a hypothesis** |
| `StageGuards.next_width` | The field that supplies the halving |
| `stage_guards` | Fills that field from `actualWidths_contract` |
| `exists_guarded_sequence` | Produces `J, X₀, δ` uniformly |
| `velocityJet`, `slicedJet` | Assemble the jet family |
| `knownJets`, `profiles_step` | Well-founded recursion over grades |
| `tail_grade_bound` | `N+1 ≤ n` for tail grades |
| `scale_support`, `high_scaled_support` | Dilate a fixed ball by `ℓ` |
| `activationTime` | When a packet starts; strictly increasing |
| `common_positive_interval` | The nested intersection has positive length |
| `exists_scales` | Produces an `ActualBounds` witness from `0 ≤ c` |
| `constructionScales` | **The single `Classical.choice`** selecting `J, D, X, δ` |
| `packets` | `stages constructionScales … n` |
| `initialDatum` | Limit of the packet family |
| `lifespan` | Second `choose`, downstream |
| `initialDatum_singularity` | The top-level Euler singularity |
| `Scales`, `ActualBounds`, `Stage` | The records carrying all of it |
| `actual := hdata.1` | Anonymous field name for the witness |

**C.6 What the other ~130 strings are.** Standard Lean/Mathlib names (`ContDiff`, `ContDiffOn`, `Lp`, `Nonempty`, `Real.rpow`, `Classical.choice`), tactics (`linarith`, `ring`, `norm_num`, `decide`), attributes and commands (`@[implemented_by]`, `noncomputable`, `partial def`, `import`), binders (`hK`, `hsupp`, `hev`), and type fragments (`S : Scales c B`, `parent.T`, `(a i).high`). None is a prose coinage.

---

## D. NOT INVENTED — 22

Standard mathematics, correctly used. Calling these buzzwords would be wrong.

| Term | Meaning |
|---|---|
| **Sobolev embedding** | `W^{1,p} ⊂ L^q`; bounds a norm by derivatives |
| **Gagliardo–Nirenberg** | Interpolation between `L^q` norms and derivatives |
| **Riesz transform / pairing** | Singular integral recovering pressure; eliminates `p` |
| **Gronwall** | Bounds a quantity by its own integral |
| **jet** | Finite Taylor coefficient list at a point |
| **germ** | Equivalence class on arbitrarily small neighbourhoods |
| **pullback** | Rewriting a function in new coordinates |
| **Fréchet derivative** | Genuine bounded linear derivative |
| **homogeneous of degree `d`** | `q ↦ Qq` multiplies the object by `Q^d` |
| **divergence-free** | `∇·u = 0` |
| **self-similar** | Invariant under a scaling group up to its action |
| **compact support** | Nonzero only inside a bounded set |
| **limsup** | Largest value a sequence keeps returning to |
| **dominated convergence** | Passing a limit inside an integral |
| **kernel** | The small trusted core that checks proofs |
| **axiom** | Accepted without proof |
| **unification** | Solvability of type equalities |
| **dependent type** | Type depending on a term |
| **inhabitation** | Having a term of that type |
| **witness** | The object an existential proof produces |
| **reducible definition** | A definition the kernel will unfold |
| **monotone** | Order-preserving |

---

## E. FOIL PHRASES — the paper quotes these to reject them

A careless reader may attribute these to the paper. It does not hold them; it puts them on trial.

| Quoted phrase | Whose claim it is | The paper's verdict |
|---|---|---|
| "fully verified" | The naïve reading of a compiled proof | Wrong by §3 |
| "machine-checked" | Same | True for logic, silent on numbers |
| "numerically and dimensionally reliable" | What people assume | False here |
| "everything the compiler checked" | Same | The compiler checked less |
| "the constant is explicit" | A claim a formalisation might support | No: every constant is `∃`-bound |
| "the estimate is dimensionally correct" | Same | Not machine-checked at all |
| "νΔ acts with weight `q^(b−2)`" | The isotropic reading | Forbidden by the code's own identities |
| "the time-supports compress as the derivative index rises" | A prose claim tested in §6 | True only for consecutive grades |
| "checks the arithmetic … conditional on the estimates being valid" | The repo's own file header | Accurate, and a limit |
| "pulse" | A word a reviewer might search for | Absent; the object is a "packet" |
| "force" | The paper's own scare quotes | It is the residual |
| "smooth solution at `T` ⇔ `0 < T < lifespan.duration`" | A repo theorem | Quoted as the exact statement |

---

## F. THE TELLS

1. **Title abstractions the body abandons.** "Arbitrage" and "Verification Limits" appear only in the title.
2. **No definitional sentences.** Zero `we call` / `we term` / `by X we mean` in 1,555 lines.
3. **The paired antithesis, repeatedly.** "epistemic, not logical"; "instrumental, not constitutive"; "logical closure, numerical opacity"; "a packet, not a pulse".
4. **Borrowed prestige domains.** Finance (`arbitrage`, `budget`), accounting (`ledger`, `entry`), law (`forensic`, `audit`, `certif-`), databases (`schema`).
5. **Ordinary observations promoted to named objects.** "the container", "the join", "the halving", "the scale regime".
6. **Terms naming a stance, not an object.** "structural", "epistemic", "instrumental".
7. **Density without definition.** 203 identifiers, 65 emphasised phrases, and not one sentence of the form "by X we mean Y".

---

## G. PLAIN-ENGLISH SWAP TABLE

| Buzzword | Say instead |
|---|---|
| Statement-Design Arbitrage | "The result follows from how the claim is worded" |
| Verification Limits | "What the proof assistant does not check" |
| Non-Evaluated Constant Barrier | "Constants are never computed" |
| the exponent ledger | "the exponent bookkeeping" |
| the container absorbs the mismatch | "the measure factor makes the scaling cancel" |
| logical closure, numerical opacity | "the logic is complete; the numbers are hidden" |
| epistemic, not logical | "it limits what we know, not what is true" |
| instrumental, not constitutive | "used to build the object, not stated in the theorem" |
| vacuous by dependency | "the question has no object" |
| forensic audit | "close reading of the source" |
| the join | "where the hypothesis is discharged" |
| the halving | "widths at least halve" |
| recoverability | "whether a number can be extracted" |
| positive position | "only on the right of a ≤" |

---

## H. WORDS HUMANS MAY NOT KNOW

Real terms, correctly used. Nothing here is invented; the invented ones are in §A.

### H.1 The fluid words

| Word | What it actually means |
|---|---|
| **Navier–Stokes equations** | The rules for a viscous fluid: acceleration comes from pressure, internal friction, and outside force. |
| **Euler equations** | The same rules with friction set to zero (inviscid flow). |
| **viscosity (ν)** | How thick the fluid is. In the equation it multiplies the Laplacian, so it smooths the flow. |
| **incompressible** | Cannot be squeezed: the same volume always takes the same space. Written ∇·u = 0. |
| **velocity field u(t, x)** | A speed and direction at every point of space, changing with time. |
| **pressure p(t, x)** | The internal push. Only pressure differences do anything; adding a constant changes nothing. |
| **forcing term f** | An outside hand stirring the fluid. |
| **vorticity ω = ∇ × u** | How much the fluid spins locally. |
| **finite energy** | The total of the squared speed over all space stays bounded. |
| **weak solution** | Satisfies the equation only after averaging against test functions, not point by point. |
| **singularity** | A quantity becomes infinite at a finite time; here the top speed as t → 1. Often called blow-up, though the paper does not use that word. |

### H.2 The analysis words

| Word | What it actually means |
|---|---|
| **compact support** | Nonzero only inside a bounded box, exactly zero outside it. |
| **smooth (C^∞)** | Has derivatives of every order; no corners or kinks anywhere. |
| **L^p norm** | A measure of size: the p-th root of the integral of the p-th power. Larger p punishes tall peaks more. |
| **essential supremum (ess sup)** | The smallest bound that holds everywhere except on a set of measure zero. |
| **limsup** | The largest value a sequence keeps returning to, even if it never settles there. |
| **Sobolev space** | Functions whose derivatives up to some order are also integrable. |
| **Sobolev inequality** | Enough derivative control forces membership in a better space; in 3D it gives an L^6 bound from a gradient bound. |
| **Gagliardo–Nirenberg** | Interpolation: a middle norm is controlled by a weak norm and a derivative norm together. |
| **Riesz transform** | A singular integral operator; in fluids it recovers pressure from velocity. |
| **Riesz symbol** | The Fourier multiplier implementing that transform: each frequency is multiplied by a fixed factor. |
| **Gronwall's inequality** | If a quantity is bounded by its own integral, it is bounded by an exponential. |
| **dominated convergence** | A limit may be moved inside an integral when one fixed integrable function dominates the integrand. |
| **Fréchet derivative** | The real derivative of a map between infinite-dimensional spaces; a bounded linear operator. |
| **Jacobian** | The local volume-stretch factor of a coordinate change. |
| **measure element** | The volume factor you must include after changing coordinates, such as dz ds. |
| **self-similar** | The shape repeats at every scale, up to rescaling. |
| **homogeneous of degree d** | Scaling the input by Q multiplies the output by Q^d. |
| **pullback** | Rewriting a function in new coordinates, here blow-up coordinates. |
| **jet** | All derivatives up to a given order at a point, packaged as one object. |
| **germ** | Behaviour on arbitrarily small neighbourhoods; equal germs give equal derivatives at the point. |
| **ansatz** | A guessed form of the solution, chosen to make the equation tractable. |

### H.3 The Lean words

| Word | What it actually means |
|---|---|
| **proof assistant** | Software that checks each proof step against fixed rules. |
| **kernel** | The small trusted core that performs the check; everything else is convenience. |
| **dependent type** | A type that depends on a value, such as vectors of length n. |
| **Prop** | The type of statements that are true or false. |
| **term** | An object of a type. A proof is a term of a proposition. |
| **elaboration** | Filling in implicit arguments and checking that all types match. |
| **unification** | Solving equations between types, such as 6 =? 4. |
| **definitional equality** | Equality the kernel can compute, stronger than merely provable equality. |
| **reducible** | A definition the kernel is allowed to unfold. |
| **inhabitation** | Whether any term of a type exists at all. |
| **witness** | The concrete object an existence proof produces. |
| **Classical.choice** | An axiom: from a proof that something exists, pick one. |
| **noncomputable** | The object exists but cannot be executed. |
| **axiom** | A statement accepted without proof. |
| **sorry** | Lean's placeholder for an omitted proof. |
| **native_decide** | A command that trusts compiled code instead of the kernel. |
| **unsafe** | Code that bypasses Lean's guarantees. |
| **implemented_by** | Attaches fast, unchecked code to a proved function. |
| **partial def** | A definition that may not terminate, so it cannot serve as a proof. |
| **Nonempty** | The proposition that a type has at least one element. |
| **linarith, ring, norm_num** | Lean commands that finish linear arithmetic, polynomial identities, and numeric evaluation automatically. |

### H.4 The audit words

| Word | What it actually means |
|---|---|
| **binder** | The for-all and there-exists prefix of a statement. |
| **binder order** | Which quantifier is chosen first; choosing D before R gives a bound uniform in R. |
| **residual** | What is left when you substitute a guess into the equation. |
| **cutoff (χ)** | A smooth function equal to 1 inside a region and 0 outside. |
| **commutator [∇, χ]** | The extra term produced by differentiating a cutoff times a field. |
| **corrector** | A patch field that restores a property after cutting. |
| **lattice sum** | Adding shifted copies of a function over a grid to make it periodic. |
| **periodization** | The same idea: turning a whole-space object into one on the torus. |
| **torus T³** | Space with every direction wrapped around, like a 3D video-game screen. |
| **localization radius R** | The size of the ball cut out before letting R tend to infinity. |
| **competitor class** | The set of rival solutions a uniqueness theorem is allowed to consider. |

### H.5 Ordinary English words that trip people up

| Word | What it actually means |
|---|---|
| **antitone** | Order-reversing: as one thing grows, the other shrinks. |
| **monotone** | Order-preserving, or consistently one-directional. |
| **vacuous** | True or empty for a trivial reason; "vacuous by dependency" means the question has no subject. |
| **canonical** | The standard, choice-free version of an object. |
| **majorize** | To bound from above by something simpler. |
| **annihilate** | To make zero; here, a constant killed by integrating against a divergence-free field. |

### H.6 The notation

| Symbol | Read as |
|---|---|
| ∀, ∃ | for all, there exists |
| ¬, ∧ | not, and |
| ℝ, ℕ | real numbers, natural numbers |
| ∇, Δ, ∇· | gradient, Laplacian, divergence |
| ∂t, ∂s, ∂z | partial derivatives |
| T³, ℝ³ | the 3-torus, 3-dimensional space |
| C^∞, L^p, H^s_loc | smooth functions, p-integrable functions, locally s-smooth in L² |
| ν, κ, σ, τ, η, χ | viscosity, small exponent, wave parameter, time-to-blow-up, similarity variable, cutoff |

---

*Sources: `MANUSCRIPT.tex` (1,555 lines), `PHASE2-FINDINGS.md`, `AUDIT_LOG.md` (167 headings), `NavierStokesAndEuler/NavierStokes/{ExponentLedger,PressureStream,CorrectionStep}.lean`. Counts produced by extraction over the full source, not sampling. No TeX engine was available, so the page estimate is arithmetic, not a compiled measurement.*

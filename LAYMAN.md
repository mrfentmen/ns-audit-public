# THE AUDIT, IN PLAIN ENGLISH

There are now three versions of this work, and they are meant to be read at different times.

1. **`MANUSCRIPT.tex`** — the paper itself. Formal, with proofs, exact file and line citations, and the full technical apparatus. Written for someone who will check the claims.
2. **`CAVEMAN.md` and `CAVEMAN_1TO1.md`** — the same content in caveman. Deliberately blunt and broken, useful when the formal prose is too dense to hold in your head.
3. **This file** — plain English. Ordinary sentences, no grunting, and no symbol that is not explained in words first. Written for a reader who is comfortable with ideas but is not a mathematician, a logician, or a Lean user.

This version follows the paper section by section, so you can put it next to `MANUSCRIPT.tex` and read across. It does not add claims and it does not soften findings. Where the paper says "we did not verify this", this file says so too.

---

## A note on what a proof assistant is

Lean is a program that checks mathematical proofs. You write a proof in a formal language, and Lean verifies that every step follows from the previous ones by the rules. If a step does not follow, the proof does not compile.

The useful mental picture is a very literal clerk. The clerk is tireless, never gets bored, and never makes an arithmetic slip. But the clerk only knows what it has been told. It has never seen a fluid, does not know what a second is, and cannot tell whether the symbols you gave it describe the thing you meant to describe.

Almost everything in this audit follows from that one limitation. The repository is not sloppy and the clerk is not faulty. The question is what kind of mistake the arrangement can and cannot catch.

---

## 1. INTRODUCTION

### 1.1 The artifact

The repository is OpenAI's `NavierStokesAndEuler`, a formalization in Lean 4 of results about the motion of an incompressible fluid. It is large: 641,332 lines across 2,659 files. A figure of 28.6 million lines is sometimes quoted for it; that number includes the entire standard mathematics library it depends on, and should not be attributed to this repository.

At the level of foundations it is unusually clean. There is no axiom smuggled in, no use of the shortcut that trusts compiled code, no unsafe feature, no partial definition, and no "trust me" hole reachable from the main results. One file does contain such a hole, but nothing in the project imports that file, and the file says as much in its own header.

The repository reports that nine independent external checkers accepted it. This audit re-ran one of them: Comparator, which checks that the solution proves the same statement the challenge poses. It passes on both challenges the repository poses — the Navier–Stokes one (E75) and the Euler one (E79). The other eight were not re-run. E80 then checked the Euler pair the way E76 checked the Clay pair, except by code rather than by paper: those two statements are the ones the repository's own index calls its Euler theorems, and the gap between the challenge's plain-function wording and the development's internal objects is closed by a proved equivalence, not by a promise that they mean the same thing. E81 finally held both statements next to the Euler paper's own Theorem 1.1. Five of its clauses come out stronger than the paper's; two come out weaker. The paper says the *slope* of the flow blows up. The formal statement says the slope plus the *speed* blows up, which is easier to satisfy — a sum can run off to infinity because of either term. The repository proves the paper's harder version too, but the statement Comparator checked does not include it. The second soft spot is subtler: the paper's special time is where its perfectly smooth solution dies, while the formal version measures the same time in a class of solutions that is only smooth in space, with a weaker kind of time derivative. Nobody has proved those two classes are the same object, so the formal blow-up time is the one for the larger class. E82 records both.

So the question is not whether the project compiles. The question is what the compiled object actually certifies.

### 1.2 What the artifact proves

Stated without symbols: for every positive viscosity, there exist a velocity field, a pressure, an external push, and a bounded region, such that —

- the velocity and pressure are smooth at every time before the blow-up (not necessarily extendible through it), and compactly supported in space;
- the push is smooth and only acts at positive times;
- the fluid starts from rest and satisfies the Navier–Stokes equations exactly;
- the total kinetic energy stays bounded on the whole time interval;
- the speed becomes unbounded as the final time is approached;
- and no globally existing finite-energy solution exists for that same push.

Two phrases are worth translating. "Compactly supported" means the motion is confined to a bounded region of space, zero outside it. "No global finite-energy solution" means there is no alternative history of the same fluid, under the same push, that exists for all time with bounded energy.

The version actually proved is slightly stronger: the fluid is completely at rest for an initial stretch of time, up to `t = 3/8`, before anything happens.

### 1.3 Two halves, of very different cost

The statement is really two claims wearing one coat, and separating them is the first step towards an honest account of the cost.

**Naming the push is free.** Take any smooth, incompressible flow that is confined to a bounded region, starts from rest, blows up at the final time, and keeps bounded energy. Now compute what is left over when you substitute it into the equation, and call that leftover "the push". The equation then holds by definition. This is not cheating and it is not hidden: the repository defines the force exactly this way, as the residual of the fields it constructs.

There is even a formal lemma recording the consequence: if a push of this kind rules out a global solution, then it cannot be zero everywhere at positive times. The result is forced by the push, not spontaneous.

**Smoothing the push is not free.** This is the real work, and it is where the cost sits. Because the speed becomes unbounded, the time derivative of the velocity is singular at the final time. The leftover, being built from that derivative, is a combination of singular terms whose sum must cancel to every order. Producing a flow that blows up is easy. Producing one whose leftover does not blow up is the construction.

The repository pays this bill in the assembly of the force, not through the definition. Its final assembly step accepts "the push is smooth" as an assumption and passes it straight into the record. That assumption is not left hanging: it is discharged in two steps, traced in the audit log as E65 and E66 and summarised in Section 5.2.

**The comparison half.** The second claim — that no global solution exists — is genuine mathematics, and it is the strongest part of the development. It is a uniqueness theorem. Its assumptions about the competing solution are close to minimal: smoothness, incompressibility, matching equations, and bounded energy. It does not assume anything about the pressure, nothing about decay at infinity, nothing about support or growth. Even the constant that appears in the argument is uniform in a way that is fixed at the outset rather than chosen later.

So the ledger has three lines, not two. Naming the push is free. Smoothing it is the construction. Proving nobody else has a solution is the mathematics.

### 1.4 Two structural findings

The paper makes two observations about the formalization, and neither says the proof is wrong.

The first is the **constant barrier**. Every constant in the analytic chain of inequalities is introduced by a phrase of the form "there exists a number such that". The proof assistant confirms that such a number exists. It never confirms that the number is small, or the right size for the next step, or measured in the right units. Section 3 explains why this is not an oversight but a consequence of what the tool checks.

The barrier is about the estimates, not about all arithmetic. The exponent ledger works on exact rationals and its equalities are checked; every exponent in the argument is verified to be the one that was intended. What is unweighed is the size of the constants multiplying those powers.

The second is **anisotropic scaling**. The viscosity term, viewed through the change of coordinates used in the construction, splits into two pieces that shrink at different rates: one with the radius, one with the height. The difference between the rates depends on a parameter of the construction. Section 4 explains what that means and what it does not.

Both findings come from one principle: the proof assistant checks arithmetic that has been built into the labels of objects, and is silent about arithmetic that has not.

### 1.5 Relation to the macroscopic caveats

Public discussion of this repository has concentrated on two features: the zero starting velocity, and the fact that the push is defined as a residual. Both are real. Both concern how the theorem is stated. Neither is the subject of this paper.

This audit takes them as given and asks a different question: given that statement, what does the proof certify about it? The answer is not "everything the compiler checked". That distinction matters, because "machine-checked" is routinely read as "numerically and dimensionally reliable", and Section 3 shows that reading is false here, for a reason that will recur in any large formalization of a quantitative estimate.

### 1.6 Method and reproducibility

The findings in this document come from reading proofs and definitions, not from recompiling them. Kernel acceptance was tested separately: the `NavierStokes` library builds (9,580 jobs, exit 0, 817 modules) and the four whole-space theorems depend only on Lean's three standard axioms. That confirms the terms; it does not confirm the statements, and it does not machine-check any finding here. For every claim, the log records the exact file and line, the order in which assumptions are introduced where that matters, the statement in ordinary notation, and a check of units.

Where a review task named a file or declaration that does not exist at the audited commit, the log records the missing premise and points at the module that actually contains the content, rather than inventing a lemma to fill the gap. Of thirty-five tasks in the final review matrix, nineteen were answered from declarations that exist under the names given; sixteen needed their premise corrected.

### 1.7 Three kinds of claim

Findings are easy to over-read, so the paper separates three kinds of statement.

1. **A fact about the code.** This binder comes first, this identity is proved outright, this value was chosen rather than computed, this file is not imported by the root. Facts of this kind are settled by reading, and every one is cited to a file and a line.
2. **A limit on what the formalization establishes.** A fact about the *type* rather than the *term*: no number comes out, no unit is checked. Such a limit can hold of a development whose theorem is also true. Both of this audit's findings are of this kind.
3. **A mathematical error.** A false estimate, a wrong exponent, an inference that does not follow. Only this kind bears on whether the theorem is true, and it requires naming the step and the inequality that fails.

The paper makes claims of the first kind, draws consequences of the second, and makes none of the third. The one time the audit briefly asserted the third — that the anisotropic weights allowed no order-by-order expansion — the source contradicted it and the claim was withdrawn in the log (E63). That is the standard: a claim of the third kind survives only if the bad step can be pointed at.

---

## 2. PRELIMINARIES: NOTATION AND THE TWO SPACES

The paper uses standard fluid notation. Velocity is a vector field; pressure is a scalar; viscosity is a positive number; vorticity is the curl of velocity and measures local spin. A few geometric quantities appear later: the distance from the axis of symmetry, a rescaled version of it, and the height coordinate.

Two spaces appear, and the relationship between them is worth stating because an earlier review hypothesis about it turned out to be wrong.

The first is ordinary three-dimensional space. The second is a torus, which for this purpose means a box whose opposite faces are glued together, so that a flow leaving one side re-enters the other. Physically that models a repeating pattern.

The first fact is that the whole-space development is primary, and the torus version is built from it by adding up shifted copies of the pressure. That the sum is locally finite is proved, not assumed.

The second fact is that the two versions agree exactly inside a central cube, not merely approximately. The agreement is an identity between derivatives of the two residuals, obtained from a local equality of the functions themselves, not from an estimate that something is small. The construction is supported well inside the cube, so the shifted copies do not overlap and no truncation of a series is involved.

Why it matters here is narrow but real. In the comparison argument, pressure is only determined up to an added constant, and that constant cancels against the incompressibility of the difference of two velocities. So no assumption about the size of the pressure is ever needed. That is a genuine strength of the artifact, and it is why the comparison survives objections about how the theorem is stated. It is also why the quantitative content has to be examined separately: once pressure is eliminated, what remains is a chain of inequalities, and that chain is where Section 3 bites.

### 2.1 Alternative (D) and the pressure-periodicity clause

The repository also formalizes a periodic corollary, which corresponds to a different alternative of the Clay problem than the one the main theorem targets.

Its structures impose a condition with no counterpart in the whole-space version: the pressure, as well as the velocity, is required to be periodic in space. Read against a statement that makes only the velocity periodic, that would narrow the class of competing solutions, and narrowing the competitors is exactly how a breakdown claim can be made to look easier than it is.

The objection does not apply here. The official problem description carries an erratum stating that in the periodic case the equation requires both velocity and pressure to be periodic. The repository's clause is the published hypothesis, not an addition to it.

The clause plays no role in the result this paper audits, which concerns the whole-space forced problem and never invokes pressure periodicity. One limitation is recorded alongside the claim: the erratum was not read at first hand for this audit. The attribution rests on the repository's own reference and on secondary descriptions, so it is correctly attributed rather than independently verified.

### 2.2 The periodic corollary, and why it is the stronger statement

The repository also proves a version on the torus, corresponding to the fourth Clay alternative. It says: for every positive viscosity there is a setup, confined to a box, whose speed runs away at time one, and for which no global smooth periodic solution exists.

Two things about it are stronger than the whole-space version this audit concentrates on, not weaker. The competing solutions it rules out need only be smooth, periodic, divergence-free, start from rest, and solve the equation forever; they are not required to have bounded energy or a normalised pressure. Ruling out a larger class is a harder claim, so the periodic result is not obtained by weakening its opponents.

And the move from whole space to the torus is a real change of scale, not a change of notation. Time is stretched so the blow-up still happens at exactly one, space is squeezed, the force and pressure are rescaled to match, viscosity is untouched, and the equation is re-checked after the substitution. The squeeze factor is chosen so that everything fits inside the central box; only then is the pattern repeated across the grid.

The one phrase to read carefully is "support". A periodic pattern that is not identically zero cannot be confined to a bounded region of all of space. The statement instead says: inside each box, the part of the flow that is nonzero sits in a smaller box. That is the honest torus version, and the source says as much itself.

What was done later: the axiom check was run on the periodic side too, on a clean clone, on a rented Linux machine. All five declarations that matter — the periodic theorem, its paper corollary, and both adapters between them — depend only on `propext`, `Classical.choice` and `Quot.sound`, exactly the set the configuration permits, with no `sorryAx` (E73). Before that run the answer was inferred rather than seen (E70, E72).

A second, independent checker also ran: nanoda, a Rust implementation that re-verifies the exported proof without Lean's kernel. It accepted the solution, Lean's kernel accepted it too, and the run ended with `Your solution is okay!` (E75 §7). Two implementations, one answer. That is a second opinion on the replay rather than a second statement comparison, which happened once, on the exports.

### 2.4 Does the encoded statement match Clay's?

This was the objection no checker could answer, so it was answered by reading. Clay's official problem description is six pages; its alternatives (C) and (D) are eleven numbered conditions. Each one was matched to a named field in the file the checker verified: the equation, incompressibility, the initial condition, the two decay conditions, smoothness of velocity and pressure, the bounded-energy condition on all of space, the periodic conditions, and the pressure-periodicity correction from Clay's own errata page. Nothing is missing and nothing is weakened (E76).

Two places where the file says the same thing in different words are now named rather than assumed: "smooth on the closed half-space" is written as smooth on that set, and "every derivative decays faster than any polynomial" is carried as a bound on the whole derivative, which dominates a bound on any single component, with the statement's own free constant absorbing the difference. Neither changes what is claimed.

One spare corridor is recorded too: a group of definitions called `WaveInputs`, and the two endpoint helpers that feed it, are never called by the proof. They are an alternate route, not an assumption the proof leans on (E77).

---

## 3. FINDING ONE: NUMBERS THE COMPUTER NEVER WEIGHS

### 3.1 Three exhibits

The paper gives three examples of constants that the proof assistant accepts without ever evaluating.

**A constant inherited from the standard library.** The development needs a constant for a classical inequality relating the size of a function to the size of its gradient. It takes whatever constant the library's proof produced. That object cannot be computed, has no formula, and is not reducible to anything simpler. A later constant, built from it by doubling and adding one, is just as opaque.

**A bound extracted from an existence proof.** A proof shows that some constant bounds a certain second derivative, by compactness and continuity. The development then names the witness of that existence proof and records only two facts about it: that it is positive, and that it bounds what it was chosen to bound. There is no equation defining it.

**A pressure functional.** A bound on a pressure-related quantity is proved to exist, and the witness is assembled from an explicit expression in the data, multiplied by an operator norm that is itself supplied by an existence proof. This is the friendliest of the three: the dependence on the data is visible. The numerical size is still not.

### 3.2 Why the kernel cannot see it: indices versus terms

Here is the mechanism, and it is worth reading twice.

Some numbers can be built into the **label** of an object. In the formal language, a space of functions can be labelled by an exponent, and a differentiability class can be labelled by an order. If a proof tries to use an object labelled 6 where an object labelled 4 is required, the labels do not match and the proof fails to compile. For numbers used this way, the checker is a complete decision procedure: wrong means rejected.

Most numbers cannot be used this way. A statement of the form "there exists a constant C such that for all x, the size of T x is at most C times the size of S x" is a proposition, not a label. The proof supplies a witness and the checker confirms the witness satisfies the proposition. There is no second, independent description of C to compare against, because the proposition is the only description there is.

Worse, once such a constant is extracted by the non-constructive choice operation, it is not merely unknown but inaccessible. It cannot be computed, cannot be simplified, and has no defining equation. It is a black box that has been certified to exist.

The consequence is precise. An error in an exponent that reaches a label becomes a compile failure. An error in a multiplicative constant does not: the same proposition remains true if the constant is replaced by a million times itself, and every use in the repository is monotone in the constant, so the inflated witness satisfies exactly the same statements. The artifact therefore cannot distinguish a correct constant from a bloated one.

That last observation — monotonicity — is an argument about the proof scripts made by a human, not a fact checked by the machine. It is the reason this audit had to check units by hand.

### 3.3 Epistemic, not logical

It is essential not to overstate this. The barrier does not make the artifact unsound and does not threaten the truth of the theorem.

The headline statement contains no numerical constant. It says: for every viscosity there exist fields and a region satisfying a checklist. The checklist is qualitative — smoothness, support, incompressibility, an identity, an unboundedness claim, and the nonexistence of a global solution. No assignment of values to auxiliary constants can change whether that statement is true.

What the barrier does foreclose is a specific and often assumed set of readings:

- that the proof yields an explicit bound — it does not, every constant is existential or chosen;
- that the bound is dimensionally consistent — this is not machine-checked at all, because units are a layer the formal language does not have;
- that the constant is small enough for a subsequent step — no step ever instantiates a constant by a numeral;
- that the exponent bookkeeping is correct — this one is true, wherever the exponent reaches a label or a reducible definition;
- that the theorem itself holds — this is true, subject to the proof being accepted.

### 3.4 The contrast case: exponents that are checked

It would be wrong to conclude that the formalization checks nothing quantitative. It checks exponents carefully, and precisely because those exponents are definitions rather than witnesses.

There is a module that fixes the bookkeeping of residual orders. Its own header is candid: it checks the arithmetic of those assignments, conditional on the estimates being valid, and it does not define the analytic classes, construct a correction, or prove an estimate. Within that scope its results are exact. One gain is defined as a nested minimum of simple expressions; a theorem proves it equals two fifths, by linear arithmetic on exact rationals. That is something the checker genuinely verifies.

The contrast is the sharpest in the paper. The gain is a definition of a real number built from rationals, so equality with a numeral is decidable. The Sobolev constant is a witness of an existence claim, so no numeral exists to compare against.

Two further details are recorded. First, one parameter of the construction is never defined in the repository: every theorem is stated for values below a bound, and a separate declaration only checks that the numeral used in the manuscript satisfies that bound. The artifact verifies a range, not the manuscript's choice; a smaller value is also recorded as admissible. Second, the tightest numerical margin in the ledger is three orders of magnitude looser than the value actually used. So the ledger is consistent, not tight, and correctness here means internal consistency rather than optimality.

### 3.5 Consequence for the "fully verified" reading

The natural reading of "machine-checked" is that the quantitative content of the paper has been checked. On this artifact that reading fails, and it fails structurally: not because a constant is wrong, but because the proof assistant has no mechanism by which a constant could be right in a checkable sense.

At the quantitative level, the formalization is a certificate that the exponent algebra and the structure of implications are consistent. That is a real achievement. It is what catches an off-by-one in a derivative count, which is the usual way this literature breaks. It is not a certificate of numerical or dimensional correctness.

---

## 4. FINDING TWO: THE FLUID STRETCHES DIFFERENTLY IN TWO DIRECTIONS

### 4.1 The coordinates

To study a solution near the moment it blows up, the construction zooms in on the singular point. The zoom is chosen so that the picture stops changing: as time runs out, space is rescaled in a way that keeps the shape of the flow fixed. This is the standard similarity idea, and it is what makes the blow-up analysable at all.

The subtlety is that the zoom is not the same in every direction. Height and radius shrink at different rates. The rate for height is written `D(h)`, and it depends on a parameter `h` of the construction. For the allowed range of that parameter, height shrinks more slowly than radius. The classical, isotropic case sits at one endpoint of the range; the construction deliberately excludes that endpoint.

There is a family of rescalings that leaves the zoomed coordinates unchanged. That the family acts as claimed is proved from the defining equation, not assumed as an ansatz.

### 4.2 The pullback and its four exact derivative identities

The construction represents a physical field by a fixed profile multiplied by a power of the shrinking factor. This is called the pullback.

Four identities describe what differentiation does to that representation. Two involve first derivatives, two involve second derivatives. In each case, differentiating the physical field corresponds to differentiating the profile and multiplying by a different power of the shrinking factor. The vertical derivative carries a more complicated bookkeeping factor, because the vertical coordinate depends on the shrinking factor in a way the radial one does not.

These are not approximations. They are exact identities, proved by the chain and product rules, and the paper cites each one.

The asymmetry is the whole point. Differentiating sideways moves the power by exactly one. Differentiating vertically moves it by the height exponent, which is a different number whenever the parameter is away from the classical endpoint.

### 4.3 The Laplacian is a sum of two homogeneous weights

The viscous term in cylinder coordinates has three pieces: a second derivative in the radial direction, a first derivative that comes from the geometry of circles, and a second derivative in the vertical direction.

Applying the four identities, the radial pieces combine into a single power, and the vertical piece carries a different power. The radial group closes because the radial second derivative loses two powers while the geometry of the coordinate supplies one back. The vertical group has no such compensation.

The two resulting degrees differ by a quantity that is positive for every allowed value of the parameter. Neither matches what an isotropic viscous term would carry, except at the excluded classical endpoint. So no allowed member of the family is isotropic.

This is a statement about the operator, not about whether the construction works. Any estimate that treats the viscous term as a single object with one scaling degree is, on this family, describing only its radial part.

### 4.4 The container absorbs the mismatch

The mismatch does not break the construction, because the geometry of the zoom contains it.

The zoomed domain is a cone, and the physical volume element picks up a factor that depends on the height exponent. Working through the change of variables, the squared size of a field acquires a power of the shrinking factor that depends on both the profile power and the height exponent. Setting that power to zero identifies the profile power for which the scaling of the norm cancels. That critical power moves with the parameter.

So the cone behaves like a container whose opening determines both which derivative loses least and which power makes the energy scale-invariant. With the wrong bookkeeping, one of the three terms is assigned the wrong exponent.

The paper is careful to say that these particular formulas are the auditors' own derivation, immediate consequences of definitions in the repository, and are labelled as derived rather than quoted.

### 4.5 Why the exponent ledger cannot see this

The reason this survives the formalization is the same reason the constants do, and it is precise.

The profile power is an ordinary real number passed to a definition. It appears inside a power operation whose type is the same no matter what the number is. Changing the power to a different value changes no label, creates no mismatch, and cannot be detected by the checker.

Likewise the height exponent is a definition, and the identity relating it to the parameter is proved by ring arithmetic. But no declaration asserts that the two degrees are different, because that is a statement about geometry, not about the algebra the file set out to check.

So the ledger is exact where it operates, on rationals by linear and ring arithmetic, and silent where geometry enters. The anisotropy is visible in the code, in four theorems with explicit weights. What is absent is any declaration that would fail if someone treated those weights as equal. That absence is structural: to make the power a label, the development would have to reflect it into a type, and it does not.
---

## 5. THREE PLACES WHERE A BILL USUALLY COMES — AND DOESN'T

Sections 3 and 4 are about the inside of the chain. A separate pass looked at the three seams where a construction like this normally pays a visible price: the edge of space at infinity, the moment the flow switches on, and the damage done by cutting a flow to confine it.

In each case the audit found the same pattern. What disappears is a separate boundary, matching, or repair estimate — not because the term involved is small, but because the seam is closed by an identity instead of an inequality. That is why none of the three adds a constant or an assumption to the ledger.

### 5.1 Pressure non-locality and the spatial decay boundary

Pressure is not local. At any point it depends on the whole flow, because it is determined by solving an equation across all of space.

So any argument that integrates pressure against a test field has to do one of two things: assume the pressure decays at infinity, or restrict attention to flows confined to a bounded region. The audit asked which the repository does.

Neither. The uniqueness theorem has no boundary term to evaluate at all. Its assumptions are: smoothness on the time slab; compact support of the reference flow only; incompressibility of both flows; matching equations; matching data; and bounded energy of the competitor. There is no assumption about the competitor's support, decay, growth, or derivatives, and none about the pressure.

Two mechanisms make the surface term vanish before anyone writes it. First, pressure never appears alone: it is paired with the gradient of a smooth cutoff, and that cutoff is compactly supported for every finite radius, so no integral over a distant sphere is ever formed. Second, an identity rewrites the pairing as a standard pressure functional of the tensor product of the two velocities, and that functional is bounded by a constant fixed before the radius is chosen.

Every remaining dependence on the radius is explicit and tends to zero: one term falls like the inverse square, one like the inverse radius, and a third combines both with a fractional power. The conclusion is that the energy of the difference of the two velocities tends to zero.

So the boundary term is neither assumed away nor dodged by a qualitative condition on the competitor. It is never formed. Decay at infinity is replaced by two weaker and checkable assumptions — bounded energy of the competitor, compact support of the reference — and the limit is taken on a bound rather than an identity. This is stronger than the review task anticipated, and it explains why no decay lemma exists to be found: the proof never needs one.

### 5.2 Temporal interface regularity at the initial rest margin

The second seam is the moment the flow switches on, at `t = 3/8`.

The audit asked whether smoothness there is carried by one global statement or by a piecewise construction that hands smoothness to sub-intervals, and whether the time derivatives of the force are evaluated at the seam.

Neither. There is no conditional branch in the definition, and no derivative is evaluated at a point. The seam is a smooth clock function multiplying the whole field: the velocity and pressure are switched on by one scalar function of time, the force by another. Smoothness is inherited because smooth functions are closed under multiplication and composition.

The two sides agree because the field itself is zero on the early interval. The velocity and pressure vanish there, so the residual vanishes there, and the equation across the seam is closed by a case split: on the early side both sides are zero, on the late side the force identity applies.

Two corrections to the premise of the task are recorded. The file the task named contains no smoothness proof of the force at all; its theorems are a uniqueness transfer, a lower bound showing the force cannot vanish, and an energy bound. Force smoothness is established elsewhere, by multiplying the force by a smooth spatial cutoff and then by the smooth time switch. And the time support of the force is not asserted near the seam but bounded strictly away from it.

So no derivative is matched at the seam by computation. The seam is regular because both sides are eventually equal to zero, and smoothness is closed under that identification.

**Where the smoothness of the force actually comes from.** This deserves its own paragraph, because it was the sharpest question an earlier review put to this audit.

The final assembly receives "the force is smooth" as an assumption, which sounds like a gap. It is not, and the audit log traces why in entries E65 and E66.

The first step is inheritance. Smoothness survives multiplication by the smooth spatial cutoff and by the smooth time switch, so the final force inherits its smoothness from the cut force. Nothing is assumed at that boundary; the property is passed along by theorems about multiplication.

The second step is the limit data. Building the force requires the derivatives of the residual to converge locally uniformly at the final time, and that convergence has to come from somewhere. It is constructed, not assumed. The residual's tower of derivatives is proved to vanish at the singular spatial point; those vanishing jets yield boundary limits through smooth one-sided extensions; and those limits are exactly what the smooth extension consumes. The chain bottoms out not at a hypothesis but at the finite-stage estimates — the finite-stage quantitative bounds, which is where the real analytic work of the repository lives.

So there is no unexplained smoothness assumption sitting at the final assembly boundary. What there is, instead, is a place where the audit stops: whether those finite-stage estimates themselves withstand detailed scrutiny is a separate and deeper question, and it is the natural next target.

That next target was taken up, and the result narrows the caveat without removing it. The stage estimates were traced below their own interface (E67, E68); the single fact they rest on — a membership statement about the source of the flow — turned out to be proved for the starting state and rebuilt at every cycle (E69); and the assembly that rebuilds it was read field by field, every field constructed, carried for a reason, or discharged before the call (E71). So the audit's stopping point is not a place where something was assumed and left there. It is a place where the numbers are still existential: the kernel agreed that suitable constants exist, never that any particular constant is small, or dimensionally right. That is finding one, and none of this touches it.

### 5.3 Divergence-free cutoff corrections in the torus interface

Cutting a flow to confine it damages incompressibility: the cut field develops a divergence defect.

The standard repair is a correction field, obtained by solving a divergence equation and subtracting a gradient. The audit asked whether such a correction exists here, whether its derivatives consume powers of the shrinking factor that the ledger has not accounted for, and whether its residual is added to the force or absorbed into a constant.

There is no correction field, and none is needed. The construction cuts the potential, not the velocity, and then takes a curl. A curl is automatically divergence-free, as an identity. The periodized velocity is the curl of the periodized potential, so incompressibility holds exactly. The defective quantity a correction would repair never appears.

The price is paid elsewhere and is visible. The gradient of the cutoff is not removed; it is kept inside the velocity, by the product rule. The extra term is precisely the commutator that a correction field would have cancelled. Here it is part of the field. That is why the cut velocity is exactly divergence-free while matching the naive cut only away from the boundary region: on the plateau where the cutoff equals one, the commutator vanishes, and an eventual equality upgrades the plateau identity to equality of all derivatives. Off the plateau the commutator lives in a thin annulus and enters the residual as an exact term of the equation.

Both ledger questions therefore have empty answers, and that is the finding. There are no correction entries because there is no correction, so no powers can be missing. And no correction residual is absorbed into the force, because there is none to absorb.

---

## 6. THE MACHINERY THAT BUILDS THE FLOW

Sections 3 and 4 concern the statement and the operator. Neither says how the existence half is actually assembled. Section 1.3 takes a field, names its residual, and stops; where the field came from is a separate story.

This section and the next close that gap, on the Euler side of the repository, where the building blocks are constructed and where the singular starting configuration is defined.

### 6.1 The object is a packet, not a pulse

A search for the vocabulary of oscillatory pulses returns nothing. No file is named for a pulse and the word does not appear in the relevant trees. The construction is called a packet.

This is not cosmetic. The subtree is large, and a scan for a word that is not used reports the absence of a name, not the absence of a mechanism. Confusing those two is how an audit produces a false negative.

What is proved here is a construction, not a continuation. The packets have time windows that shrink, and the configuration they define is the limit of that process. Nothing in this part claims that an evolving solution can be continued smoothly through the final time. The smoothness proved is that of the limiting initial configuration.

### 6.2 The halving is a theorem about one geometric sequence

The quantity that shrinks is a time width, defined as a product of consecutive terms of a geometric sequence divided by a square root of a shear quantity that grows much faster.

The numerator is a product of two consecutive terms; the denominator is super-exponential. No asymptotic analysis is needed to see the ratio fall.

A theorem concludes that each width is at most half the previous one, from explicit lower bounds on two parameters, a witness for the scale data, and a smallness condition. The route is a comparison with one component of the scale data, followed by a term bound for a finite series, followed by elementary arithmetic converting a ratio bound into a halving. A finite series total, then arithmetic. No limit, no compactness, no asymptotic expansion.

### 6.3 One link is a hypothesis, and the join is made elsewhere

The nesting theorem carries the halving as an explicit assumption, and its file does not import the file where the halving is proved. Read on its own, it is conditional, and citing it as an unconditional result overstates by one import.

The join is made through the guard structure: the halving is a field of a record, one construction fills that field with the proved theorem, and an existence result produces the parameters uniformly. So the compression closes through that record, not through the nesting file alone.

The arithmetic the nesting consumes is elementary. From a step bound and the halving, one gets containment of the next window inside the current one. Those constants actually give a strict drop that the library does not state: the next horizon is at least a third of a width below the previous one. The library records only the non-strict inequality, which is all the nesting argument needs.

### 6.4 Grade is the derivative order

Whether the claim that time supports compress as the derivative index rises is true of this construction depends on whether the index is the derivative order or just a stage counter.

It is the derivative order, in the operative sense. The jet used at each stage is assembled from the high, mean, and corrector parts of earlier stages; the record of known jets is the history of that family, so grade `p` is exactly the order-`p` jet being cancelled; the recursion for higher grades depends only on the strict prefix, which is well founded; and a tail bound records that grades beyond the required order are indexed past it.

The literal theorem is still about consecutive grades. The width has no separate derivative-order parameter, so the two indices coincide by construction, not by definition. A reader who takes the sentence as a statement about arbitrary derivatives is reading one step further than the code goes.

### 6.5 Three things the compression is not

It is not a dimensional law. The grading and the shrinking come from the same geometric sequence, and the ratio is controlled by a summable cost series, not by differentiating a scaling ansatz. So it is not evidence either way about the isotropy question of Section 4.

It is not the spatial support. The spatial radius grows exponentially at a different exponent, and the two objects are separate. A claim about the time width is not a claim about the spatial radius.

It is not collapse to a point. The activation times increase while the horizons decrease, so the windows nest from both ends, but a theorem shows the intersection has positive length. Nesting keeps one common interval available; it does not squeeze it shut.

---

## 7. THE SINGLE CHOICE THAT SETS THE SCALE

The compression theorems are written for an arbitrary scale record and consume its bounds. That raises a question the local proofs cannot answer: does such a record actually reach the top-level theorem, or is it merely asserted somewhere nearby?

The answer is that the chain closes through a single opaque selection of the scale regime. The lifespan is a second choice, downstream of the first, not a competing root.

### 7.1 The five links

The chain has five links.

First, existence: there is a theorem producing a nonempty scale record from nothing but a nonnegativity assumption. Its proof takes a base power, then common guards, then assembles the record. A bounds witness is produced, for some parameters, from no data at all.

Second, selection: the construction chooses one such record, non-constructively, and never looks inside it.

Third, packets: the packet sequence is the stage sequence applied to that record, with two reflexivity arguments discharging the stage hypotheses so that neither is carried downstream.

Fourth, the datum and its lifespan: the starting configuration is the limit of the packet sequence, and the lifespan is chosen from a finiteness theorem, with its duration bounded by a horizon computed from the selected record.

Fifth, the top level: a theorem assembling the singular configuration, in a root file that imports exactly one module.

### 7.2 Where the compression is spent

Each stage carries a guard record, obtained by passing the selected bounds into a guard constructor, which reaches the halving theorem. That is the only place the halving is proved.

A restriction theorem consumes it to place the next horizon strictly below the parent terminal time. Without the halving, that inequality does not close. The rest of the containment comes from three simple facts: the parent terminal time is the current time plus twice the width, the parent terminal time is bounded by the base horizon, and the base horizon is at most one. Together they keep every packet inside the unit interval.

### 7.3 Instrumental, not constitutive

The exact statement of the final configuration theorem settles what the choice is for.

It asserts smoothness at every order, compact support, non-vanishing, vanishing divergence everywhere, positive duration bounded by one, an equivalence between the existence of a smooth solution and the duration, a blow-up of the first derivative in the limsup sense, and a divergence of a vorticity integral.

Nothing in that list mentions the width, the bounds record, or any scale parameter. The halving is used instrumentally, to build the packet sequence whose limit the configuration is; it is not part of the conclusion. So the chain closes in the construction and not in the statement, which is exactly why a reader who opens only the final file cannot see it.

### 7.4 Logical closure, numerical opacity

Because the scale record is chosen non-constructively, its parameters have no computable content, and every downstream quantity is defined from that opaque witness.

The halving theorem is nevertheless about the actual object: every lemma is written for an arbitrary record and uses only its fields, so nothing is assumed about a hypothetical one. What is lost is recoverability, not correctness. No explicit bound on the first width, on the parameters, or on the base horizon follows from the statement.

This is the constant barrier at a coarser grain. There the opacity sat behind individual constants; here it covers the entire scale regime, chosen once at the root and inherited by every packet. The difference is that this opacity is structural rather than incidental: the choice is the construction, and no rewriting would expose the witness without also exposing which witness was chosen.

Two side checks are recorded. The smallness and geometry conditions on one parameter are stronger than the halving requires, so there is slack. And the bounds record has further producers elsewhere, both of them theorems; no path enters it as an axiom or a bare assumption.

Both questions this trace originally left open are now closed. The import path is four hops, and the final edge is forced because only one module inside the reachable set imports the lifespan file. The chosen parameter does not constrain the derivative order: it enters a frequency only at index zero and every later term is free of it. Its one degrading effect is absorbed by enlarging another parameter, and there is no upper bound on it anywhere, so no ceiling on the order follows. The width argument never reads it.

---

## 8. CONCLUSION

### 8.1 The verdict

The logical integrity of the repository is robust. There are no axioms, no shortcuts that trust compiled code, no unsafe features, no partial definitions, no implementation hooks, and no reachable trust-me holes. The exponent ledger is exact rational arithmetic. And the comparison theorem is a genuine uniqueness result with nearly empty hypotheses.

But the success is an achievement of statement design, not of fluid physics. The two findings mark what the artifact certifies.

The first: every constant in the analytic chain of inequalities is existential or chosen, so the checker verifies existence and never size or dimension. This is not a claim that nothing quantitative is checked: the exponent ledger works on exact rationals and its equalities are verified. The headline theorem is constant-free, so it is not threatened; but no effective bound is extracted, and no machine check of dimensional consistency is possible.

The second: the viscous term on the generalized cone is a sum of two homogeneous pieces whose degrees differ by a parameter-dependent amount. Neither degree is the isotropic one except at the excluded endpoint, so no allowed member is isotropic. The cone's shape absorbs the mismatch, through the volume factor and the parameter-dependent critical weight.

Both are one principle: the checker audits arithmetic reflected into labels and is silent about arithmetic that is not. A reader who takes "machine-checked" to mean "numerically and dimensionally reliable" is misreading the artifact — not because it is defective, but because that is not what type checking is.

A third observation is of another kind. The three seams of Section 5 need no separate boundary, matching, or correction estimate. The pressure pairing has no boundary term at infinity because the test field is compactly supported and the limit is taken on a vanishing bound. The time seam is a smooth scalar multiplier closed by a vanishing germ rather than a derivative match. The divergence defect of cutting is avoided by curling the cut potential, which keeps the commutator inside the velocity. None of the three appears as a constant, an exponent, or an assumption. The seams are exact identities, and exactness is why the constant barrier never has to be crossed there.

The construction side carries its own ledger. Packet widths halve by theorem rather than assumption, with one conditional link joined through a record field. And the whole scale regime enters through a single non-constructive choice, from which the packet family, the limiting configuration, and its lifespan are all built. That root is why the final theorem can be constant-free in its statement while opaque in its construction: the compression is spent to build the object, and the object definition is the only place the witness is ever named.

### 8.2 What the theorem says, in one sentence

A smooth, compactly supported push can drive a fluid from rest to unbounded speed with no global finite-energy solution.

That is the data and the conclusion of alternative (C) of the Clay problem: zero is an admissible starting velocity, and a smooth compactly supported push is stronger than the rapid-decay requirement the statement asks for. If the proof is correct, it resolves (C).

It does not establish the unforced alternatives (A) or (B), and the repository's own lemma showing the force cannot vanish is the formal witness that the result cannot be restated with no push at all — which is exactly why it bears on (C) and not on (A). Whether the proof is correct, and how the Clay institute evaluates it, are separate questions this audit does not decide.

### 8.3 Scope and limitations

The findings rest on reading proofs, definitions, and the order of assumptions. Kernel acceptance was reproduced afterwards on Linux — the `NavierStokes` library built with exit 0, and the four whole-space theorems use only Lean's three standard axioms — because the pinned toolchain's build tool crashes on current macOS. That reproduces acceptance; it does not re-run the nine external checkers, and it verifies terms, not statements. The statement-level caveats are exactly what kernel acceptance cannot test.

Some formulas in Section 4.4 are the auditors' own derivation, immediate consequences of definitions in the repository, and are labelled as derived. One log entry is provisional: the call site and the approximation estimates were verified, but the exact assumption was not opened. And the monotonicity claim behind Section 3.2 is an argument about the scripts, not a machine-checked fact.

### 8.4 Implications beyond this repository

Large formalizations of quantitative estimates are becoming feasible, and this artifact previews their characteristic failure mode.

The checker will faithfully audit the combinatorial and exponent-theoretic skeleton, which is where human error is most common and most damaging. It will not audit the two things a numerical analyst cares most about: the size of constants, and the homogeneity class of the operator.

If such developments are to support claims like "the constant is explicit" or "the estimate is dimensionally correct", those claims must be reflected into the types — as explicit numerals, as rational bounds, or as homogeneity statements proved about the pullback. Otherwise no amount of compilation bears on them.

---

## APPENDIX A. WHAT IS WHERE

The paper's artifact index gives exact paths and line numbers. In words, the important locations are:

- the statement of the theorem and its checklist, in the problem statement file;
- the constant-free restatement and the version with an initial rest interval, in the theorem file;
- the lower bound showing the force cannot vanish, in the breakdown file;
- the uniqueness theorem, in the whole-space uniqueness file;
- the three constant exhibits, in the weighted Sobolev, localized flux, and pressure functional files;
- the exponent ledger and its kappa checks, in the ledger file;
- the coordinates, the pullback identities, and the scaling laws, in the similarity files;
- the torus interface identities, in the periodic localization and residual limits files;
- the cutoff and periodization, in the spatial localization file;
- the time switch, in the time localization and positive-time force files.

## APPENDIX B. WHAT THIS PAPER DOES NOT CLAIM

1. That the repository is unsound, hides an axiom, or proves something false. The verifications point the other way.
2. That Lean or its mathematics library is to blame for the statement-design choices. The same theorem written in prose would meet the same objections.
3. That the comparison theorem is weak or circular. It is, in this audit's view, the strongest part of the development.
4. That the anisotropy finding is a bug in the code. The identities are correct; the finding is that an isotropic reading of them is incompatible with the code.
5. That the whole repository is comparison argument. The line count is the whole tree, and the comparison chain is a small fraction of it.

---

## GLOSSARY, IN ORDINARY WORDS

- **Compactly supported** — confined to a bounded region, zero outside it.
- **Incompressible** — volume is preserved; the flow neither bunches up nor spreads out.
- **Divergence-free** — the mathematical form of incompressibility.
- **Viscosity** — internal friction; a measure of thickness.
- **Kinetic energy** — total motion, squared and summed over the fluid.
- **Blow-up** — the speed becoming unbounded at a finite time.
- **Similarity coordinates** — a zoom that keeps the shape of a blow-up fixed as time runs out.
- **Anisotropy** — behaving differently in different directions.
- **Homogeneous** — scaling by a single overall power.
- **Pullback** — representing a physical field as a fixed profile times a shrinking factor.
- **Laplacian** — the term that measures how a quantity differs from its local average.
- **Witness** — a specific object produced to satisfy an existence statement.
- **Non-constructive choice** — picking a witness without any rule or formula.
- **Type** — a label saying what kind of object something is.
- **Unification** — the step where the checker decides two labels are the same.
- **Axiom** — an assumption accepted without proof.
- **Formalization** — a mathematical argument written so a machine can check it.

---

## WHAT CHANGED AFTER THIS FILE WAS WRITTEN (E94–E96)

Three things, and the first is a correction to this file's own claim that one result of the paper could not be found in the tree.

- **Proposition 9.1 was there.** The paper calls the object "the normalised linear residual"; the tree calls it `globalGood`. Searches for the paper's phrase returned nothing, and two passes recorded that as an absence. The statement is `LocalizedWaveBounds`: the residual in class `α + 1/2 − 3κ`, the pressure in `α + 1/2`, the curl correction in `α + 1/2 − κ`. The paper's "apart from tails vanishing to infinite order" is not a caveat but a theorem — a quantity supported in finitely many bands lies in *every* class with the same weight.
- **The two other partial results came closer.** Proposition 5.3's bound prints `2Nh − 2 − M` in the tree where the paper prints `2h(N+1) − K_m`; those are the same number when `K_m = m + 2 + 2h`, so the derivative loss is exact and does not grow with the truncation. Proposition 9.6's stage bound in `WholeDomainPhysicalStageTheorem` is stated with `gain h (j+1)`, which composes with the ledger identity `h·B_j = gain h j + 7h/10` — the paper's bookkeeping, in the tree's coordinates.
- **The discharge question got a first answer.** Theorem 4.6's inputs are produced, not assumed: the profile it needs is a theorem about existence, and the assembly takes it from there. And the §5 residual rate assumes smoothness and nothing else — no estimate appears among its hypotheses. One thing is still unread: the tree contains two profile constructions, one for the cone and one for the residual rates, and no declaration this audit read identifies them. That is a target, not a defect.

- **Then the last three partial results closed (E97).** Proposition 5.3's divergence clause is `divergence_slowVelocity_eq_zero`, stated for the ordinary three-dimensional divergence of the summed field — and the neighbouring theorem shows that divergence is *exactly* the finite coefficient series, not merely small. Proposition 9.5's `6/5` is `MeanResidualBounds`, which states the class as `1 + σ` for every admissible `σ`, and stage zero has `σ = 1/5`. Proposition 9.6's cycle output is stated one tenth higher, `σ + 1/10`. The profile question above also resolved: `FinalSlowBase.profileSequence` *defines* the §5 profile from the same cone certificate, so there was only ever one object. One qualification stands: Proposition 9.6's four corrections are four declarations, not one composed step.

Counts after these entries: of the paper's 74 numbered results, 12 were placed at statement level (was 8 at the start of the day), 1 was partial, 2 were cited but unchecked, and 59 were unplaced. The single partial row was Proposition 10.1's clause that the fields vanish for a short initial interval.

Later entries moved both the denominator and the numerator, so this is the paragraph to correct:

- **The paper has 73 numbered results, not 74.** A full-text scan finds 3 theorems, 26 propositions, 37 lemmas and 7 corollaries; three of the numbers the earlier count expected are section headings (`9.4` is the §9.4 title). This is E135.
- **That partial row closed.** E98 found `theorem_1_1_with_initial_rest`, which proves the fields vanish for `|t| ≤ 3/8`. The paper only asks for "sufficiently small `t ≥ 0`", so the tree proves a stronger statement, and the compressibility argument downstream uses it.
- **The current ledger, as of E164, is 34 placed, 5 partial, 0 cited-but-unchecked, 34 unplaced.** The five partials are of three kinds. Lemma 6.2 bundles four preservation claims into one sentence; the tree proves three of them one at a time, and the fourth — radial integration at fixed (z, t), plus the promise that no new band appears — is not stated as such, and the property the sentence is about has no name in the development (E164). Lemma 9.7 is partial on a clause that cannot be a Lean statement at all: it counts how many derivatives of the input a stage needs, and that is a fact about how the proof is written, not about the fields (E159). The other three are maps the development never names — Corollary 7.3's `f_m ↦ (t_m, π_m)`, Proposition 7.2's pressure half, and Proposition 7.6's `Σ ↦ LΣ` — while the bounds on what those maps produce are all declared. §7 itself is finished: Lemma 7.1 places (the normal estimate, an explicit left inverse, a modal diagonal true by construction and a damping error that is derived rather than assumed), Lemma 7.4 places (`cP ≤ x ≤ CP` with printed constants, and the ratio to `h` within `4κ_c/S`), and Proposition 7.5 places (Cramer weights, square-root amplitudes, `H(a²) = T`, and a uniform positive floor from compactness plus a stability margin under perturbation). Proposition 7.5 also carries the first place where a printed inequality is *stronger* than the tree's: the paper says `y ≥ c√(Sζ)`, the tree proves `c√S·ζ`, which is smaller by `√ζ` — and the tree proves that this weaker floor is what the next estimate actually needs, so nothing breaks. Section 6 has now begun: Lemma 6.1 places outright (E163) — one radius fixed before the label quantifier, a finite palette of 2250 colours, an explicit bound on how far indices can differ, and the "if two supports touch, their lifted rectangles are disjoint" statement as a field of a structure — and Lemma 6.2 moves to partial for the reason above. E162 names the pattern behind the three map-shaped partials: the §7–§8 construction is written in terms of the fields it produces, not the operators it uses.

What has not changed is what "placed" means. It says a declaration exists whose statement is the paper's. It does not say anyone read its proof, and none of this was compiled by the audit.

---

## WHERE THIS FILE SITS

There are three versions of this work. The formal paper is the record. The caveman files are for holding the shape in your head. This file is for the reader who wants the argument, in order, without the apparatus.

Nothing here replaces the paper. Every claim in this file is a restatement of one in `MANUSCRIPT.tex`, and the citations that let you check it are there, not here.

<!-- ledger: placed=34 partial=5 unplaced=34 total=73 -->

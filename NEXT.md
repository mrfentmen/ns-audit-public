# NEXT — the queue is closed at E170

The work order that used to live here had **32 unplaced** numbered results. E170 read all
thirty-two at statement level. Six place exactly and twenty-six are now `partial-unread`,
each with the declaration that supplies part of the paper's statement and the bundle that has
no single declaration named in `AUDIT_LOG.md`.

The ledger is now:

| Status | Count |
|---|---|
| placed, statement read | 40 |
| placed, weaker but sufficient | 1 |
| partial, unread | 32 |
| partial, inexpressible | 1 |
| unplaced | 0 |
| **total** | **74** |

The denominator is still **74**, and it is the paper's, not a count of what the audit found
easy. E135's 73 was wrong because the census could not match `Lemma 6.3 (Number of relevant
labels)`, a titled statement; E165 restored 74.

## The six exact placements

Lemma A.1, Lemma A.2, Lemma A.9, Lemma C.1, Lemma 4.11 and Theorem 3.1. The first three are
Appendix A's rank, quadratic-branch and flat-primitive results; C.1 and 4.11 are the same
true-cone loop at the appendix's and the main text's coordinates; Theorem 3.1 is
`LocalPaperTheorem.local_theorem`.

## The twenty-six partials

These are the supporting bundles of Appendices A–C and §§4–5. Each has a declared fragment;
each is missing a single statement that composes the paper's clauses. They are category 2 —
formalization limits, not false steps.

| Group | Results |
|---|---|
| Appendix A | Lemma A.3, Lemma A.5, Lemma A.6, Proposition A.7, Lemma A.8, Proposition A.10 |
| Appendix B | Lemma B.1, Proposition B.3, Lemma B.4, Proposition B.5, Corollary B.6, Lemma B.7, Proposition B.8 |
| Appendix C | Proposition C.3 |
| §4 | Lemma 4.1, Proposition 4.2, Lemma 4.3, Lemma 4.4, Lemma 4.5, Lemma 4.8, Lemma 4.9, Proposition 4.10 |
| §5 | Lemma 5.2, Lemma 5.4, Proposition 5.5 |
| §6 | Lemma 6.3 |

The six older partials — Lemma 5.1, Corollary 7.3, Proposition 7.2, Proposition 7.6,
Lemma 10.2 and Lemma 6.2 — are unchanged. Lemma 9.7 remains `partial-inexpressible`.

## What “partial-unread” means here

The named fragment was read. The rest of the bundle was not matched to one declaration. It
does **not** mean the paper's full statement was placed, and it does not mean the missing
bundle is false. The distinction is the one the whole audit keeps:

1. a code fact — a declaration with this statement exists;
2. a formalization limit — the paper's clause is not one statement;
3. a mathematical error — none has been established.

## Standing limits

- Reading only. Nothing in this queue was compiled on this machine; any new kernel evidence
  has to go through `kernel-check.yml` on Actions.
- “Placed” is statement-level. It says a declaration exists whose statement is the paper's,
  not that the proof of that declaration is valid.
- The partials are where the algebra is stated and the bounds are assembled. That is the most
  likely place for a real defect, because the kernel never weighs the bounds.

<!-- ledger: placed=40 weaker=1 partial_unread=32 partial_inexpressible=1 unplaced=0 total=74 -->

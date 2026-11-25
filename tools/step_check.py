#!/usr/bin/env python3
"""Check PROOF_STEPS.md's structure, verdict vocabulary and cited lines.

The ledger checker guards the counts; this guard is about the companion. It
fails if

  * a step is missing one of the six required fields;
  * a step's verdict is absent or outside the published vocabulary;
  * the `proof-steps:` sentinel disagrees with the verdicts actually used;
  * a `ns.txt:NNNN` or `NavierStokes/....lean:NNN` line is beyond the end of
    its source (when that source is present in the checkout);
  * a cited Lean file does not exist in the checkout.

The upstream tree and the paper extract are not vendored, so in CI the line
checks are reported as skipped rather than passed. The structural checks always
run.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOC = ROOT / "PROOF_STEPS.md"
PAPER = ROOT / ".setup" / "paper" / "ns.txt"
TREE = ROOT / "NavierStokesAndEuler"

REQUIRED = [
    "**Paper.**",
    "**In plain terms.**",
    "**Hypotheses.**",
    "**What the paper does.**",
    "**Lean.**",
    "**Does the inference follow?**",
]
VERDICTS = {"exact", "composition", "partial", "inexpressible", "unread", "defect"}
SENTINEL = re.compile(
    r"proof-steps:\s*steps=(\d+)\s+exact=(\d+)\s+composition=(\d+)\s+"
    r"partial=(\d+)\s+inexpressible=(\d+)\s+defect=(\d+)"
)
VERDICT = re.compile(r"\*\*Does the inference follow\?\*\*\s*`([a-z]+)`")
STEP = re.compile(r"^## Step (\d+) — (.+)$", re.MULTILINE)
LINE = re.compile(r"`([^`]+\.(?:lean|txt)):(\d+)`")


def main() -> int:
    problems: list[str] = []
    warnings: list[str] = []

    if not DOC.exists():
        print("PROOF_STEPS.md: missing")
        return 1
    text = DOC.read_text(encoding="utf-8")

    headings = STEP.findall(text)
    if not headings:
        problems.append("PROOF_STEPS.md: no '## Step N — ...' headings")
    numbers = [int(n) for n, _ in headings]
    if numbers != list(range(1, len(numbers) + 1)):
        problems.append(f"PROOF_STEPS.md: step numbers are {numbers}, expected 1..{len(numbers)}")
    titles = [t.strip() for _, t in headings]
    if len(titles) != len(set(titles)):
        problems.append("PROOF_STEPS.md: duplicate step titles")

    bodies = STEP.split(text)
    # split() returns [prefix, number, title, body, number, title, body, ...]
    counts = {key: 0 for key in VERDICTS}
    seen = 0
    for i in range(1, len(bodies), 3):
        number = bodies[i]
        body = bodies[i + 2]
        seen += 1
        for field in REQUIRED:
            if field not in body:
                problems.append(f"PROOF_STEPS.md: Step {number} lacks {field!r}")
        hit = VERDICT.search(body)
        if not hit:
            problems.append(f"PROOF_STEPS.md: Step {number} has no backticked verdict")
            continue
        verdict = hit.group(1)
        if verdict not in VERDICTS:
            problems.append(f"PROOF_STEPS.md: Step {number} has unknown verdict {verdict!r}")
        else:
            counts[verdict] += 1

    found = SENTINEL.findall(text)
    if len(found) != 1:
        problems.append(f"PROOF_STEPS.md: {len(found)} proof-steps sentinels, expected 1")
    else:
        expected = (
            seen,
            counts["exact"],
            counts["composition"],
            counts["partial"],
            counts["inexpressible"],
            counts["defect"],
        )
        actual = tuple(int(x) for x in found[0])
        if actual != expected:
            problems.append(
                f"PROOF_STEPS.md: sentinel {actual} != actual {expected} "
                "(steps, exact, composition, partial, inexpressible, defect)"
            )

    paper_lines = 0
    if PAPER.exists():
        paper_lines = len(PAPER.read_text(encoding="utf-8", errors="replace").splitlines())
    else:
        warnings.append("paper extract absent; ns.txt line checks skipped")

    tree_present = TREE.exists()
    if not tree_present:
        warnings.append("upstream tree absent; Lean line checks skipped")

    for path_text, line_text in LINE.findall(text):
        line = int(line_text)
        if path_text.endswith(".txt"):
            if paper_lines and line > paper_lines:
                problems.append(
                    f"PROOF_STEPS.md: {path_text}:{line} beyond end ({paper_lines} lines)"
                )
            continue
        if not tree_present:
            continue
        candidates = [TREE / path_text, TREE / "NavierStokes" / path_text]
        path = next((p for p in candidates if p.exists()), None)
        if path is None:
            problems.append(f"PROOF_STEPS.md: cited Lean file missing: {path_text}")
            continue
        total = len(path.read_text(encoding="utf-8", errors="replace").splitlines())
        if line > total:
            problems.append(f"PROOF_STEPS.md: {path_text}:{line} beyond end ({total} lines)")

    if problems:
        print("proof-step check failed:")
        for p in problems:
            print("  -", p)
        return 1

    print(
        f"proof-step ok: {seen} steps, {counts['exact']} exact, "
        f"{counts['composition']} composition, {counts['partial']} partial, "
        f"{counts['inexpressible']} inexpressible, {counts['defect']} defect"
    )
    for w in warnings:
        print("  note:", w)
    return 0


if __name__ == "__main__":
    sys.exit(main())

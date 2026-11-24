#!/usr/bin/env python3
"""Cross-document check of the CROSSWALK ledger.

`CROSSWALK.md` is the source of truth: its ledger table carries the placed,
partial, unplaced and total counts and the named rows behind the first two.
Every document that quotes those counts carries one sentinel line

    <!-- ledger: placed=26 partial=2 unplaced=45 total=73 -->   (Markdown)
    % ledger: placed=26 partial=2 unplaced=45 total=73         (TeX)

and this script fails if a sentinel is missing or disagrees with the table, if
the table's arithmetic is wrong, or if its named-row counts do not match the
numbers it claims. The denominator is fixed at 73, the count of numbered
results in the paper after E135 corrected the kind breakdown that produced 74.

History is not checked: `AUDIT_LOG.md` is append-only and quotes counts as they
stood at the time, so it is deliberately absent from DOCS.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TOTAL = 73

DOCS = [
    "README.md",
    "NEXT.md",
    "CROSSWALK.md",
    "CAVEMAN.md",
    "CAVEMAN_1TO1.md",
    "LAYMAN.md",
    "MANUSCRIPT.tex",
]

SENTINEL = re.compile(
    r"ledger:\s*placed=(\d+)\s+partial=(\d+)\s+unplaced=(\d+)\s+total=(\d+)"
)


def ledger_table(text: str) -> dict[str, tuple[int, list[str]]]:
    """Parse the four ledger rows: count, and the names in the third cell."""
    rows: dict[str, tuple[int, list[str]]] = {}
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) != 3:
            continue
        label, count, names = cells
        digits = re.sub(r"\D", "", count)
        if not digits:
            continue
        key = None
        # "unplaced" contains "placed": test the longer label first.
        for candidate in ("unplaced", "partial", "placed", "total"):
            if candidate in label:
                key = candidate
                break
        if key is None:
            continue
        listed = [n.strip() for n in names.split(",") if n.strip()]
        rows[key] = (int(digits), listed)
    return rows


def main() -> int:
    problems: list[str] = []

    crosswalk = (ROOT / "CROSSWALK.md").read_text(encoding="utf-8")
    rows = ledger_table(crosswalk)
    for key in ("placed", "partial", "unplaced", "total"):
        if key not in rows:
            problems.append(f"CROSSWALK.md: ledger row {key!r} not found")
    if problems:
        print("\n".join(problems))
        return 1

    placed, placed_names = rows["placed"]
    partial, partial_names = rows["partial"]
    unplaced, _ = rows["unplaced"]
    total, _ = rows["total"]

    if placed + partial + unplaced != total:
        problems.append(
            f"CROSSWALK.md: {placed} + {partial} + {unplaced} = "
            f"{placed + partial + unplaced}, row says {total}"
        )
    if total != TOTAL:
        problems.append(f"CROSSWALK.md: total is {total}, expected {TOTAL}")
    if len(placed_names) != placed:
        problems.append(
            f"CROSSWALK.md: placed row lists {len(placed_names)} results, "
            f"claims {placed}"
        )
    if len(partial_names) != partial:
        problems.append(
            f"CROSSWALK.md: partial row lists {len(partial_names)} results, "
            f"claims {partial}"
        )

    expected = (placed, partial, unplaced, total)
    for doc in DOCS:
        path = ROOT / doc
        if not path.exists():
            problems.append(f"{doc}: missing")
            continue
        found = SENTINEL.findall(path.read_text(encoding="utf-8"))
        if not found:
            problems.append(f"{doc}: no ledger sentinel")
            continue
        if len(found) > 1:
            problems.append(f"{doc}: {len(found)} ledger sentinels, expected 1")
        for hit in {tuple(int(x) for x in h) for h in found}:
            if hit != expected:
                problems.append(
                    f"{doc}: sentinel {hit} != table {expected} "
                    "(placed, partial, unplaced, total)"
                )

    if problems:
        print("ledger check failed:")
        for p in problems:
            print("  -", p)
        return 1

    print(
        f"ledger ok: {placed} placed, {partial} partial, {unplaced} unplaced, "
        f"{total} total; {len(DOCS)} documents agree"
    )
    print("partials: " + ", ".join(partial_names))
    return 0


if __name__ == "__main__":
    sys.exit(main())

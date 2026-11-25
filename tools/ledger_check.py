#!/usr/bin/env python3
"""Cross-document check of the CROSSWALK ledger and the NEXT queue.

`CROSSWALK.md` is the source of truth: one ledger row per status, each carrying
a count and the result names behind it. `NEXT.md`'s queue table is the work
order for the unplaced rows. Every document that quotes the counts carries one
sentinel line

    <!-- ledger: placed=34 weaker=1 partial_unread=6 partial_inexpressible=1 unplaced=32 total=74 -->   (Markdown)
    % ledger: placed=34 weaker=1 partial_unread=6 partial_inexpressible=1 unplaced=32 total=74         (TeX)

This script fails if

  * a ledger row is missing, or its count disagrees with the names it lists;
  * the arithmetic does not close, or the denominator is not 74;
  * a result appears in two status rows;
  * the queue and the unplaced row name different results, the queue repeats
    one, or it names a result the ledger has already placed (the E165 defect:
    a stale `Lemma 8.8` row survived while the counts still added up);
  * a document's sentinel is missing, duplicated or disagrees with the table;
  * the zero-count `cited in a docstring, unchecked` row is missing or non-empty;
  * a reader edition omits one of the awkward partials from its narrative, or
    contains a phrase that was true only before E165 (a narrative-drift guard).

History is not checked: `AUDIT_LOG.md` is append-only and quotes counts as they
stood at the time, so it is deliberately absent from DOCS.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TOTAL = 74

DOCS = [
    "README.md",
    "NEXT.md",
    "CROSSWALK.md",
    "CAVEMAN.md",
    "CAVEMAN_1TO1.md",
    "LAYMAN.md",
    "MANUSCRIPT.tex",
]

# The five counted rows, then the total. Labels are matched exactly after
# stripping bold markers and case; anything else in the table is ignored.
STATUS_LABELS = {
    "placed, statement read": "placed",
    "placed, weaker but sufficient": "weaker",
    "partial, unread": "partial_unread",
    "partial, inexpressible": "partial_inexpressible",
    "cited in a docstring, unchecked": "cited",
    "unplaced": "unplaced",
    "total": "total",
}

# Narrative checks are deliberately narrow: they guard the three partials that
# were dropped from a summary once already, and the phrases that quoted the
# pre-E165 counts. AUDIT_LOG is excluded because it quotes history.
NARRATIVE_DOCS = ["MANUSCRIPT.tex", "CAVEMAN.md", "CAVEMAN_1TO1.md", "LAYMAN.md"]
REQUIRED_NARRATIVE = ["Lemma 9.7", "Lemma 10.2", "Lemma 6.2"]
STALE_PHRASES = [
    "forty-four numbered results",
    "The four partial rows",
    "five are partial, and thirty-four are unplaced",
    "## The denominator, settledThe",
]
COUNTED = ("placed", "weaker", "partial_unread", "partial_inexpressible", "unplaced")

NAME = re.compile(r"^(?:Theorem|Lemma|Proposition|Corollary)\s+(?:[0-9]+|[A-Z])\.(?:[0-9]+)$")
SENTINEL = re.compile(
    r"ledger:\s*placed=(\d+)\s+weaker=(\d+)\s+partial_unread=(\d+)"
    r"\s+partial_inexpressible=(\d+)\s+unplaced=(\d+)\s+total=(\d+)"
)
ATTRIBUTION = re.compile(r"\s*\((?:E\d+)(?:,\s*E\d+)*\)\s*$")


def cells_of(line: str) -> list[str]:
    return [c.strip() for c in line.strip().strip("|").split("|")]


def clean_name(cell: str) -> str:
    cell = cell.strip().strip("`")
    cell = ATTRIBUTION.sub("", cell)
    return re.sub(r"\s+", " ", cell).strip()


def split_names(text: str) -> list[str]:
    """Split on commas that are not inside the `(E136, E150)` annotations."""
    parts: list[str] = []
    depth = 0
    buf = ""
    for ch in text:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(buf)
            buf = ""
        else:
            buf += ch
    parts.append(buf)
    return [clean_name(p) for p in parts if p.strip()]


def ledger_table(text: str) -> dict[str, tuple[int, list[str]]]:
    rows: dict[str, tuple[int, list[str]]] = {}
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        cells = cells_of(line)
        if len(cells) != 3:
            continue
        label = re.sub(r"\*+", "", cells[0]).strip().lower()
        key = STATUS_LABELS.get(label)
        if key is None:
            continue
        digits = re.sub(r"\D", "", cells[1])
        if not digits:
            continue
        names_text = cells[2].strip()
        listed = (
            []
            if names_text in {"—", "-", ""} or names_text.lower() == "the rest"
            else split_names(names_text)
        )
        rows[key] = (int(digits), listed)
    return rows


def queue_names(text: str) -> list[str]:
    """The four-column queue table in NEXT.md, identified by its result names."""
    names: list[str] = []
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        cells = cells_of(line)
        if len(cells) != 4:
            continue
        name = clean_name(cells[0])
        if NAME.match(name):
            names.append(name)
    return names


def main() -> int:
    problems: list[str] = []

    crosswalk = (ROOT / "CROSSWALK.md").read_text(encoding="utf-8")
    rows = ledger_table(crosswalk)
    for key in (*COUNTED, "cited", "total"):
        if key not in rows:
            problems.append(f"CROSSWALK.md: ledger row {key!r} not found")
    if problems:
        print("\n".join(problems))
        return 1

    counts = {key: rows[key][0] for key in COUNTED}
    names = {key: rows[key][1] for key in COUNTED}
    total = rows["total"][0]

    if rows["cited"][0] != 0 or rows["cited"][1]:
        problems.append("CROSSWALK.md: the cited row must be 0 and name no results")

    if sum(counts.values()) != total:
        problems.append(
            "CROSSWALK.md: "
            + " + ".join(str(counts[k]) for k in COUNTED)
            + f" = {sum(counts.values())}, row says {total}"
        )
    if total != TOTAL:
        problems.append(f"CROSSWALK.md: total is {total}, expected {TOTAL}")

    seen: dict[str, str] = {}
    for key in COUNTED:
        if len(names[key]) != counts[key]:
            problems.append(
                f"CROSSWALK.md: {key} row lists {len(names[key])} results, "
                f"claims {counts[key]}"
            )
        for name in names[key]:
            if not NAME.match(name):
                problems.append(f"CROSSWALK.md: {key} row has malformed name {name!r}")
            if name in seen:
                problems.append(
                    f"CROSSWALK.md: {name} appears in both {seen[name]} and {key}"
                )
            seen[name] = key

    queue_path = ROOT / "NEXT.md"
    queue = queue_names(queue_path.read_text(encoding="utf-8"))
    if len(queue) != len(set(queue)):
        duplicates = sorted({n for n in queue if queue.count(n) > 1})
        problems.append("NEXT.md: duplicate queue rows: " + ", ".join(duplicates))
    queue_set = set(queue)
    if len(queue_set) != counts["unplaced"]:
        problems.append(
            f"NEXT.md: {len(queue_set)} distinct queue rows, "
            f"ledger says {counts['unplaced']} unplaced"
        )
    missing = queue_set - set(names["unplaced"])
    extra = set(names["unplaced"]) - queue_set
    if missing:
        problems.append(
            "NEXT.md: queue rows absent from the unplaced ledger row: "
            + ", ".join(sorted(missing))
        )
    if extra:
        problems.append(
            "CROSSWALK.md: unplaced results absent from the NEXT queue: "
            + ", ".join(sorted(extra))
        )
    overlap = queue_set & (set(names["placed"]) | set(names["weaker"]) | set(names["partial_unread"]) | set(names["partial_inexpressible"]))
    if overlap:
        problems.append(
            "NEXT.md: queue rows the ledger has already classified: "
            + ", ".join(sorted(overlap))
        )

    expected = (
        counts["placed"],
        counts["weaker"],
        counts["partial_unread"],
        counts["partial_inexpressible"],
        counts["unplaced"],
        total,
    )
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
                    "(placed, weaker, partial_unread, partial_inexpressible, unplaced, total)"
                )

    for doc in NARRATIVE_DOCS:
        text = (ROOT / doc).read_text(encoding="utf-8").replace("~", " ")
        for name in REQUIRED_NARRATIVE:
            if name not in text:
                problems.append(f"{doc}: narrative omits {name}")

    for phrase in STALE_PHRASES:
        for doc in DOCS:
            if phrase in (ROOT / doc).read_text(encoding="utf-8"):
                problems.append(f"{doc}: stale phrase {phrase!r}")

    if problems:
        print("ledger check failed:")
        for p in problems:
            print("  -", p)
        return 1

    print(
        f"ledger ok: {counts['placed']} exact, {counts['weaker']} weaker, "
        f"{counts['partial_unread']} partial-unread, "
        f"{counts['partial_inexpressible']} partial-inexpressible, "
        f"{counts['unplaced']} unplaced, {total} total"
    )
    print(f"queue ok: {len(queue_set)} rows, identical to the unplaced ledger row")
    print(
        "partial-unread: "
        + ", ".join(names["partial_unread"])
        + " | partial-inexpressible: "
        + ", ".join(names["partial_inexpressible"])
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

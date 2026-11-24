#!/usr/bin/env python3
"""Print byte size and page count for each PDF given on the command line.

No third-party imports. The page tree is usually inside a compressed object
stream, so a plain regex over the file finds no `/Count` at all and the earlier
version reported `0 pages` on every PDF the typeset workflow produces. This
version inflates each FlateDecode stream and takes the largest `/Count` it
finds, falling back to counting `/Type /Page` objects in the inflated text.
"""

import re
import sys
import zlib


def inflated(blob: bytes) -> list[bytes]:
    """Every stream body that inflates, plus the raw file."""
    chunks = [blob]
    for match in re.finditer(rb"stream\r?\n(.*?)\r?\nendstream", blob, re.S):
        try:
            chunks.append(zlib.decompress(match.group(1)))
        except zlib.error:
            continue
    return chunks


def pages(path: str) -> str:
    with open(path, "rb") as handle:
        blob = handle.read()
    chunks = inflated(blob)
    counts = [int(m.group(1)) for chunk in chunks
              for m in re.finditer(rb"/Count\s+(\d+)", chunk)]
    if counts:
        return str(max(counts))
    found = sum(len(re.findall(rb"/Type\s*/Page[^s]", chunk)) for chunk in chunks)
    return str(found) if found else "unknown"


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("usage: pdfpages.py FILE.pdf [...]", file=sys.stderr)
        return 2
    for path in argv[1:]:
        try:
            size = len(open(path, "rb").read())
        except OSError as exc:
            print(f"{path}: {exc}")
            continue
        print(f"{path}: {size} bytes, {pages(path)} pages")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))

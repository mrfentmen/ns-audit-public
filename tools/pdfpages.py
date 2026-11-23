#!/usr/bin/env python3
"""Print byte size and page count for each PDF given on the command line.

No third-party imports: the page tree is read straight out of the file's
object stream, which is enough for the PDFs the typeset workflow produces.
"""

import re
import sys


def pages(path: str) -> str:
    with open(path, "rb") as handle:
        blob = handle.read()
    count = re.search(rb"/Count\s+(\d+)", blob)
    if count:
        return count.group(1).decode()
    return str(len(re.findall(rb"/Type\s*/Page[^s]", blob)))


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

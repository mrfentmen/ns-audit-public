#!/usr/bin/env bash
# Fetch the pinned Lake dependencies with plain git.
# Lake's own package fetcher aborts (SIGTRAP in libmalloc) on this host, so the
# dependency checkouts are created here and Lake is only asked to read them.
set -u
cd "$(dirname "$0")/NavierStokesAndEuler" || exit 1
export PATH="$HOME/.elan/bin:$PATH"

mkdir -p .lake/packages

python3 - <<'PY' > /tmp/pkgs.tsv
import json
m = json.load(open("lake-manifest.json"))
for p in m.get("packages", []):
    print(p["name"], p["url"], p["rev"], sep="\t")
PY

while IFS=$'\t' read -r name url rev; do
  dir=".lake/packages/$name"
  if [ -d "$dir/.git" ] && [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null)" = "$rev" ]; then
    echo "[skip] $name already at $rev"
    continue
  fi
  echo "[fetch] $name $rev"
  rm -rf "$dir"
  mkdir -p "$dir"
  git -C "$dir" init -q
  git -C "$dir" remote add origin "$url"
  if ! git -C "$dir" fetch -q --depth 1 origin "$rev"; then
    echo "  depth-1 fetch failed, trying full fetch"
    if ! git -C "$dir" fetch -q origin "$rev"; then
      echo "  direct rev fetch failed, fetching all refs"
      git -C "$dir" fetch -q origin '+refs/heads/*:refs/remotes/origin/*' '+refs/tags/*:refs/tags/*' || {
        echo "[FAIL] $name could not be fetched"; continue; }
    fi
  fi
  git -C "$dir" checkout -q --detach "$rev" 2>/dev/null \
    || git -C "$dir" checkout -q --detach FETCH_HEAD
  got="$(git -C "$dir" rev-parse HEAD 2>/dev/null)"
  if [ "$got" = "$rev" ]; then
    echo "[ok]    $name $(du -sh "$dir" | cut -f1)"
  else
    echo "[MISMATCH] $name wanted $rev got $got"
  fi
done < /tmp/pkgs.tsv

echo "=== dependency footprint ==="
du -sh .lake/packages 2>/dev/null

#!/usr/bin/env bash
# Build the audited repository inside the Linux guest.
# Reason: the pinned Lean runtime aborts on the macOS host (libmalloc double-free
# at thread teardown), so Lake cannot build anything natively.
set -u
export DEBIAN_FRONTEND=noninteractive
export PATH="$HOME/.elan/bin:$PATH"

echo "=== host ==="
uname -a
nproc
free -g | head -2

echo "=== apt ==="
sudo apt-get update -qq
sudo apt-get install -y -qq git curl ca-certificates build-essential xz-utils python3
echo "APT_EXIT=$?"

echo "=== elan ==="
if ! command -v elan >/dev/null 2>&1; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --no-modify-path --default-toolchain none
fi
elan --version
echo "ELAN_EXIT=$?"

echo "=== toolchain ==="
elan toolchain install leanprover/lean4:v4.34.0-rc2
elan default leanprover/lean4:v4.34.0-rc2
lean --version
echo "TOOLCHAIN_EXIT=$?"

echo "=== copy repo into guest disk ==="
SRC="${NS_SRC:-$(cd "$(dirname "$0")" && pwd)/NavierStokesAndEuler}"
DST="$HOME/ns-build"
rm -rf "$DST"
mkdir -p "$DST"
tar -C "$SRC" --exclude .lake -cf - . | tar -C "$DST" -xf -
cd "$DST" || exit 1
echo "source files: $(find . -name '*.lean' | wc -l), lines: $(find . -name '*.lean' -print0 | xargs -0 cat | wc -l)"
echo "COPY_EXIT=$?"

echo "=== mathlib cache ==="
lake exe cache get
echo "CACHE_EXIT=$?"

echo "=== oleans present after cache ==="
find .lake/packages/mathlib/.lake/build -name '*.olean' 2>/dev/null | wc -l

echo "=== build NavierStokes ==="
/usr/bin/time -v lake build NavierStokes 2>&1 | tail -25
echo "BUILD_EXIT=${PIPESTATUS[0]}"

echo "=== oleans in repo ==="
find .lake/build -name '*.olean' 2>/dev/null | wc -l

echo "=== kernel check of the main statement ==="
cat > AuditProbe.lean <<'EOF'
import NavierStokes.R3.Theorem
#print axioms breakdownStatement
EOF
lake env lean AuditProbe.lean
echo "PROBE_EXIT=$?"

echo "=== disk ==="
df -h / | tail -1
du -sh "$HOME/.elan" "$DST/.lake" 2>/dev/null
echo "ALL_DONE $(date -u +%H:%M:%S)"

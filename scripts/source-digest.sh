#!/usr/bin/env bash
# Deterministic digest of every input that determines the exported rules:
# Lean sources, Lake configuration, the dependency manifest and the toolchain.
# Prints a lowercase hex SHA-256.
set -euo pipefail
cd "$(dirname "$0")/.."
{
  find OSR -name '*.lean' -print
  printf '%s\n' OSR.lean lakefile.toml lake-manifest.json lean-toolchain scripts/Export.lean
} | LC_ALL=C sort | while read -r f; do
  printf '%s  %s\n' "$(sha256sum "$f" | cut -d' ' -f1)" "$f"
done | sha256sum | cut -d' ' -f1

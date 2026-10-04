#!/usr/bin/env bash
# put agda on PATH and register cubical
set -euo pipefail

dir=${TOOLCHAIN_DIR:-$HOME/toolchain}
echo "$dir/bin" >> "$GITHUB_PATH"
mkdir -p "$HOME/.agda"
echo "$dir/cubical/cubical.agda-lib" > "$HOME/.agda/libraries"
cat "$dir/versions.env" | tee -a "$GITHUB_ENV"

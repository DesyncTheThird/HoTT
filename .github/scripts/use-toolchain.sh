#!/usr/bin/env bash
# put agda (or mikan) on PATH and register cubical
set -euo pipefail

dir=${TOOLCHAIN_DIR:-$HOME/toolchain}
# versions, and Mikan_datadir for mikan
set -a
# shellcheck source=/dev/null
source "$dir/versions.env"
set +a
if [[ -n ${Mikan_datadir:-} && ! -d $Mikan_datadir ]]; then
  echo "missing mikan data dir $Mikan_datadir" >&2
  exit 1
fi

echo "$dir/bin" >> "$GITHUB_PATH"
mkdir -p "$HOME/.agda"
echo "$dir/cubical/cubical.agda-lib" > "$HOME/.agda/libraries"
tee -a "$GITHUB_ENV" < "$dir/versions.env"
"$dir/bin/agda" --version

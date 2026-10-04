#!/usr/bin/env bash
# put the proof assistant on PATH and register cubical
set -euo pipefail

usage() {
  cat <<EOF
usage: $0 [--dir=PATH]

activate a toolchain in github actions
EOF
}

dir=${TOOLCHAIN_DIR:-$HOME/toolchain}
for arg in "$@"; do
  case $arg in
    --dir=?*) dir=${arg#*=} ;;
    -h | --help) usage; exit 0 ;;
    *) echo "error: bad argument: $arg" >&2; usage >&2; exit 2 ;;
  esac
done

# don't overwrite local ~/.agda/libraries
if [[ -z ${GITHUB_ENV:-} || -z ${GITHUB_PATH:-} ]]; then
  echo "error: not in github actions (GITHUB_ENV/GITHUB_PATH unset)" >&2
  usage >&2
  exit 1
fi

# prover, versions, data dir
set -a
# shellcheck source=/dev/null
source "$dir/versions.env"
set +a
for var in Agda_datadir Mikan_datadir; do
  if [[ -n ${!var:-} && ! -d ${!var} ]]; then
    echo "error: missing $PROVER data dir ${!var}" >&2
    exit 1
  fi
done

echo "$dir/bin" >> "$GITHUB_PATH"
mkdir -p "$HOME/.agda"
echo "$dir/cubical/cubical.agda-lib" > "$HOME/.agda/libraries"
tee -a "$GITHUB_ENV" < "$dir/versions.env"
"$dir/bin/$PROVER" --version

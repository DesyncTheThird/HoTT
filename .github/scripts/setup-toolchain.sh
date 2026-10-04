#!/usr/bin/env bash
# install agda + cubical into $TOOLCHAIN_DIR
set -euo pipefail

usage() {
  echo "usage: $0 [--resolve-only] <stable|nightly> <stable|nightly>" >&2
  exit 2
}

resolve_only=false
if [[ ${1:-} == --resolve-only ]]; then
  resolve_only=true
  shift
fi
[[ $# -eq 2 ]] || usage
agda_ch=$1
cubical_ch=$2
dir=${TOOLCHAIN_DIR:-$HOME/toolchain}

case $agda_ch in
  stable)
    agda_tag=$(gh release view -R agda/agda --json tagName -q .tagName)
    ;;
  nightly)
    agda_tag=nightly
    ;;
  *) usage ;;
esac
agda_asset=$(gh release view "$agda_tag" -R agda/agda --json assets \
  -q '.assets[].name | select(endswith("-linux.tar.xz"))')
agda_version=${agda_asset#Agda-}
agda_version=${agda_version%-linux.tar.xz}

case $cubical_ch in
  stable)
    cubical_ref=$(gh release view -R agda/cubical --json tagName -q .tagName)
    cubical_version=$cubical_ref
    ;;
  nightly)
    cubical_ref=$(gh api repos/agda/cubical/commits/master -q .sha)
    cubical_version=${cubical_ref:0:7}
    ;;
  *) usage ;;
esac

key="toolchain-$agda_ch-$cubical_ch-$agda_version-$cubical_version"
echo "agda $agda_version, cubical $cubical_version"
if [[ -n ${GITHUB_OUTPUT:-} ]]; then
  echo "key=$key" >> "$GITHUB_OUTPUT"
else
  echo "key=$key"
fi
$resolve_only && exit 0

rm -rf "$dir"
mkdir -p "$dir/agda" "$dir/bin" "$dir/cubical"

# agda
gh release download "$agda_tag" -R agda/agda -p "$agda_asset" -O - | tar -xJ -C "$dir/agda"
agda_bin=$(find "$dir/agda" -type f -name agda | head -n 1)
chmod +x "$agda_bin"
ln -s "$agda_bin" "$dir/bin/agda"
"$dir/bin/agda" --version

# cubical
git -C "$dir/cubical" init -q
git -C "$dir/cubical" fetch -q --depth=1 https://github.com/agda/cubical "$cubical_ref"
git -C "$dir/cubical" checkout -q FETCH_HEAD
(cd "$dir/cubical" && "$dir/bin/agda" --build-library)

cat > "$dir/versions.env" <<EOV
AGDA_VERSION=$agda_version
CUBICAL_VERSION=$cubical_version
EOV

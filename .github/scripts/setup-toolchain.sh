#!/usr/bin/env bash
# install agda/mikan + cubical into $TOOLCHAIN_DIR
set -euo pipefail

usage() {
  echo "usage: $0 [--resolve-only] <stable|nightly|mikan> <stable|nightly>" >&2
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
  stable | nightly)
    if [[ $agda_ch == stable ]]; then
      agda_tag=$(gh release view -R agda/agda --json tagName -q .tagName)
    else
      agda_tag=nightly
    fi
    agda_asset=$(gh release view "$agda_tag" -R agda/agda --json assets \
      -q '.assets[].name | select(endswith("-linux.tar.xz"))')
    agda_version=${agda_asset#Agda-}
    agda_version=${agda_version%-linux.tar.xz}
    ;;
  mikan)
    mikan_rev=$(curl -fsSL https://codeberg.org/api/v1/repos/1lab/mikan/branches/main | jq -r .commit.id)
    [[ $mikan_rev =~ ^[0-9a-f]{40}$ ]] || { echo "could not resolve mikan main" >&2; exit 1; }
    agda_version=mikan-${mikan_rev:0:7}
    ;;
  *) usage ;;
esac

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
mkdir -p "$dir/bin" "$dir/cubical"

# agda
if [[ $agda_ch == mikan ]]; then
  # build from source, needs ghc and cabal
  src=$(mktemp -d)
  git -C "$src" init -q
  git -C "$src" fetch -q --depth=1 https://codeberg.org/1lab/mikan "$mikan_rev"
  git -C "$src" checkout -q FETCH_HEAD
  (cd "$src" && cabal update && cabal install exe:mikan -foptimise-heavily \
    --installdir="$dir/mikan" --install-method=copy --overwrite-policy=always)
  # link mikan as agda
  ln -s "$dir/mikan/mikan" "$dir/bin/mikan"
  ln -s "$dir/mikan/mikan" "$dir/bin/agda"
  # unpack data files inside the toolchain dir
  export Mikan_datadir=$dir/mikan-data
  mkdir -p "$Mikan_datadir"
  "$dir/bin/agda" --setup
else
  mkdir -p "$dir/agda"
  gh release download "$agda_tag" -R agda/agda -p "$agda_asset" -O - | tar -xJ -C "$dir/agda"
  agda_bin=$(find "$dir/agda" -type f -name agda | head -n 1)
  chmod +x "$agda_bin"
  ln -s "$agda_bin" "$dir/bin/agda"
fi
"$dir/bin/agda" --version

# cubical
git -C "$dir/cubical" init -q
git -C "$dir/cubical" fetch -q --depth=1 https://github.com/agda/cubical "$cubical_ref"
git -C "$dir/cubical" checkout -q FETCH_HEAD
if ! (cd "$dir/cubical" && "$dir/bin/agda" --build-library); then
  # keep what built, then try only the imported modules
  echo "::warning::cubical $cubical_version does not fully typecheck with $agda_version"
  repo=${GITHUB_WORKSPACE:-$PWD}
  grep -rhoE 'import[[:space:]]+Cubical(\.[^[:space:]();]+)+' "$repo/En" \
    | awk '{ print $2 }' | sort -u \
    | while read -r module; do
        file=$(find "$dir/cubical" -path "$dir/cubical/${module//.//}.*agda" | head -n 1)
        [[ -n $file ]] || continue
        (cd "$dir/cubical" && "$dir/bin/agda" "$file" > /dev/null) \
          || echo "::warning::failed to typecheck $module"
      done
fi

cat > "$dir/versions.env" <<EOV
AGDA_VERSION=$agda_version
CUBICAL_VERSION=$cubical_version
EOV
if [[ $agda_ch == mikan ]]; then
  echo "Mikan_datadir=$dir/mikan-data" >> "$dir/versions.env"
fi

#!/usr/bin/env bash
# install a proof assistant (agda or mikan) + cubical into a toolchain dir
set -euo pipefail

usage() {
  cat <<EOF
usage: $0 [--prover=agda|mikan] [--release=stable|nightly]
       [--cubical=stable|nightly] [--dir=PATH] [--resolve-only]

install a prover + cubical into PATH (default: \$TOOLCHAIN_DIR or ~/toolchain)
defaults: agda, stable, stable
EOF
}

die_usage() {
  echo "error: $1" >&2
  usage >&2
  exit 2
}

prover=agda
release=stable
cubical=stable
dir=${TOOLCHAIN_DIR:-$HOME/toolchain}
resolve_only=false

for arg in "$@"; do
  case $arg in
    --prover=agda | --prover=mikan) prover=${arg#*=} ;;
    --release=stable | --release=nightly) release=${arg#*=} ;;
    --cubical=stable | --cubical=nightly) cubical=${arg#*=} ;;
    --dir=?*) dir=${arg#*=} ;;
    --resolve-only) resolve_only=true ;;
    -h | --help) usage; exit 0 ;;
    *) die_usage "bad argument: $arg" ;;
  esac
done

# resolve prover
case $prover-$release in
  agda-*)
    case $(uname -s)-$(uname -m) in
      Linux-x86_64) platform=linux ;;
      Darwin-arm64) platform=macOS-arm64 ;;
      Darwin-x86_64) platform=macOS-x64 ;;
      *) echo "error: no agda release binary for $(uname -s) $(uname -m)" >&2; exit 1 ;;
    esac
    if [[ $release == stable ]]; then
      agda_tag=$(gh release view -R agda/agda --json tagName -q .tagName)
    else
      agda_tag=nightly
    fi
    agda_asset=$(gh release view "$agda_tag" -R agda/agda --json assets \
      -q ".assets[].name | select(endswith(\"-$platform.tar.xz\"))")
    prover_version=${agda_asset#Agda-}
    prover_version=${prover_version%-"$platform".tar.xz}
    ;;
  mikan-nightly)
    mikan_rev=$(curl -fsSL https://codeberg.org/api/v1/repos/1lab/mikan/branches/main | jq -r .commit.id)
    [[ $mikan_rev =~ ^[0-9a-f]{40}$ ]] || { echo "error: could not resolve mikan main" >&2; exit 1; }
    prover_version=${mikan_rev:0:7}
    ;;
  mikan-stable) die_usage "mikan has no releases, use --release=nightly" ;;
esac

# resolve cubical
if [[ $cubical == stable ]]; then
  cubical_ref=$(gh release view -R agda/cubical --json tagName -q .tagName)
  cubical_version=$cubical_ref
else
  cubical_ref=$(gh api repos/agda/cubical/commits/master -q .sha)
  cubical_version=${cubical_ref:0:7}
fi

key="toolchain/$prover-$release/cubical-$cubical/$prover-$prover_version+cubical-$cubical_version"
echo "prover:  $prover $release ($prover_version)"
echo "cubical: $cubical ($cubical_version)"
echo "key:     $key"
if [[ -n ${GITHUB_OUTPUT:-} ]]; then
  echo "key=$key" >> "$GITHUB_OUTPUT"
fi
$resolve_only && exit 0

# only replace an earlier toolchain dir
if [[ -e $dir && -n $(ls -A "$dir") && ! -f $dir/versions.env ]]; then
  echo "error: $dir is not empty and not a toolchain dir, refusing to replace it" >&2
  exit 1
fi
rm -rf "$dir"
mkdir -p "$dir/bin" "$dir/cubical"

# prover
if [[ $prover == mikan ]]; then
  # build from source
  src=$(mktemp -d)
  git -C "$src" init -q
  git -C "$src" fetch -q --depth=1 https://codeberg.org/1lab/mikan "$mikan_rev"
  git -C "$src" checkout -q FETCH_HEAD
  (cd "$src" && cabal update && cabal install exe:mikan -foptimise-heavily \
    --installdir="$dir/mikan" --install-method=copy --overwrite-policy=always)
  ln -s "$dir/mikan/mikan" "$dir/bin/mikan"
  datadir_var=Mikan_datadir
else
  mkdir -p "$dir/agda"
  gh release download "$agda_tag" -R agda/agda -p "$agda_asset" -O - | tar -xJ -C "$dir/agda"
  agda_bin=$(find "$dir/agda" -type f -name agda | head -n 1)
  chmod +x "$agda_bin"
  ln -s "$agda_bin" "$dir/bin/agda"
  datadir_var=Agda_datadir
fi

# unpack data files inside the toolchain dir
datadir=$dir/$prover-data
mkdir -p "$datadir"
export "$datadir_var=$datadir"
"$dir/bin/$prover" --setup
"$dir/bin/$prover" --version

# cubical
git -C "$dir/cubical" init -q
git -C "$dir/cubical" fetch -q --depth=1 https://github.com/agda/cubical "$cubical_ref"
git -C "$dir/cubical" checkout -q FETCH_HEAD
echo "$dir/cubical/cubical.agda-lib" > "$dir/libraries"
if ! (cd "$dir/cubical" && "$dir/bin/$prover" --build-library); then
  # keep what built, then try only the imported modules
  echo "::warning::cubical $cubical_version does not fully typecheck with $prover $prover_version"
  repo=${GITHUB_WORKSPACE:-$PWD}
  grep -rhoE 'import[[:space:]]+Cubical(\.[^[:space:]();]+)+' "$repo/En" \
    | awk '{ print $2 }' | sort -u \
    | while read -r module; do
        file=$(find "$dir/cubical" -path "$dir/cubical/${module//.//}.*agda" | head -n 1)
        [[ -n $file ]] || continue
        (cd "$dir/cubical" && "$dir/bin/$prover" "$file" > /dev/null) \
          || echo "::warning::failed to typecheck $module"
      done
fi

cat > "$dir/versions.env" <<EOV
PROVER=$prover
PROVER_VERSION=$prover_version
CUBICAL_VERSION=$cubical_version
$datadir_var=$datadir
EOV

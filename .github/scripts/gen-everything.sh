#!/usr/bin/env bash
# print an En.Everything module importing every module under En/
set -euo pipefail

usage() {
  cat <<EOU
usage: $0 [--root=PATH] > En/Everything.agda

print En.Everything importing all modules under PATH/En (default: .)
EOU
}

root=.
for arg in "$@"; do
  case $arg in
    --root=?*) root=${arg#*=} ;;
    -h | --help) usage; exit 0 ;;
    *) echo "error: bad argument: $arg" >&2; usage >&2; exit 2 ;;
  esac
done

echo "module En.Everything where"
echo
(cd "$root" && find En -type f \( -name '*.agda' -o -name '*.lagda*' \)) \
  | sed -E 's/\.l?agda(\.[a-z]+)?$//; s|/|.|g' \
  | grep -vx 'En\.Everything' \
  | LC_ALL=C sort \
  | sed 's/^/import /'

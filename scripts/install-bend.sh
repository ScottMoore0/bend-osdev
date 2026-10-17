#!/usr/bin/env bash
# Installs the Bend release named in BEND_VERSION (linux-x64), after checking
# the downloaded archive against the SHA-256 recorded there.
#   scripts/install-bend.sh [prefix]     (default prefix: ~/.bend)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
read -r ver sha < "$root/BEND_VERSION"
prefix=${1:-$HOME/.bend}
archive="bend-$ver-linux-x64.tar.gz"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
curl --proto '=https' --tlsv1.2 -fsSL -o "$work/$archive" \
  "https://github.com/bendlang/bend/releases/download/v$ver/$archive"
echo "$sha  $work/$archive" | sha256sum -c - > /dev/null
tar -xzf "$work/$archive" -C "$work"
mkdir -p "$prefix/bin"
rm -rf "$prefix/bend2" "$prefix/guide"
mv "$work/bend/bend2" "$work/bend/guide" "$prefix/"
mv -f "$work/bend/bin/bend" "$prefix/bin/bend"
echo "installed Bend $ver at $prefix/bin/bend"

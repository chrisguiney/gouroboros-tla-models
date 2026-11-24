#!/usr/bin/env bash
# Checks every configuration in one model directory and says whether each
# one did what it is supposed to:
#   - a config whose name ends in Bug.cfg is EXPECTED TO FAIL (a mutation,
#     a known bug, or a reachability probe), so it must report a violation
#     or a deadlock;
#   - every other config must pass.
# A config names its module on a "\* SPEC: Name.tla" line; without one, the
# module with the config's own name is used.
#
# Usage: scripts/run-model.sh specs/06-blockfetch
set -uo pipefail

dir="${1:?usage: scripts/run-model.sh specs/<model-directory>}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root/$dir" || exit 2

ok=0
wrong=0
for cfg in *.cfg; do
  name="${cfg%.cfg}"
  tla="$(sed -n 's/^\\\* *SPEC: *//p' "$cfg")"
  tla="${tla:-$name.tla}"
  if "$root/bin/tlc" -workers auto -config "$cfg" "$tla" >"/tmp/run-model.$$.out" 2>&1; then
    passed=yes
  else
    passed=no
  fi
  rm -rf states
  case "$name" in
    *Bug) expected=no ;;
    *)    expected=yes ;;
  esac
  if [[ "$passed" == "$expected" ]]; then
    ok=$((ok + 1))
    [[ "$expected" == yes ]] && echo "  pass   $cfg" || echo "  fails  $cfg (as expected)"
  else
    wrong=$((wrong + 1))
    echo "  WRONG  $cfg: expected $([[ $expected == yes ]] && echo pass || echo failure)"
    grep -E 'violated|Deadlock|Error' "/tmp/run-model.$$.out" | head -3 | sed 's/^/         /'
  fi
done
rm -f "/tmp/run-model.$$.out"
echo "$dir: $ok as expected, $wrong wrong"
[[ "$wrong" -eq 0 ]]

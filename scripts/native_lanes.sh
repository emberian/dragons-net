#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# The native lanes, in order, each with its log in build/evidence/. check_all.sh and CI both run
# all of them from this one list. Named lanes run alone; the nightly run uses this to start each
# on a fresh machine. The compiler is the one CAKE names, or else the pinned release. A lane that
# passed on the inputs it read is not run again (scripts/once.py); DN_ONCE=none runs it untraced.
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONSAFEPATH=1
lanes=(native baseline entry server framing grammar accept session nntp crash faults parser fuzz)
# Lanes that mount FUSE, run only by name, where it may be mounted (CI's lazyfs job). FUSE's mount
# helpers look up /etc/mtab, the mount table, which a trace cannot hold still: such a lane is not
# run again on a tree it passed on.
fuse=(power)
script_of() {
  case $1 in
    native) script=(scripts/native_check.py) ;;
    baseline) script=(scripts/native_baseline.py) ;;
    entry) script=(scripts/entry_bench.py check) ;;
    server) script=(scripts/server_check.py) ;;
    framing) script=(scripts/framing_check.py) ;;
    grammar) script=(scripts/grammar_check.py) ;;
    accept) script=(scripts/accept_check.py) ;;
    session) script=(scripts/session_native.py) ;;
    nntp) script=(scripts/nntp_check.py) ;;
    crash) script=(scripts/crash_check.py) ;;
    faults) script=(scripts/faults_check.py) ;;
    power) script=(scripts/power_check.py) ;;
    parser) script=(scripts/parser_contract.py) ;;
    fuzz) script=(scripts/native_fuzz.py) ;;
    *)
      echo "native_lanes.sh: no lane named '$1'; the lanes are ${lanes[*]} ${fuse[*]}" >&2
      exit 2
      ;;
  esac
}
if (($#)); then chosen=("$@"); else chosen=("${lanes[@]}"); fi
# A misspelt name would otherwise run nothing and pass.
for name in "${chosen[@]}"; do script_of "$name"; done
cake="${CAKE:-}"
if [[ -z "$cake" ]]; then cake=$(python3 scripts/bootstrap_tool.py cake); fi
mkdir -p build/evidence
# The pinned tools a lane takes, put in place first and untraced: a lane that installed one would
# read what it wrote, and so would run every time.
tools() {
  case $1 in
    grammar) python3 scripts/bootstrap_tool.py abnfgen ;;
    crash | faults) python3 scripts/bootstrap_tool.py libfiu ;;
    power) python3 scripts/bootstrap_tool.py lazyfs && python3 scripts/bootstrap_tool.py libfiu ;;
  esac >/dev/null
}
lane() {
  local name=$1 key
  script_of "$name"
  tools "$name"
  run=(python3 "${script[@]}" --cake "$cake")
  if [[ ${DN_ONCE:-} == none ]]; then
    "${run[@]}" 2>&1 | tee "build/evidence/$name.log"
  elif [[ " ${fuse[*]} " == *" $name "* ]]; then
    if key=$(python3 scripts/once.py check "lane-$name" -- "${run[@]}"); then return 0; fi
    [[ $key =~ ^[0-9a-f]{64}$ ]] || { echo "native_lanes.sh: no key of lane-$name" >&2; exit 1; }
    "${run[@]}" 2>&1 | tee "build/evidence/$name.log"
    python3 scripts/once.py stamp "lane-$name" "$key"
  else
    python3 scripts/once.py run "lane-$name" --log "build/evidence/$name.log" -- "${run[@]}"
  fi
}
if ((${DN_PARALLEL:-1} < 2 || ${#chosen[@]} < 2)); then
  for name in "${chosen[@]}"; do lane "$name"; done
  exit 0
fi
# DN_PARALLEL lanes at a time, the longest first, each one's output shown whole once all are done;
# an interrupt ends every lane running.
trap 'trap - INT TERM; kill 0' INT TERM
longest=(nntp session parser framing grammar baseline fuzz accept faults power crash server entry native)
ordered=()
for name in "${longest[@]}" "${chosen[@]}"; do
  if [[ " ${chosen[*]} " == *" $name "* && " ${ordered[*]} " != *" $name "* ]]; then ordered+=("$name"); fi
done
chosen=("${ordered[@]}")
started=0
for name in "${chosen[@]}"; do
  # Once as many run as may, each next one waits for one of them to end.
  if ((started >= DN_PARALLEL)); then wait -n || true; fi
  started=$((started + 1))
  (
    set +e
    (set -e; lane "$name") >"build/evidence/$name.out" 2>&1
    echo $? >"build/evidence/$name.status"
  ) &
done
wait
status=0
for name in "${chosen[@]}"; do
  cat "build/evidence/$name.out"
  if [[ $(<"build/evidence/$name.status") != 0 ]]; then
    echo "native_lanes.sh: the lane $name failed" >&2
    status=1
  fi
done
exit "$status"

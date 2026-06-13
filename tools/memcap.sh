#!/usr/bin/env bash
# memcap.sh — detect available memory and recommend an in-flight subagent cap.
#
# Used by the manager (and `/goal` skill) to decide how many concurrent opus
# subagents to dispatch without OOMing the box. Per agent ≈ 8 GB (Lean LSP +
# lake build + worktree files + temp), so cap = min(6, max(1, available_GB // 8)).
#
# Detection priority — SMALLEST limit wins:
#   1. $SLURM_MEM_PER_NODE  — HPC SLURM allocation (in MB).
#   2. /sys/fs/cgroup/memory.max  (cgroup v2) or memory.limit_in_bytes (v1) — containers / WSL2.
#   3. /proc/meminfo MemAvailable  — bare-metal fallback.
#
# WHY NOT MemTotal: on shared HPC nodes /proc/meminfo MemTotal reads node-physical
# (e.g. 503 GB on Duke DCC) regardless of the per-job SLURM allocation (e.g. 128 GB).
# Using MemTotal as the cap basis would OOM-kill on smaller per-job allocations.
#
# Usage:
#   ./tools/memcap.sh            # one-line summary: cap=N available_gb=M source=...
#   ./tools/memcap.sh --json     # JSON object
#   ./tools/memcap.sh --verbose  # show full detection process
#   ./tools/memcap.sh --cap-only # just the cap number, for shell math
#
# Cap formula tunable via env:
#   GB_PER_AGENT (default 8)  — RAM budget per concurrent agent.
#   MAX_CAP      (default 6)  — hard ceiling regardless of memory.

set -euo pipefail

GB_PER_AGENT="${GB_PER_AGENT:-8}"
MAX_CAP="${MAX_CAP:-6}"

mode="default"
case "${1:-}" in
  --json)     mode="json" ;;
  --verbose)  mode="verbose" ;;
  --cap-only) mode="cap-only" ;;
  -h|--help)
    sed -n '2,30p' "$0" | sed 's/^# \?//'
    exit 0
    ;;
  "") ;;
  *)
    echo "Unknown argument: $1" >&2
    echo "Try: $0 --help" >&2
    exit 1
    ;;
esac

# --- Source 1: SLURM ---
slurm_mb=""
if [[ -n "${SLURM_MEM_PER_NODE:-}" ]]; then
  slurm_mb="$SLURM_MEM_PER_NODE"
fi

# --- Source 2: cgroup ---
cgroup_bytes=""
if [[ -r /sys/fs/cgroup/memory.max ]]; then
  v=$(cat /sys/fs/cgroup/memory.max)
  if [[ "$v" != "max" ]]; then
    cgroup_bytes="$v"
  fi
elif [[ -r /sys/fs/cgroup/memory/memory.limit_in_bytes ]]; then
  v=$(cat /sys/fs/cgroup/memory/memory.limit_in_bytes)
  # cgroup v1 reports a huge sentinel when unlimited; treat anything ≥ 8 EiB as "unset".
  if [[ "$v" -lt 9000000000000000000 ]]; then
    cgroup_bytes="$v"
  fi
fi

# --- Source 3: /proc/meminfo MemAvailable ---
meminfo_kb=""
if [[ -r /proc/meminfo ]]; then
  meminfo_kb=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
fi

# --- Pick smallest limit (in GB) ---
candidates=()  # array of "GB:source"
[[ -n "$slurm_mb"     ]] && candidates+=("$((slurm_mb / 1024)):SLURM_MEM_PER_NODE")
[[ -n "$cgroup_bytes" ]] && candidates+=("$((cgroup_bytes / 1024 / 1024 / 1024)):cgroup")
[[ -n "$meminfo_kb"   ]] && candidates+=("$((meminfo_kb / 1024 / 1024)):/proc/meminfo")

if [[ ${#candidates[@]} -eq 0 ]]; then
  echo "memcap.sh: no memory source detected" >&2
  exit 2
fi

# Find the minimum.
min_gb=999999
min_src="unknown"
for c in "${candidates[@]}"; do
  gb="${c%%:*}"
  src="${c##*:}"
  if (( gb < min_gb )); then
    min_gb="$gb"
    min_src="$src"
  fi
done

# Cap formula.
raw_cap=$(( min_gb / GB_PER_AGENT ))
cap=$(( raw_cap < 1 ? 1 : raw_cap ))
cap=$(( cap > MAX_CAP ? MAX_CAP : cap ))

case "$mode" in
  cap-only)
    echo "$cap"
    ;;
  json)
    printf '{"cap": %d, "available_gb": %d, "source": "%s", "gb_per_agent": %d, "max_cap": %d}\n' \
      "$cap" "$min_gb" "$min_src" "$GB_PER_AGENT" "$MAX_CAP"
    ;;
  verbose)
    echo "memcap.sh — detection trace:"
    for c in "${candidates[@]}"; do
      gb="${c%%:*}"
      src="${c##*:}"
      marker="  "
      [[ "$src" == "$min_src" ]] && marker="* "
      echo "$marker$src: $gb GB"
    done
    echo ""
    echo "Smallest limit:    $min_gb GB (from $min_src)"
    echo "Per-agent budget:  $GB_PER_AGENT GB (env GB_PER_AGENT)"
    echo "Max-cap ceiling:   $MAX_CAP (env MAX_CAP)"
    echo "Recommended cap:   min($MAX_CAP, max(1, $min_gb / $GB_PER_AGENT)) = $cap"
    ;;
  default)
    echo "cap=$cap available_gb=$min_gb source=$min_src"
    ;;
esac

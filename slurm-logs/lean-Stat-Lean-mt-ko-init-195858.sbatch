#!/bin/bash
#SBATCH --job-name=lean-ko-init-195858
#SBATCH --partition=shared
#SBATCH --time=0-02:00
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --output=/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-ko-init/slurm-logs/%x-%j.out
#SBATCH --error=/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-ko-init/slurm-logs/%x-%j.err
#SBATCH --no-requeue

set -uo pipefail
source "/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/lean-on-fasrc/env.Stat-Lean.sh"

mkdir -p "/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-ko-init/slurm-logs"
echo "[2026-06-13T19:58:58-04:00] host=holy7c04103.rc.fas.harvard.edu wt=/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-ko-init target=StatLean.MultipleTesting.Knockoff.Initial cpus=$SLURM_CPUS_PER_TASK mem=24G"
cd "/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-ko-init"

echo "--- git status ---"
git rev-parse HEAD
git status --short

echo "--- lake env ---"
elan show || true
lean --version || true
lake --version || true

echo "--- lake build StatLean.MultipleTesting.Knockoff.Initial ---"
START=$SECONDS
export LEAN_NUM_THREADS="$SLURM_CPUS_PER_TASK"
lake build StatLean.MultipleTesting.Knockoff.Initial
RC=$?
ELAPSED=$((SECONDS - START))

echo "--- post-build ---"
echo "exit_code=$RC"
echo "wallclock_seconds=$ELAPSED"
SORRY_LINES="$(grep -c 'declaration uses .sorry' "/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-ko-init/slurm-logs"/*-${SLURM_JOB_ID}.err 2>/dev/null || echo 0)"
echo "sorry_count=$SORRY_LINES"

exit $RC

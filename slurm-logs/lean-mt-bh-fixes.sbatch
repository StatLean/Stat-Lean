#!/bin/bash
#SBATCH --job-name=lean-mt-bh-fixes
#SBATCH --partition=shared
#SBATCH --time=0-02:00
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=24G
#SBATCH --output=slurm-logs/%x-%j.out
#SBATCH --error=slurm-logs/%x-%j.err
#SBATCH --no-requeue

set -uo pipefail
source "/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/lean-on-fasrc/env.Stat-Lean.sh"

mkdir -p slurm-logs
echo "[$(date -Is)] host=$(hostname) wt=/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-bh target=StatLean.MultipleTesting.BenjaminiHochberg cpus=$SLURM_CPUS_PER_TASK mem=24G"
cd "/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-bh"

echo "--- git status ---"
git rev-parse HEAD
git status --short

echo "--- lake env ---"
elan show || true
lean --version || true
lake --version || true

echo "--- lake build StatLean.MultipleTesting.BenjaminiHochberg ---"
START=$SECONDS
export LEAN_NUM_THREADS="$SLURM_CPUS_PER_TASK"
lake build StatLean.MultipleTesting.BenjaminiHochberg
RC=$?
ELAPSED=$((SECONDS - START))

echo "--- post-build ---"
echo "exit_code=$RC"
echo "wallclock_seconds=$ELAPSED"
SORRY_LINES="$(grep -c 'declaration uses .sorry' slurm-logs/*-${SLURM_JOB_ID}.err 2>/dev/null || echo 0)"
echo "sorry_uses_in_err=$SORRY_LINES"

exit $RC

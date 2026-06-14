#!/bin/bash
#SBATCH --job-name=lean-ko-super
#SBATCH --partition=hsph,shared,sapphire,serial_requeue
#SBATCH --time=0-04:00:00
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --output=slurm-ko-super-build.out
#SBATCH --error=slurm-ko-super-build.err
#SBATCH --no-requeue

set -uo pipefail
source "/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/lean-on-fasrc/env.Stat-Lean.sh"

WT="/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/mt-ko-super"
echo "[$(date -Is)] host=$(hostname) wt=${WT} target=StatLean.MultipleTesting.Knockoff.Supermartingale"
cd "${WT}"

echo "--- git status ---"
git rev-parse HEAD
git status --short

echo "--- lake build StatLean.MultipleTesting.Knockoff.Supermartingale ---"
START=$SECONDS
export LEAN_NUM_THREADS="$SLURM_CPUS_PER_TASK"
lake build StatLean.MultipleTesting.Knockoff.Supermartingale
RC=$?
ELAPSED=$((SECONDS - START))

echo "--- post-build ---"
echo "exit_code=$RC"
echo "wallclock_seconds=$ELAPSED"

# Report sorrys
echo "--- sorry inventory ---"
lake build StatLean.MultipleTesting.Knockoff.Supermartingale 2>&1 | grep -i sorry || true

exit $RC

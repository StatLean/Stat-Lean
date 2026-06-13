#!/bin/bash
#SBATCH --job-name=lean-vecnorms-r2
#SBATCH --partition=shared
#SBATCH --time=0-00:40:00
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=24G
#SBATCH --output=slurm-vecnorms-build.out
#SBATCH --error=slurm-vecnorms-build.err
#SBATCH --no-requeue

set -uo pipefail
source "/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/lean-on-fasrc/env.Stat-Lean.sh"

WT="/n/holylabs/LABS/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/hds-vecnorms-r2"
echo "[$(date -Is)] host=$(hostname) wt=${WT} target=StatLean.HighDimensionalStatistics.ForMathlib.VecNorms"
cd "${WT}"

echo "--- git status ---"
git rev-parse HEAD
git status --short

echo "--- lake build StatLean.HighDimensionalStatistics.ForMathlib.VecNorms ---"
START=$SECONDS
export LEAN_NUM_THREADS="$SLURM_CPUS_PER_TASK"
lake build StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
RC=$?
ELAPSED=$((SECONDS - START))

echo "--- post-build ---"
echo "exit_code=$RC"
echo "wallclock_seconds=$ELAPSED"

exit $RC

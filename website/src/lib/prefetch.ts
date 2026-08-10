// Warm the Cytoscape route chunk before it is navigated to. The compact graph
// JSON remains a separate cacheable request and Mathlib data stays on demand,
// so opening the Dependencies / graph pages feels instant.
export const prefetchDependencies = () => import("../pages/Dependencies");
export const prefetchGraphView = () => import("../pages/GraphView");

let warmed = false;
/** Prefetch the dependency-graph chunk once the browser is idle. */
export function warmGraphChunks() {
  if (warmed) return;
  warmed = true;
  const run = () => {
    prefetchDependencies();
  };
  if ("requestIdleCallback" in window) {
    (window as any).requestIdleCallback(run, { timeout: 2500 });
  } else {
    setTimeout(run, 1500);
  }
}

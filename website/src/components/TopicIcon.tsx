import type { CategoryId } from "../lib/types";

/** Minimal line icons keyed to each topic, drawn in the current accent color. */
export function TopicIcon({
  id,
  className = "",
}: {
  id: CategoryId;
  className?: string;
}) {
  const common = {
    className,
    viewBox: "0 0 48 48",
    fill: "none",
    stroke: "currentColor",
    strokeWidth: 1.6,
    strokeLinecap: "round" as const,
    strokeLinejoin: "round" as const,
    "aria-hidden": true,
  };
  switch (id) {
    case "parametric":
      // Gaussian bell curve over an axis (LAN / normal limit)
      return (
        <svg {...common}>
          <path d="M5 36h38" />
          <path d="M7 35c6 0 7-22 17-22s11 22 17 22" opacity={0.55} />
          <path d="M24 13v23" strokeDasharray="2 3" opacity={0.7} />
        </svg>
      );
    case "semiparametric":
      // 4D hypercube (tesseract) — orthographic wireframe projection
      return (
        <svg {...common}>
          <path d="M5 5h38v38H5z" />
          <path d="M16 16h16v16H16z" opacity={0.7} />
          <path d="M5 5l11 11M43 5l-11 11M43 43l-11-11M5 43l11-11" opacity={0.55} />
        </svg>
      );
    case "concentration":
      // sharply peaked density with a measure bracket — mass concentrates at the mean
      return (
        <svg {...common}>
          <path d="M5 34h38" />
          <path d="M8 34c8 0 6-20 16-20s8 20 16 20" />
          <path d="M19 38h10" opacity={0.7} />
          <path d="M19 36v4M29 36v4" opacity={0.7} />
        </svg>
      );
    case "highdim":
      // sparse signal — a grid with only a few active coordinates
      return (
        <svg {...common}>
          <rect x="8" y="8" width="32" height="32" rx="2" />
          <path d="M8 19h32M8 30h32M19 8v32M30 8v32" opacity={0.4} />
          <circle cx="13.5" cy="13.5" r="2.1" fill="currentColor" stroke="none" />
          <circle cx="35" cy="24.5" r="2.1" fill="currentColor" stroke="none" />
          <circle cx="24" cy="35" r="2.1" fill="currentColor" stroke="none" />
        </svg>
      );
    case "multipletesting":
      // two overlapping densities split by a decision threshold
      return (
        <svg {...common}>
          <path d="M4 34h40" />
          <path d="M6 34c7 0 6-16 13-16s6 16 13 16" opacity={0.75} />
          <path d="M16 34c7 0 6-16 13-16s6 16 13 16" opacity={0.75} />
          <path d="M27 13v23" strokeDasharray="2 3" opacity={0.8} />
        </svg>
      );
    case "minimaxity":
      // Le Cam two-point method — two separated hypotheses
      return (
        <svg {...common}>
          <circle cx="12" cy="24" r="5.5" />
          <circle cx="36" cy="24" r="5.5" />
          <path d="M19.5 24h9" />
          <path d="M19.5 24l3-3M19.5 24l3 3M28.5 24l-3-3M28.5 24l-3 3" opacity={0.8} />
        </svg>
      );
    case "optimization":
      // gradient descent — iterates rolling into a convex bowl
      return (
        <svg {...common}>
          <path d="M7 9c2 22 12 28 17 28s15-6 17-28" />
          <path d="M5 38h38" opacity={0.4} />
          <circle cx="24" cy="35.5" r="2.6" fill="currentColor" stroke="none" />
          <circle cx="14.5" cy="20" r="1.7" fill="currentColor" stroke="none" opacity={0.55} />
          <circle cx="19.5" cy="30" r="1.7" fill="currentColor" stroke="none" opacity={0.8} />
        </svg>
      );
    case "bayesian":
      // Bayesian updating — a broad (dashed) prior sharpened into a peaked posterior
      return (
        <svg {...common}>
          <path d="M5 34h38" />
          <path d="M6 34c10 0 8-14 18-14s8 14 18 14" strokeDasharray="2 3" opacity={0.55} />
          <path d="M14 34c6 0 5-20 12-20s6 20 12 20" />
        </svg>
      );
    case "nonparametric":
      // kernel density estimate — a smooth bimodal curve over a rug of data points
      return (
        <svg {...common}>
          <path d="M5 36h38" />
          <path d="M6 36c4 0 5-11 9-11s4 6 8 6 4-18 9-18 8 23 12 23" />
          <path d="M11 39v3M17 39v3M23 39v3M30 39v3M34 39v3M38 39v3" opacity={0.7} />
        </svg>
      );
    case "statisticalmodels":
      // Kaplan–Meier survival curve — descending step function with a censoring tick
      return (
        <svg {...common}>
          <path d="M5 40h38" />
          <path d="M6 9h8v7h7v7h7v8h8v5h7" />
          <path d="M25 20v-4" opacity={0.7} />
          <path d="M34 28v-4" opacity={0.7} />
        </svg>
      );
    case "probability":
      // compass star — assorted foundational results (miscellaneous)
      return (
        <svg {...common}>
          <circle cx="24" cy="24" r="16" opacity={0.5} />
          <path d="M24 9l4 11 11 4-11 4-4 11-4-11-11-4 11-4z" />
        </svg>
      );
    case "hypothesistesting":
      // null density cut by a critical value, with the rejection region beyond it
      return (
        <svg {...common}>
          <path d="M5 34h38" />
          <path d="M7 34c8 0 6-20 15-20s7 20 15 20" />
          <path d="M31 34V16" strokeDasharray="2 3" opacity={0.85} />
          <path d="M32.5 34v-3.4M35 34v-2.5M37.5 34v-1.7" opacity={0.7} />
        </svg>
      );
    case "pointestimation":
      // target on the parameter with an estimate off-centre — bias and variance
      return (
        <svg {...common}>
          <circle cx="24" cy="24" r="15" opacity={0.45} />
          <circle cx="24" cy="24" r="7.5" opacity={0.7} />
          <path d="M24 20v8M20 24h8" opacity={0.5} />
          <circle cx="30" cy="18.5" r="2.5" fill="currentColor" stroke="none" />
        </svg>
      );
    case "timeseries":
      // A sampled path with a marked lag (autocovariance / spectrum)
      return (
        <svg {...common}>
          <path d="M5 38h38" />
          <path d="M6 30c3-8 5 6 8-2s5 10 8 1 5 7 8-3 5 5 7 1" opacity={0.85} />
          <path d="M16 38v4M32 38v4" opacity={0.6} />
          <path d="M16 42h16" strokeDasharray="2 3" opacity={0.7} />
        </svg>
      );
    case "causal":
      // Treatment → outcome with a confounder arrow (a DAG)
      return (
        <svg {...common}>
          <circle cx="11" cy="34" r="4" />
          <circle cx="37" cy="34" r="4" />
          <circle cx="24" cy="12" r="4" />
          <path d="M15 34h18" />
          <path d="M21 15 14 30" opacity={0.7} />
          <path d="M27 15 34 30" opacity={0.7} />
        </svg>
      );
    case "statlearning":
      // A separating boundary between two point clouds (classification)
      return (
        <svg {...common}>
          <path d="M8 40 40 8" />
          <circle cx="15" cy="16" r="2.4" opacity={0.85} />
          <circle cx="23" cy="12" r="2.4" opacity={0.85} />
          <circle cx="14" cy="25" r="2.4" opacity={0.85} />
          <path d="M31 33h4M33 31v4" opacity={0.85} />
          <path d="M22 38h4M24 36v4" opacity={0.85} />
          <path d="M34 23h4M36 21v4" opacity={0.85} />
        </svg>
      );
    case "expdesign":
      // A blocked design grid with randomized allocation marks
      return (
        <svg {...common}>
          <rect x="7" y="10" width="34" height="28" rx="2" />
          <path d="M18 10v28M29 10v28M7 19h34M7 29h34" opacity={0.5} />
          <circle cx="12.5" cy="14.5" r="1.8" opacity={0.9} />
          <circle cx="23.5" cy="24" r="1.8" opacity={0.9} />
          <circle cx="34.5" cy="33.5" r="1.8" opacity={0.9} />
          <circle cx="34.5" cy="14.5" r="1.8" opacity={0.9} />
        </svg>
      );
    default:
      // Never render an empty card: fall back to a neutral mark for any new topic.
      return (
        <svg {...common}>
          <circle cx="24" cy="24" r="15" opacity={0.5} />
          <path d="M24 15v18M15 24h18" opacity={0.7} />
        </svg>
      );
  }
}

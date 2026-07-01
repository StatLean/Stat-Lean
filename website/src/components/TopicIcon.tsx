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
    case "hypothesis":
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
    case "probability":
      // compass star — assorted foundational results (miscellaneous)
      return (
        <svg {...common}>
          <circle cx="24" cy="24" r="16" opacity={0.5} />
          <path d="M24 9l4 11 11 4-11 4-4 11-4-11-11-4 11-4z" />
        </svg>
      );
  }
}

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
    case "empirical":
      // empirical CDF step function (Glivenko–Cantelli / Donsker)
      return (
        <svg {...common}>
          <path d="M6 38h6v-7h7v-7h7v-7h9" />
          <path d="M6 38V9" opacity={0.4} />
          <path d="M6 38h36" opacity={0.4} />
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

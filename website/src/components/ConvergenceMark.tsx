/** Decorative "convergence to a limit" motif: nested arcs collapsing to a point. */
export function ConvergenceMark({
  className = "",
  rings = 5,
}: {
  className?: string;
  rings?: number;
}) {
  return (
    <svg viewBox="0 0 100 100" className={className} aria-hidden="true">
      {Array.from({ length: rings }).map((_, i) => {
        const r = 46 - (i * 44) / rings;
        return (
          <circle
            key={i}
            cx="50"
            cy="50"
            r={r}
            fill="none"
            stroke="currentColor"
            strokeWidth={0.6}
            opacity={0.25 + (i / rings) * 0.6}
          />
        );
      })}
      <circle cx="50" cy="50" r="1.6" fill="currentColor" />
    </svg>
  );
}

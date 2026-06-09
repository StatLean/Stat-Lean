import { useMemo } from "react";
import { renderInformal } from "../lib/render";

/** Renders an informal HTML string with inline/display KaTeX. */
export function MathText({
  html,
  className = "",
  onMount,
}: {
  html: string;
  className?: string;
  onMount?: (el: HTMLDivElement | null) => void;
}) {
  const rendered = useMemo(() => renderInformal(html), [html]);
  return (
    <div
      ref={onMount}
      className={className}
      dangerouslySetInnerHTML={{ __html: rendered }}
    />
  );
}

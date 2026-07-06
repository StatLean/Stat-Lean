import { useMemo } from "react";
import { renderInformal, renderReference } from "../lib/render";

/**
 * Renders an HTML string with KaTeX. With `markdown` set, also turns
 * `*italic*` / `**bold**` into emphasis (for reference/bibliographic text).
 */
export function MathText({
  html,
  className = "",
  markdown = false,
  onMount,
}: {
  html: string;
  className?: string;
  markdown?: boolean;
  onMount?: (el: HTMLDivElement | null) => void;
}) {
  const rendered = useMemo(
    () => (markdown ? renderReference(html) : renderInformal(html)),
    [html, markdown],
  );
  return (
    <div
      ref={onMount}
      className={className}
      dangerouslySetInnerHTML={{ __html: rendered }}
    />
  );
}

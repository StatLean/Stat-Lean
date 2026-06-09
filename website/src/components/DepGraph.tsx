import { useEffect, useRef, useState } from "react";
import cytoscape from "cytoscape";
import dagre from "cytoscape-dagre";
import { loadGraph, getResult } from "../lib/data";
import { docUrlForNode } from "../lib/site";
import { AREA_VAR, AREA_LABEL, nodeArea, nodeShape, type Area } from "../lib/graphArea";
import type { CategoryId, DepGraph as DepGraphData } from "../lib/types";

cytoscape.use(dagre);

/** Raw "r g b" triplet behind a CSS custom property. */
function triplet(name: string): string {
  const v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  return v || "136 136 136";
}
// Cytoscape's color parser needs comma-separated rgb()/rgba(), not the
// space-separated CSS-4 syntax — otherwise it silently falls back to a default.
const csv = (t: string) => t.trim().split(/\s+/).join(",");
const rgb = (t: string) => `rgb(${csv(t)})`;
const rgba = (t: string, a: number) => `rgba(${csv(t)},${a})`;
/** relative luminance (0–255) of an "r g b" triplet */
function lum(t: string): number {
  const [r, g, b] = t.split(/\s+/).map(Number);
  return 0.2126 * r + 0.7152 * g + 0.0722 * b;
}
/** a readable text triplet (dark or light) for a given fill triplet */
const contrastTriplet = (t: string) => (lum(t) > 145 ? "26 24 20" : "247 243 235");

export function DepGraph({ id, fill: fillMode = false }: { id: string; fill?: boolean }) {
  const elRef = useRef<HTMLDivElement>(null);
  const [graph, setGraph] = useState<DepGraphData | null>(null);
  const [state, setState] = useState<"loading" | "ready" | "empty">("loading");

  useEffect(() => {
    let alive = true;
    loadGraph(id).then((g) => {
      if (!alive) return;
      if (g && g.nodes.length > 0) {
        setGraph(g);
        setState("ready");
      } else {
        setState("empty");
      }
    });
    return () => {
      alive = false;
    };
  }, [id]);

  useEffect(() => {
    if (state !== "ready" || !graph || !elRef.current) return;

    const rootArea: CategoryId = getResult(id)?.category ?? "semiparametric";
    const ink = triplet("--ink");
    const inkSoft = triplet("--ink-soft");
    const bg = triplet("--bg");
    const rule = triplet("--rule");

    // precompute area-triplet per area, once
    const areaTriplet: Record<Area, string> = {
      parametric: triplet(AREA_VAR.parametric),
      semiparametric: triplet(AREA_VAR.semiparametric),
      empirical: triplet(AREA_VAR.empirical),
      probability: triplet(AREA_VAR.probability),
      external: triplet(AREA_VAR.external),
    };

    const nodeEls = graph.nodes.map((n) => {
      const area = nodeArea(n, rootArea);
      const at = areaTriplet[area];
      const isRoot = n.kind === "root";

      // Color = area (Mathlib / external = yellow). Every node gets a solid area
      // fill with a contrast label; the root carries a thick ink ring.
      const fill = rgb(at);
      const labelColor = rgb(contrastTriplet(at));
      const border = isRoot ? rgb(ink) : rgba(at, 0.55);
      const borderWidth = isRoot ? 3 : 1;

      return {
        data: {
          id: n.id,
          label: n.label,
          full: n.full,
          module: n.module,
          shape: nodeShape(n),
          fill,
          border,
          borderWidth,
          labelColor,
          fontWeight: isRoot ? 600 : 400,
        },
      };
    });

    const cy = cytoscape({
      container: elRef.current,
      elements: [
        ...nodeEls,
        // reverse: draw the arrow from a dependency TO the result it supports
        // (premise → conclusion), so arrowheads point at what is implied.
        ...graph.edges.map((e) => ({
          data: { id: `${e.target}~>${e.source}`, source: e.target, target: e.source },
        })),
      ],
      style: [
        {
          selector: "node",
          style: {
            label: "data(label)",
            "font-family": "JetBrains Mono, monospace",
            "font-size": 11,
            "font-weight": "data(fontWeight)",
            color: "data(labelColor)",
            "text-valign": "center",
            "text-halign": "center",
            "text-max-width": "210px",
            shape: "data(shape)",
            width: "label",
            height: "label",
            padding: "9px",
            "background-color": "data(fill)",
            "border-width": "data(borderWidth)",
            "border-color": "data(border)",
            "border-style": "solid",
          },
        },
        {
          selector: "edge",
          style: {
            width: 1.4,
            "line-color": rgb(rule),
            "target-arrow-color": rgb(rule),
            "target-arrow-shape": "triangle",
            "arrow-scale": 0.8,
            "curve-style": "bezier",
            opacity: 0.85,
          },
        },
        {
          selector: "node:active",
          style: { "overlay-opacity": 0.1 },
        },
      ] as any,
      layout: {
        name: "dagre",
        rankDir: "TB", // vertical: foundations on top, the ultimate result at the bottom
        nodeSep: 18,
        rankSep: 64,
        edgeSep: 10,
      } as cytoscape.LayoutOptions,
      minZoom: 0.2,
      maxZoom: 2.5,
      wheelSensitivity: 0.25,
    });

    // every node links to its doc-gen4 page
    cy.on("tap", "node", (evt) => {
      const d = evt.target.data();
      if (d.module && d.full)
        window.open(docUrlForNode(d.module, d.full), "_blank", "noopener");
    });
    cy.on("mouseover", "node", () => {
      if (elRef.current) elRef.current.style.cursor = "pointer";
    });
    cy.on("mouseout", "node", () => {
      if (elRef.current) elRef.current.style.cursor = "default";
    });

    cy.fit(undefined, 32);
    return () => cy.destroy();
  }, [state, graph, id]);

  if (state === "loading")
    return (
      <div className="h-72 grid place-items-center text-ink-faint font-sans text-sm">
        Loading dependency graph…
      </div>
    );

  if (state === "empty")
    return (
      <div className="h-44 grid place-items-center text-center px-6">
        <p className="font-serif text-ink-soft">
          The dependency graph for this result has not been generated yet.
          <br />
          <span className="text-sm text-ink-faint font-sans">
            Run <code className="font-mono">lake exe deps</code> to build it.
          </span>
        </p>
      </div>
    );

  return (
    <div className={fillMode ? "h-full flex flex-col min-h-0" : ""}>
      <div
        ref={elRef}
        className={
          (fillMode ? "flex-1 min-h-0" : "h-[28rem]") +
          " w-full rounded-lg border hairline bg-parchment-sunk"
        }
      />
      <p className="mt-3 text-xs font-sans text-ink-faint shrink-0">
        Arrows point from a premise to the result it implies · click any node to open its{" "}
        <strong>doc-gen4</strong> page · drag to pan · scroll to zoom
      </p>
      <div className="mt-2 flex flex-wrap gap-x-5 gap-y-2 text-xs font-sans text-ink-soft shrink-0">
        <ShapeKey shape="rectangle" label="User-facing theorem" />
        <ShapeKey shape="ellipse" label="Auxiliary lemma" />
        <ShapeKey shape="round" label="Definition" />
      </div>
      <div className="mt-2 flex flex-wrap gap-x-5 gap-y-2 text-xs font-sans text-ink-soft shrink-0">
        {(["parametric", "semiparametric", "empirical", "probability", "external"] as Area[]).map(
          (a) => (
            <ColorKey key={a} area={a} />
          ),
        )}
      </div>
    </div>
  );
}

function ShapeKey({
  shape,
  label,
}: {
  shape: "rectangle" | "ellipse" | "round";
  label: string;
}) {
  const radius =
    shape === "ellipse" ? "9999px" : shape === "round" ? "5px" : "0px";
  const w = shape === "ellipse" ? "20px" : "15px";
  return (
    <span className="inline-flex items-center gap-1.5">
      <span
        className="inline-block h-3.5 border-[1.5px] border-ink-soft"
        style={{ width: w, borderRadius: radius }}
      />
      {label}
    </span>
  );
}

function ColorKey({ area }: { area: Area }) {
  return (
    <span className="inline-flex items-center gap-1.5">
      <span
        className="inline-block w-3.5 h-3.5 rounded-[3px]"
        style={{
          background: `rgb(var(${AREA_VAR[area]}) / 0.9)`,
          border: `1.5px solid rgb(var(${AREA_VAR[area]}))`,
        }}
      />
      {AREA_LABEL[area]}
    </span>
  );
}

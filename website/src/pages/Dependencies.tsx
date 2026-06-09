import { useEffect, useMemo, useRef, useState } from "react";
import { useNavigate } from "react-router-dom";
import cytoscape from "cytoscape";
import fcose from "cytoscape-fcose";
import { getGlobalGraph } from "../lib/globalGraph";
import { RESULTS } from "../lib/data";
import { CATEGORIES } from "../lib/categories";
import {
  isUserFacing,
  nodeArea,
  nodeShape,
  AREA_VAR,
  AREA_LABEL,
  type Area,
} from "../lib/graphArea";
import { triplet, rgb, rgba, areaTriplets } from "../lib/cyStyle";
import { docUrlForNode } from "../lib/site";
import type { CategoryId } from "../lib/types";

cytoscape.use(fcose);

const FULL_TO_ID = new Map(RESULTS.map((r) => [r.fullName, r.id]));

type DeclFilter = "thm" | "def";

export function Dependencies() {
  const elRef = useRef<HTMLDivElement>(null);
  const cyRef = useRef<cytoscape.Core | null>(null);
  const runLayoutRef = useRef<((eles: cytoscape.Collection) => void) | null>(null);
  const extElsRef = useRef<any[]>([]); // Mathlib elements, added to cy on demand
  const extAddedRef = useRef(false);
  const navigate = useNavigate();

  const graph = useMemo(() => getGlobalGraph(), []);
  const [topics, setTopics] = useState<Set<CategoryId>>(
    () => new Set(CATEGORIES.map((c) => c.id)),
  );
  const [decls, setDecls] = useState<Set<DeclFilter>>(
    () => new Set<DeclFilter>(["thm", "def"]),
  );
  const [showMathlib, setShowMathlib] = useState(false);

  // ---- build the graph once ----
  useEffect(() => {
    if (!elRef.current) return;
    const ats = areaTriplets();
    const ink = triplet("--ink");

    const mkNode = (n: (typeof graph.nodes)[number]) => {
      const area = nodeArea(n, "semiparametric");
      const at = ats[area];
      const emph = isUserFacing(n.full);
      const size = emph ? 19 : area === "external" ? 7 : 10;
      return {
        data: {
          id: n.id,
          label: n.label,
          full: n.full,
          module: n.module,
          area,
          shape: nodeShape(n),
          fill: rgb(at),
          border: emph ? rgb(ink) : rgba(at, 0.5),
          bw: emph ? 2 : 0.6,
          size,
        },
      };
    };
    // Split Mathlib (external) elements out — they're added on demand so the
    // initial graph (the ~198 repo + result nodes) mounts fast.
    const extIds = new Set(
      graph.nodes.filter((n) => nodeArea(n, "semiparametric") === "external").map((n) => n.id),
    );
    const repoNodeEls = graph.nodes.filter((n) => !extIds.has(n.id)).map(mkNode);
    const extNodeEls = graph.nodes.filter((n) => extIds.has(n.id)).map(mkNode);
    const repoEdgeEls: any[] = [];
    const extEdgeEls: any[] = [];
    for (const e of graph.edges) {
      const el = { data: { id: `${e.target}~${e.source}`, source: e.target, target: e.source } };
      (extIds.has(e.source) || extIds.has(e.target) ? extEdgeEls : repoEdgeEls).push(el);
    }
    extElsRef.current = [...extNodeEls, ...extEdgeEls];
    extAddedRef.current = false;

    const cy = cytoscape({
      container: elRef.current,
      elements: [...repoNodeEls, ...repoEdgeEls],
      style: [
        {
          selector: "node",
          style: {
            width: "data(size)",
            height: "data(size)",
            shape: "data(shape)",
            "background-color": "data(fill)",
            "border-width": "data(bw)",
            "border-color": "data(border)",
            label: "",
          },
        },
        {
          selector: "node.hl",
          style: {
            "border-width": 2.5,
            "border-color": rgb(ink),
            "z-index": 999,
          },
        },
        {
          selector: "edge",
          style: {
            width: 0.6,
            "line-color": rgb(triplet("--rule")),
            "curve-style": "straight",
            opacity: 0.28,
          },
        },
        { selector: ".faded", style: { opacity: 0.05, "text-opacity": 0 } },
      ] as any,
      minZoom: 0.05,
      maxZoom: 4,
      wheelSensitivity: 0.2,
    });
    cyRef.current = cy;

    // floating name tooltip
    const tip = document.createElement("div");
    tip.className =
      "pointer-events-none absolute z-20 hidden px-2 py-1 rounded-md text-[11px] font-mono " +
      "bg-parchment-panel text-ink border hairline shadow-lg whitespace-nowrap -translate-x-1/2";
    elRef.current.appendChild(tip);

    cy.on("mouseover", "node", (e) => {
      const nb = e.target.closedNeighborhood();
      cy.elements().difference(nb).addClass("faded");
      e.target.addClass("hl");
      const p = e.target.renderedPosition();
      const rid = FULL_TO_ID.get(e.target.data("full"));
      tip.textContent = (rid ? "★ " : "") + e.target.data("label");
      tip.style.left = `${p.x}px`;
      tip.style.top = `${p.y - e.target.renderedHeight() / 2 - 8}px`;
      tip.style.transform = "translate(-50%, -100%)";
      tip.style.display = "block";
      elRef.current!.style.cursor = "pointer";
    });
    cy.on("mouseout", "node", (e) => {
      cy.elements().removeClass("faded");
      e.target.removeClass("hl");
      tip.style.display = "none";
      elRef.current!.style.cursor = "default";
    });

    cy.on("tap", "node", (e) => {
      const d = e.target.data();
      const rid = FULL_TO_ID.get(d.full);
      if (rid) navigate(`/result/${rid}`);
      else if (d.module && d.full)
        window.open(docUrlForNode(d.module, d.full), "_blank", "noopener");
    });

    // ---- continuous spring-drift so nodes keep gently moving (edge tension) ----
    const drift = {
      raf: 0,
      active: false,
      last: 0,
      nodes: cy.collection() as cytoscape.NodeCollection,
      anchors: new Map<string, { x: number; y: number }>(),
      vel: new Map<string, { x: number; y: number }>(),
    };
    const tick = () => {
      drift.raf = requestAnimationFrame(tick);
      if (!drift.active || document.hidden) return;
      const now = performance.now();
      if (now - drift.last < 32) return; // ~30fps
      drift.last = now;
      cy.batch(() => {
        drift.nodes.forEach((n) => {
          if (n.grabbed() || !n.visible()) return;
          const a = drift.anchors.get(n.id());
          if (!a) return;
          const p = n.position();
          const v = drift.vel.get(n.id()) || { x: 0, y: 0 };
          // spring back to anchor + tiny random impulse, damped → bounded wander
          v.x = (v.x + (a.x - p.x) * 0.012 + (Math.random() - 0.5) * 0.8) * 0.85;
          v.y = (v.y + (a.y - p.y) * 0.012 + (Math.random() - 0.5) * 0.8) * 0.85;
          n.position({ x: p.x + v.x, y: p.y + v.y });
          drift.vel.set(n.id(), v);
        });
      });
    };
    const startDrift = () => {
      drift.nodes = cy.nodes(":visible");
      drift.anchors = new Map();
      drift.vel = new Map();
      drift.nodes.forEach((n) => {
        const p = n.position();
        drift.anchors.set(n.id(), { x: p.x, y: p.y });
        drift.vel.set(n.id(), { x: 0, y: 0 });
      });
      drift.active = true;
    };

    // explode-from-center + organic settle, then hand off to the drift loop
    const runLayout = (eles: cytoscape.Collection) => {
      drift.active = false;
      eles.nodes().positions(() => ({
        x: (Math.random() - 0.5) * 40,
        y: (Math.random() - 0.5) * 40,
      }));
      const l = eles.layout({
        name: "fcose",
        quality: "default",
        animate: true,
        animationDuration: 1100,
        animationEasing: "ease-out-cubic",
        randomize: false, // start from the central cluster → explode outward
        fit: true,
        padding: 50,
        packComponents: false,
        nodeSeparation: 60,
        idealEdgeLength: 42,
        nodeRepulsion: 7000,
        gravity: 0.4,
        gravityRange: 3,
        numIter: 600,
      } as any);
      l.one("layoutstop", startDrift);
      l.run();
    };
    runLayoutRef.current = runLayout;
    tick(); // the filter effect (runs on mount too) performs the initial layout

    return () => {
      cancelAnimationFrame(drift.raf);
      cy.destroy();
      cyRef.current = null;
      runLayoutRef.current = null;
      tip.remove();
    };
  }, [graph, navigate]);

  // ---- apply filters + (re)run the exploding layout ----
  useEffect(() => {
    const cy = cyRef.current;
    if (!cy) return;
    // lazily materialize Mathlib nodes the first time they're requested
    if (showMathlib && !extAddedRef.current) {
      cy.add(extElsRef.current);
      extAddedRef.current = true;
    }
    cy.batch(() => {
      cy.nodes().forEach((n) => {
        const area = n.data("area") as Area;
        const isExt = area === "external";
        const isDef = n.data("shape") === "round-rectangle";
        const decl: DeclFilter = isDef ? "def" : "thm";
        const visible =
          (isExt ? showMathlib : topics.has(area as CategoryId)) && decls.has(decl);
        n.style("display", visible ? "element" : "none");
      });
    });

    const visible = cy.nodes(":visible");
    if (visible.length === 0) return;
    // defer one frame so the canvas paints before the (blocking) layout runs
    const raf = requestAnimationFrame(() => {
      if (cyRef.current === cy) runLayoutRef.current?.(visible.closedNeighborhood());
    });
    return () => cancelAnimationFrame(raf);
  }, [topics, decls, showMathlib]);

  return (
    <div className="h-[calc(100vh-4rem)] flex flex-col">
      {/* controls */}
      <div className="shrink-0 border-b hairline px-5 sm:px-7 py-3 flex flex-col gap-2">
        <div className="flex items-baseline gap-3 flex-wrap">
          <h1 className="font-display text-xl font-semibold">Dependency graph</h1>
          <span className="font-sans text-xs text-ink-faint">
            Formalized results and their supporting lemmas, definitions &amp;
            Mathlib dependencies · hover a node for its name · click a result to open it
          </span>
        </div>
        <div className="flex flex-wrap items-center gap-x-5 gap-y-2 font-sans text-xs">
          <div className="flex items-center gap-1.5 flex-wrap">
            <span className="text-ink-faint uppercase tracking-widest mr-1">Topic</span>
            {CATEGORIES.map((c) => (
              <Toggle
                key={c.id}
                on={topics.has(c.id)}
                varName={AREA_VAR[c.id]}
                onClick={() => setTopics((s) => toggle(s, c.id))}
              >
                {c.name.replace(" Statistics", "").replace(" Results", "")}
              </Toggle>
            ))}
          </div>
          <div className="flex items-center gap-1.5 flex-wrap">
            <span className="text-ink-faint uppercase tracking-widest mr-1">Kind</span>
            <Toggle on={decls.has("thm")} onClick={() => setDecls((s) => toggle(s, "thm"))}>
              Theorems &amp; lemmas
            </Toggle>
            <Toggle on={decls.has("def")} onClick={() => setDecls((s) => toggle(s, "def"))}>
              Definitions
            </Toggle>
          </div>
          <Toggle
            on={showMathlib}
            varName={AREA_VAR.external}
            onClick={() => setShowMathlib((v) => !v)}
          >
            {AREA_LABEL.external}
          </Toggle>
        </div>
      </div>

      <div ref={elRef} className="relative flex-1 min-h-0 bg-parchment-sunk" />

      {/* legend */}
      <div className="shrink-0 border-t hairline px-5 sm:px-7 py-2.5 flex flex-wrap gap-x-5 gap-y-1.5 text-xs font-sans text-ink-soft">
        <span className="inline-flex items-center gap-1.5">
          <span className="inline-block w-3 h-3 rounded-[2px] border-2 border-ink" />
          User-facing result (larger)
        </span>
        <Key shape="rectangle">Theorem</Key>
        <Key shape="ellipse">Lemma</Key>
        <Key shape="round">Definition</Key>
        <span className="text-ink-faint">·</span>
        {(["parametric", "semiparametric", "empirical", "probability", "external"] as Area[]).map(
          (a) => (
            <span key={a} className="inline-flex items-center gap-1.5">
              <span
                className="inline-block w-3 h-3 rounded-full"
                style={{
                  background: `rgb(var(${AREA_VAR[a]}) / 0.9)`,
                  border: `1.5px solid rgb(var(${AREA_VAR[a]}))`,
                }}
              />
              {AREA_LABEL[a]}
            </span>
          ),
        )}
      </div>
    </div>
  );
}

function toggle<T>(s: Set<T>, v: T): Set<T> {
  const n = new Set(s);
  n.has(v) ? n.delete(v) : n.add(v);
  return n;
}

function Toggle({
  on,
  onClick,
  varName,
  children,
}: {
  on: boolean;
  onClick: () => void;
  varName?: string;
  children: React.ReactNode;
}) {
  return (
    <button
      onClick={onClick}
      className="px-3 py-1.5 rounded-full border transition-colors"
      style={
        on
          ? {
              background: varName ? `rgb(var(${varName}) / 0.16)` : "rgb(var(--ink) / 0.1)",
              borderColor: varName ? `rgb(var(${varName}))` : "rgb(var(--ink) / 0.4)",
              color: varName ? `rgb(var(${varName}))` : "rgb(var(--ink))",
            }
          : {
              background: "transparent",
              borderColor: "rgb(var(--rule))",
              color: "rgb(var(--ink-soft))",
            }
      }
    >
      {children}
    </button>
  );
}

function Key({
  shape,
  children,
}: {
  shape: "rectangle" | "ellipse" | "round";
  children: React.ReactNode;
}) {
  const radius = shape === "ellipse" ? "9999px" : shape === "round" ? "4px" : "0";
  const w = shape === "ellipse" ? "18px" : "13px";
  return (
    <span className="inline-flex items-center gap-1.5">
      <span
        className="inline-block h-3 border-[1.5px] border-ink-soft"
        style={{ width: w, borderRadius: radius }}
      />
      {children}
    </span>
  );
}

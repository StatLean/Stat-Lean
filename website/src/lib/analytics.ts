// Statcounter page-view tracking for this single-page app.
//
// The snippet in index.html loads counter.js once, which records only the
// initial page load. Because the site is a HashRouter SPA, later navigations
// change the URL without a full reload, so Statcounter never sees them. We
// re-run counter.js on every route change; each run reads the current
// `document.URL` (which HashRouter has already updated to the new `#/route`)
// and logs a fresh page view — giving the full per-page click history.
//
// Keep these in sync with the globals in index.html.
const SC_PROJECT = 13294090;
const SC_SECURITY = "99c472be";
const COUNTER_SRC = "https://www.statcounter.com/counter/counter.js";

let previous: HTMLScriptElement | null = null;

/** Record one Statcounter page view for the current URL. Never throws. */
export function recordPageview(): void {
  try {
    const w = window as unknown as Record<string, unknown>;
    w.sc_project = SC_PROJECT;
    w.sc_security = SC_SECURITY;
    w.sc_invisible = 1;
    // Drop the prior re-count node so injected scripts don't accumulate.
    previous?.remove();
    const s = document.createElement("script");
    s.src = COUNTER_SRC;
    s.async = true;
    document.body.appendChild(s);
    previous = s;
  } catch {
    /* analytics must never break navigation */
  }
}

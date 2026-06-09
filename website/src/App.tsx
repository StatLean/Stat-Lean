import { Suspense, lazy, useEffect } from "react";
import { Routes, Route, useLocation } from "react-router-dom";
import { ThemeProvider } from "./lib/theme";
import { SiteHeader } from "./components/SiteHeader";
import { SiteFooter } from "./components/SiteFooter";
import { Home } from "./pages/Home";
import { Category } from "./pages/Category";
import { ResultDetail } from "./pages/ResultDetail";
import { Search } from "./pages/Search";
import { Team } from "./pages/Team";
import { prefetchGraphView, prefetchDependencies, warmGraphChunks } from "./lib/prefetch";

// Graph pages pull in Cytoscape — keep them in their own chunks, but reuse the
// same import promise as the prefetch helpers so a warmed chunk loads instantly.
const GraphView = lazy(() => prefetchGraphView().then((m) => ({ default: m.GraphView })));
const Dependencies = lazy(() =>
  prefetchDependencies().then((m) => ({ default: m.Dependencies })),
);

function ScrollToTop() {
  const { pathname } = useLocation();
  useEffect(() => { window.scrollTo(0, 0); }, [pathname]);
  return null;
}

export default function App() {
  useEffect(warmGraphChunks, []);
  return (
    <ThemeProvider>
      <div className="min-h-screen flex flex-col">
        <ScrollToTop />
        <SiteHeader />
        <main className="flex-1">
          <Routes>
            <Route path="/" element={<Home />} />
            <Route path="/search" element={<Search />} />
            <Route
              path="/dependencies"
              element={
                <Suspense
                  fallback={
                    <div className="h-[70vh] grid place-items-center text-ink-faint font-sans text-sm">
                      Loading dependency graph…
                    </div>
                  }
                >
                  <Dependencies />
                </Suspense>
              }
            />
            <Route path="/team" element={<Team />} />
            <Route path="/category/:catId" element={<Category />} />
            <Route path="/result/:resultId" element={<ResultDetail />} />
            <Route
              path="/result/:resultId/graph"
              element={
                <Suspense
                  fallback={
                    <div className="h-[60vh] grid place-items-center text-ink-faint font-sans text-sm">
                      Loading graph…
                    </div>
                  }
                >
                  <GraphView />
                </Suspense>
              }
            />
            <Route path="*" element={<Home />} />
          </Routes>
        </main>
        <SiteFooter />
      </div>
    </ThemeProvider>
  );
}

import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// Served from a GitHub Pages subpath. Local dev also honors this base, but the
// HashRouter keeps deep links working without an SPA server fallback.
export default defineConfig({
  base: "/Lean-Asymptotic-Statistical-Theory/website/",
  plugins: [react()],
  build: {
    outDir: "dist",
    chunkSizeWarningLimit: 1200,
  },
});

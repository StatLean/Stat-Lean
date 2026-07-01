// Regenerate the README screenshots from a running build of the site.
//
//   npm run build
//   npm run preview            # serves dist at http://localhost:4173/website/
//   npx playwright install chromium   # one-time
//   node shot.mjs              # writes ../assets/screenshot-{home,result,deps}.png
//
// Override the base URL with SHOT_BASE (e.g. the deployed site).
import { chromium } from "playwright";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const __dirname = dirname(fileURLToPath(import.meta.url));
const OUT = resolve(__dirname, "..", "assets");
const BASE = (process.env.SHOT_BASE || "http://localhost:4173/website/").replace(/\/$/, "");
const RESULT_ID = process.env.SHOT_RESULT || "conc-hoeffding";

const browser = await chromium.launch();
const page = await browser.newPage({
  viewport: { width: 1440, height: 900 },
  deviceScaleFactor: 2,
});

// Scroll the whole page in steps so framer-motion `whileInView` sections
// (Topics row 2, Team cards) trigger before a full-page screenshot.
async function scrollThrough() {
  const h = await page.evaluate(() => document.body.scrollHeight);
  for (let y = 0; y <= h; y += 600) {
    await page.evaluate((yy) => window.scrollTo(0, yy), y);
    await page.waitForTimeout(120);
  }
  await page.evaluate(() => window.scrollTo(0, 0));
  await page.waitForTimeout(400);
}

async function shot(hashPath, file, { fullPage = false, settle = 900 } = {}) {
  await page.goto(`${BASE}/#${hashPath}`, { waitUntil: "networkidle" });
  await page.waitForTimeout(settle);
  if (fullPage) await scrollThrough();
  await page.screenshot({ path: resolve(OUT, file), fullPage });
  console.log("wrote", file);
}

// Home: hero + 8 alphabetical topics + Team (full page).
await shot("/", "screenshot-home.png", { fullPage: true });
// Result detail: informal ↔ Lean alignment + REFERENCE block (full page).
await shot(`/result/${RESULT_ID}`, "screenshot-result.png", { fullPage: true });
// Global dependency graph (viewport; give Cytoscape time to lay out).
await shot("/dependencies", "screenshot-deps.png", { settle: 4000 });

await browser.close();

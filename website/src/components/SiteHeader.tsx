import { Link, NavLink } from "react-router-dom";
import { useTheme } from "../lib/theme";
import { REPO_URL, DOCS_BASE } from "../lib/site";
import { prefetchDependencies } from "../lib/prefetch";
import { Logo } from "./Logo";

const NAV = [
  { to: "/search", label: "Search" },
  { to: "/dependencies", label: "Dependencies", prefetch: prefetchDependencies },
  { to: "/team", label: "Team" },
];

export function SiteHeader() {
  const { theme, toggle } = useTheme();
  return (
    <header className="sticky top-0 z-40 backdrop-blur-md bg-parchment/80 border-b hairline">
      <div className="max-w-page mx-auto px-5 sm:px-8 h-16 flex items-center gap-6">
        <Link to="/" className="flex items-center gap-3 group shrink-0">
          <Logo className="w-8 h-8 text-ink group-hover:text-param transition-colors" />
          <span className="font-display text-xl font-semibold tracking-tight">
            Stat-Lean
          </span>
        </Link>

        <nav className="hidden sm:flex items-center gap-1 ml-2 text-sm">
          {NAV.map((n) => (
            <NavLink
              key={n.to}
              to={n.to}
              onMouseEnter={n.prefetch}
              onFocus={n.prefetch}
              className={({ isActive }) =>
                `px-3 py-1.5 rounded-full font-sans transition-colors ${
                  isActive ? "bg-ink/10 text-ink" : "text-ink-soft hover:text-ink"
                }`
              }
            >
              {n.label}
            </NavLink>
          ))}
        </nav>

        <div className="ml-auto flex items-center gap-1.5 text-sm">
          <a
            href={DOCS_BASE}
            className="hidden sm:inline-block px-3 py-1.5 rounded-full text-ink-soft hover:text-ink font-sans"
          >
            API docs
          </a>
          <a
            href={REPO_URL}
            className="hidden sm:inline-block px-3 py-1.5 rounded-full text-ink-soft hover:text-ink font-sans"
          >
            GitHub
          </a>
          <button
            onClick={toggle}
            aria-label="Toggle theme"
            className="w-9 h-9 grid place-items-center rounded-full border hairline text-ink-soft hover:text-ink hover:border-ink/40 transition-colors"
          >
            {theme === "light" ? "☾" : "☀"}
          </button>
        </div>
      </div>
    </header>
  );
}

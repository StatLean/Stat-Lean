import { Link } from "react-router-dom";
import { motion } from "framer-motion";
import { CATEGORIES } from "../lib/categories";
import { RESULTS } from "../lib/data";
import { ConvergenceMark } from "../components/ConvergenceMark";
import { Logo } from "../components/Logo";
import { TheoremCard } from "../components/TheoremCard";
import { TopicIcon } from "../components/TopicIcon";

const FEATURED = [
  "hajek_le_cam_convolution_theorem",
  "TangentSpec",
  "oneStep_semiparametricallyEfficient",
  "weak_limit_under_Q_of_lecam_third",
];

export function Home() {
  const featured = FEATURED.map((id) => RESULTS.find((r) => r.id === id)).filter(
    Boolean,
  ) as typeof RESULTS;

  return (
    <div>
      {/* ---------- Hero ---------- */}
      <section className="relative overflow-hidden border-b hairline">
        <ConvergenceMark
          rings={9}
          className="pointer-events-none absolute -right-24 -top-24 w-[34rem] h-[34rem] text-ink opacity-[0.04]"
        />
        <div className="max-w-page mx-auto px-5 sm:px-8 pt-20 pb-20 relative flex items-center gap-16">
          {/* Text */}
          <div className="flex-1 min-w-0">
            <motion.p
              initial={{ opacity: 0, y: 10 }}
              animate={{ opacity: 1, y: 0 }}
              transition={{ duration: 0.6 }}
              className="font-sans text-xs uppercase tracking-[0.3em] text-ink-faint mb-6"
            >
              Formalization proofs meet with informal statements
            </motion.p>

            <motion.h1
              initial={{ opacity: 0, y: 16 }}
              animate={{ opacity: 1, y: 0 }}
              transition={{ duration: 0.7, delay: 0.05 }}
              className="font-display font-semibold tracking-tight leading-[0.98] text-5xl sm:text-6xl md:text-7xl max-w-4xl"
            >
              Lean&nbsp;4 Formalization of{" "}
              <span className="italic text-param">Asymptotic Statistical Theory</span>
            </motion.h1>

            <motion.div
              initial={{ opacity: 0, y: 16 }}
              animate={{ opacity: 1, y: 0 }}
              transition={{ duration: 0.7, delay: 0.18 }}
              className="mt-10 flex flex-wrap gap-3"
            >
              <Link
                to="/search"
                className="px-5 py-2.5 rounded-full bg-ink text-parchment font-sans text-sm font-medium hover:opacity-90 transition-opacity"
              >
                Browse the results →
              </Link>
              <Link
                to="/dependencies"
                className="px-5 py-2.5 rounded-full border hairline font-sans text-sm text-ink-soft hover:text-ink hover:border-ink/40 transition-colors"
              >
                Dependency graph
              </Link>
            </motion.div>
          </div>

          {/* Logo — visible on large screens only */}
          <motion.div
            initial={{ opacity: 0, scale: 0.92 }}
            animate={{ opacity: 1, scale: 1 }}
            transition={{ duration: 0.8, delay: 0.1 }}
            className="hidden lg:flex shrink-0 items-center justify-center"
          >
            <Logo className="w-56 h-56 text-ink opacity-90" />
          </motion.div>
        </div>
      </section>

      {/* ---------- Topics ---------- */}
      <section id="topics" className="max-w-page mx-auto px-5 sm:px-8 py-20">
        <h2 className="font-display text-3xl font-semibold mb-1">Topics in Statistics</h2>
        <p className="text-ink-soft font-serif mb-10">
          Browse the library by area; each opens a gallery of aligned results.
        </p>

        <div className="grid gap-5 md:grid-cols-2">
          {CATEGORIES.map((c, i) => (
            <motion.div
              key={c.id}
              initial={{ opacity: 0, y: 18 }}
              whileInView={{ opacity: 1, y: 0 }}
              viewport={{ once: true, margin: "-60px" }}
              transition={{ duration: 0.5, delay: i * 0.06 }}
            >
              <Link
                to={`/category/${c.id}`}
                data-cat={c.id}
                className="group relative block overflow-hidden rounded-2xl border hairline bg-parchment-panel p-7 min-h-[14rem] transition-all duration-300 hover:border-accent/60 hover:shadow-[0_20px_50px_-24px_rgb(var(--accent)/0.5)]"
              >
                <ConvergenceMark
                  rings={6}
                  className="absolute -right-10 -bottom-10 w-44 h-44 accent opacity-10 group-hover:opacity-20 group-hover:scale-110 transition-all duration-500"
                />
                <TopicIcon
                  id={c.id}
                  className="w-11 h-11 accent opacity-80 group-hover:opacity-100 transition-opacity"
                />
                <h3 className="mt-6 font-display text-2xl font-semibold group-hover:accent transition-colors">
                  {c.name}
                </h3>
                <p className="mt-1 font-sans text-sm accent">{c.tagline}</p>
                <p className="mt-3 font-serif text-[0.95rem] text-ink-soft leading-relaxed max-w-xl">
                  {c.blurb}
                </p>
              </Link>
            </motion.div>
          ))}
        </div>
      </section>

      {/* ---------- Gallery ---------- */}
      {featured.length > 0 && (
        <section className="max-w-page mx-auto px-5 sm:px-8 pb-8">
          <h2 className="font-display text-3xl font-semibold mb-1">Gallery</h2>
          <p className="text-ink-soft font-serif mb-8">
            A selection of results across the topics.
          </p>
          <div className="grid gap-4 sm:grid-cols-2 lg:grid-cols-4">
            {featured.map((r, i) => (
              <TheoremCard key={r.id} r={r} index={i} />
            ))}
          </div>
        </section>
      )}
    </div>
  );
}

import { motion } from "framer-motion";
import { ConvergenceMark } from "../components/ConvergenceMark";

const BASE = import.meta.env.BASE_URL;

interface Member {
  name: string;
  role: string;
  department: string;
  university: string;
  homepage?: string;
  photo: string;
}

const MEMBERS: Member[] = [
  {
    name: "Junwei Lu",
    role: "Associate Professor",
    department: "Department of Biostatistics",
    university: "Harvard T.H. Chan School of Public Health",
    homepage: "https://junwei-lu.github.io/",
    photo: "Junwei_Lu.jpeg",
  },
  {
    name: "Ethan X. Fang",
    role: "Associate Professor",
    department: "Department of Biostatistics & Bioinformatics",
    university: "Duke University",
    homepage: "https://ethanfangduke.github.io/",
    photo: "Ethan_Fang.jpg",
  },
  {
    name: "Tingzhou Wei",
    role: "Graduate Student",
    department: "Department of Biostatistics & Bioinformatics",
    university: "Duke University",
    photo: "Tingzhou_Wei.jpg",
  },
  {
    name: "Zeyu Zheng",
    role: "Graduate Student",
    department: "Department of Mathematical Sciences",
    university: "Carnegie Mellon University",
    homepage: "https://zeyu-zheng.github.io/",
    photo: "Zeyu_Zheng.jpg",
  },
];

export function Team() {
  return (
    <div>
      {/* Hero */}
      <section className="relative overflow-hidden border-b hairline">
        <ConvergenceMark
          rings={9}
          className="pointer-events-none absolute -right-24 -top-24 w-[34rem] h-[34rem] text-ink opacity-[0.06]"
        />
        <div className="max-w-page mx-auto px-5 sm:px-8 pt-20 pb-16 relative">
          <motion.h1
            initial={{ opacity: 0, y: 16 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ duration: 0.7 }}
            className="font-display font-semibold tracking-tight leading-[0.98] text-5xl sm:text-6xl md:text-7xl max-w-xl"
          >
            Our <span className="italic text-param">Team</span>
          </motion.h1>
        </div>
      </section>

      {/* Grid */}
      <section className="max-w-page mx-auto px-5 sm:px-8 py-20">
        <div className="grid sm:grid-cols-2 gap-8 max-w-3xl mx-auto">
          {MEMBERS.map((m, i) => (
            <motion.div
              key={m.name}
              initial={{ opacity: 0, y: 20 }}
              animate={{ opacity: 1, y: 0 }}
              transition={{ duration: 0.5, delay: i * 0.08 }}
              className="rounded-2xl border hairline bg-parchment-panel p-8 flex flex-col items-center text-center gap-4"
            >
              <img
                src={`${BASE}team/${m.photo}`}
                alt={m.name}
                className="w-32 h-32 rounded-full object-cover border hairline shadow-sm"
              />
              <div className="flex flex-col gap-1">
                {m.homepage ? (
                  <a
                    href={m.homepage}
                    target="_blank"
                    rel="noreferrer"
                    className="font-display text-xl font-semibold tracking-tight ulink"
                  >
                    {m.name}
                  </a>
                ) : (
                  <span className="font-display text-xl font-semibold tracking-tight">
                    {m.name}
                  </span>
                )}
                <p className="font-sans text-sm text-ink-soft">{m.role}</p>
                <p className="font-serif text-sm text-ink-faint leading-snug">{m.department}</p>
                <p className="font-serif text-sm text-ink-faint leading-snug">{m.university}</p>
              </div>
            </motion.div>
          ))}
        </div>
      </section>
    </div>
  );
}

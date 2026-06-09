/** @type {import('tailwindcss').Config} */
export default {
  content: ["./index.html", "./src/**/*.{ts,tsx}"],
  darkMode: ["class", '[data-theme="dark"]'],
  theme: {
    extend: {
      fontFamily: {
        display: ['Fraunces', 'Georgia', 'serif'],
        serif: ['Newsreader', 'Georgia', 'serif'],
        sans: ['"Hanken Grotesk"', 'system-ui', 'sans-serif'],
        mono: ['"JetBrains Mono"', 'ui-monospace', 'monospace'],
      },
      colors: {
        ink: {
          DEFAULT: 'rgb(var(--ink) / <alpha-value>)',
          soft: 'rgb(var(--ink-soft) / <alpha-value>)',
          faint: 'rgb(var(--ink-faint) / <alpha-value>)',
        },
        parchment: {
          DEFAULT: 'rgb(var(--bg) / <alpha-value>)',
          panel: 'rgb(var(--panel) / <alpha-value>)',
          sunk: 'rgb(var(--sunk) / <alpha-value>)',
        },
        rule: 'rgb(var(--rule) / <alpha-value>)',
        // resolves to the active category accent (see --accent in index.css)
        accent: 'rgb(var(--accent) / <alpha-value>)',
        // category accents
        param: 'rgb(var(--c-param) / <alpha-value>)',
        semi: 'rgb(var(--c-semi) / <alpha-value>)',
        empirical: 'rgb(var(--c-emp) / <alpha-value>)',
        probability: 'rgb(var(--c-prob) / <alpha-value>)',
      },
      maxWidth: {
        page: '78rem',
      },
      keyframes: {
        'rise': {
          '0%': { opacity: '0', transform: 'translateY(12px)' },
          '100%': { opacity: '1', transform: 'translateY(0)' },
        },
      },
      animation: {
        rise: 'rise 0.7s cubic-bezier(0.16,1,0.3,1) both',
      },
    },
  },
  plugins: [],
};

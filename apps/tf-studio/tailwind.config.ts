import type { Config } from "tailwindcss";

const config: Config = {
  darkMode: ["class"],
  content: [
    "./app/**/*.{ts,tsx,js,jsx,mdx}",
    "./components/**/*.{ts,tsx,js,jsx}",
    "./styles/**/*.{css}",
  ],
  theme: {
    extend: {
      colors: {
        bg: "rgb(var(--bg) / <alpha-value>)",
        surface: "rgb(var(--surface) / <alpha-value>)",
        overlay: "rgb(var(--overlay) / <alpha-value>)",
        text: "rgb(var(--text) / <alpha-value>)",
        muted: "rgb(var(--muted) / <alpha-value>)",
        "tf-publish":   "rgb(var(--tf-publish) / <alpha-value>)",
        "tf-subscribe": "rgb(var(--tf-subscribe) / <alpha-value>)",
        "tf-transform": "rgb(var(--tf-transform) / <alpha-value>)",
        "tf-keypair":   "rgb(var(--tf-keypair) / <alpha-value>)",
        pass:  "#22c55e",
        warn:  "#f59e0b",
        fail:  "#ef4444",
      },
      borderRadius: { xl2: "1.25rem" },
      boxShadow: { soft: "0 10px 30px rgba(0,0,0,0.25)" },
    },
  },
  plugins: [],
};

export default config;

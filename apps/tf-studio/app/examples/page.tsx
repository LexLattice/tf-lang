import Link from "next/link";
import BrandMark from "../../components/BrandMark";
import ExampleCard from "../../components/ExampleCard";

export const metadata = {
  title: "Examples · TF-Studio",
};

const EXAMPLES = [
  {
    title: "Auto FNOL Fast Track",
    description:
      "Canonical v0.6 build trace. Render the DOT graph or check the branch exclusivity law harness.",
    filePath: "examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json",
    lawGoal: "branch-exclusive" as const,
  },
  {
    title: "Auto Quote Bind Issue",
    description:
      "A larger pipeline with multiple capability checks. Useful for seeing dense graphs.",
    filePath: "examples/v0.6/build/auto.quote.bind.issue.v2.l0.json",
    lawGoal: "branch-exclusive" as const,
  },
];

export default function ExamplesPage() {
  return (
    <main className="px-6 md:px-10 py-10 space-y-10">
      <header className="flex items-center justify-between">
        <BrandMark />
        <Link href="/" className="badge border-white/10 chip-transform">Back to home</Link>
      </header>

      <section className="space-y-3">
        <h1 className="text-2xl font-semibold tracking-tight">Explore Pipeline Samples</h1>
        <p className="text-sm text-zinc-300 max-w-2xl leading-relaxed">
          Select an example to build its graph or run law checks. Everything happens in-process via
          the Studio API, so you can peek at real artifacts without leaving the browser.
        </p>
      </section>

      <section className="grid gap-4 md:grid-cols-2">
        {EXAMPLES.map((example) => (
          <ExampleCard key={example.filePath} {...example} />
        ))}
      </section>
    </main>
  );
}

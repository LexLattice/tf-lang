import Link from "next/link";
import BrandMark from "../../components/BrandMark";
import ExpandPanel from "../../components/ExpandPanel";
import PlaygroundBridge from "./bridge";
import PlaygroundPanel from "./panel";

export const metadata = {
  title: "Playground · TF-Studio",
};

export default function PlaygroundPage() {
  return (
    <main className="px-6 md:px-10 py-10 space-y-10">
      <PlaygroundBridge />

      <header className="flex items-center justify-between">
        <BrandMark />
        <Link href="/" className="badge border-white/10 chip-publish">Back to home</Link>
      </header>

      <section className="space-y-4">
        <h1 className="text-2xl font-semibold tracking-tight">Interactive Playground</h1>
        <p className="text-sm text-zinc-300 max-w-2xl leading-relaxed">
          Experiment with L2 input expansion and call the in-process CLI endpoints directly from
          your browser. Everything runs against the checked-in repo modules—no shell commands.
        </p>
      </section>

      <ExpandPanel />

      <section className="space-y-4">
        <h2 className="text-xl font-semibold">Quick API helpers</h2>
        <p className="text-sm text-zinc-300 max-w-2xl leading-relaxed">
          Use the console-style helpers below (and the <code>window.tf</code> bindings) to run graph
          renders or law checks without switching tabs.
        </p>
        <PlaygroundPanel />
      </section>
    </main>
  );
}

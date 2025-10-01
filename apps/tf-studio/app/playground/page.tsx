import Link from "next/link";
import BrandMark from "../../components/BrandMark";
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
          Play with live TF-Lang artifacts straight from the repo. All requests go through the
          in-process CLI adapters, so you can inspect real effects without any mock services.
        </p>
      </section>

      <PlaygroundPanel />
    </main>
  );
}

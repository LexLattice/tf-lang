import KernelHero from "../components/KernelHero";
import BrandMark from "../components/BrandMark";
import Link from "next/link";

export default function Home() {
  return (
    <main className="px-6 md:px-10 py-10 space-y-8">
      <div className="flex items-center justify-between">
        <BrandMark />
        <div className="flex gap-3">
          <Link href="/examples" className="badge chip-transform border-white/10">Examples</Link>
          <Link href="/playground" className="badge chip-publish border-white/10">Playground</Link>
          <Link href="/chat" className="badge chip-keypair border-white/10">Game Master</Link>
        </div>
      </div>
      <KernelHero />
    </main>
  );
}

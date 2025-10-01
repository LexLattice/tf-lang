import Image from "next/image";

export default function BrandMark({ size = 56 }: { size?: number }) {
  return (
    <div className="inline-flex items-center gap-3">
      <Image
        src="/brand/brand-splash.svg"
        alt="TF-Lang brand"
        width={size * 2.2}
        height={size * 1.1}
        className="rounded-lg border border-white/10 shadow-soft"
      />
      <div>
        <div className="text-lg font-semibold tracking-tight">TF-Studio</div>
        <div className="text-xs text-muted">Playground & gallery for TF-Lang</div>
      </div>
    </div>
  );
}

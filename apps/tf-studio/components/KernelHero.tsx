import React from "react";

const N = [
  { k: 'Publish',   color: 'var(--tf-publish)',   x: 20,  y: 40, r: 10 },
  { k: 'Subscribe', color: 'var(--tf-subscribe)', x: 80,  y: 40, r: 10 },
  { k: 'Transform', color: 'var(--tf-transform)', x: 50,  y: 20, r: 10 },
  { k: 'Keypair',   color: 'var(--tf-keypair)',   x: 50,  y: 74, r: 10 },
];

export default function KernelHero() {
  return (
    <div className="relative mx-auto max-w-4xl rounded-2xl p-6 bg-gradient-to-b from-zinc-900/60 to-zinc-900/20 border border-white/10 shadow-2xl">
      <div className="flex items-center justify-between mb-4">
        <h1 className="text-2xl md:text-3xl font-semibold tracking-tight">TF‑Lang Kernel</h1>
        <div className="text-sm text-zinc-400">Publish · Subscribe · Transform · Keypair</div>
      </div>
      <svg viewBox="0 0 100 100" className="w-full h-64" aria-hidden>
        <defs>
          <filter id="g" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="0.6" />
          </filter>
        </defs>
        <g stroke="white" strokeOpacity="0.25">
          <AnimatedEdge a={{x:20,y:40}} b={{x:50,y:20}} delay={0} />
          <AnimatedEdge a={{x:50,y:20}} b={{x:80,y:40}} delay={0.2} />
          <AnimatedEdge a={{x:20,y:40}} b={{x:50,y:74}} delay={0.4} />
          <AnimatedEdge a={{x:50,y:74}} b={{x:80,y:40}} delay={0.6} />
        </g>
        {N.map((n, i) => (
          <g key={n.k} filter="url(#g)">
            <circle cx={n.x} cy={n.y} r={n.r} fill={n.color}>
              <animate attributeName="r" values="9;10.5;9" dur="3s" begin={`${i*0.2}s`} repeatCount="indefinite"/>
            </circle>
            <text x={n.x} y={n.y + 18} textAnchor="middle" fontSize="4" fill="rgba(255,255,255,0.9)">{n.k}</text>
          </g>
        ))}
        <text x="50" y="50" textAnchor="middle" fontSize="4.5" fill="rgba(255,255,255,0.6)">Compose anything</text>
      </svg>
      <p className="text-zinc-300 text-sm leading-relaxed">
        A minimal kernel of four true functions. Build pipelines from L2 intents, expand to L0,
        and verify with effects, capabilities, and laws—live in your browser.
      </p>
    </div>
  );
}

function AnimatedEdge({a,b,delay}:{a:{x:number,y:number},b:{x:number,y:number},delay:number}) {
  const id = Math.random().toString(36).slice(2);
  return (
    <g>
      <line x1={a.x} y1={a.y} x2={b.x} y2={b.y} strokeWidth="0.6" />
      <circle r="1.2" fill="white">
        <animateMotion dur="3s" begin={`${delay}s`} repeatCount="indefinite">
          <mpath xlinkHref={`#${id}`} />
        </animateMotion>
      </circle>
      <path id={id} d={`M ${a.x} ${a.y} L ${b.x} ${b.y}`} fill="none" stroke="transparent"/>
    </g>
  );
}

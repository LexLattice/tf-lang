"use client";

import { useState } from "react";

type CodeEditorProps = {
  initial?: string;
  onChange: (value: string) => void;
};

export default function CodeEditor({ initial = "", onChange }: CodeEditorProps) {
  const [value, setValue] = useState(initial);

  return (
    <textarea
      className="w-full h-[360px] card p-3 font-mono text-sm"
      value={value}
      onChange={(event) => {
        const next = event.target.value;
        setValue(next);
        onChange(next);
      }}
      spellCheck={false}
      placeholder="Paste L2 YAML here..."
    />
  );
}

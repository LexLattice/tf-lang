"use client";

import { useEffect } from "react";
import { apiGraph, apiLaws } from "../../lib/tools";

type PlaygroundHelpers = {
  apiGraph: typeof apiGraph;
  apiLaws: typeof apiLaws;
};

export default function PlaygroundBridge() {
  useEffect(() => {
    const helpers: PlaygroundHelpers = {
      apiGraph,
      apiLaws,
    };

    const win = window as typeof window & { tf?: PlaygroundHelpers };
    win.tf = helpers;

    return () => {
      if (win.tf === helpers) {
        delete win.tf;
      }
    };
  }, []);

  return null;
}

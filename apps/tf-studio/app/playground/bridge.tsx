"use client";

import { useEffect } from "react";
import { apiEffects, apiExpand, apiGraph, apiLaws, apiPlanInstances, apiTypecheck } from "../../lib/tools";

type PlaygroundHelpers = {
  apiGraph: typeof apiGraph;
  apiLaws: typeof apiLaws;
  apiEffects: typeof apiEffects;
  apiTypecheck: typeof apiTypecheck;
  apiPlanInstances: typeof apiPlanInstances;
  apiExpand: typeof apiExpand;
};

export default function PlaygroundBridge() {
  useEffect(() => {
    const helpers: PlaygroundHelpers = {
      apiGraph,
      apiLaws,
      apiEffects,
      apiTypecheck,
      apiPlanInstances,
      apiExpand,
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

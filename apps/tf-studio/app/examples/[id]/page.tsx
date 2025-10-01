import ChatDock from "../../../components/ChatDock";
import EffectsPanel from "../../../components/EffectsPanel";
import GraphPanel from "../../../components/GraphPanel";
import InstancePlanPanel from "../../../components/InstancePlanPanel";
import LawPanel from "../../../components/LawPanel";
import TypecheckPanel from "../../../components/TypecheckPanel";

export const metadata = {
  title: "Example Detail · TF-Studio",
};

type ExampleDetailProps = {
  searchParams: { l0?: string };
};

export default function ExampleDetail({ searchParams }: ExampleDetailProps) {
  const filePath = searchParams?.l0 ?? "";

  return (
    <main className="px-6 md:px-10 py-10 space-y-6">
      <h1 className="text-2xl font-semibold">Example detail</h1>
      <div className="text-sm text-muted">File</div>
      <div className="card p-3 font-mono text-xs">
        {filePath || "(missing file param)"}
      </div>

      {filePath && (
        <div className="grid lg:grid-cols-2 gap-4">
          <GraphPanel filePath={filePath} />
          <EffectsPanel filePath={filePath} />
          <TypecheckPanel filePath={filePath} />
          <InstancePlanPanel filePath={filePath} />
          <LawPanel filePath={filePath} />
          <ChatDock filePath={filePath} />
        </div>
      )}
    </main>
  );
}

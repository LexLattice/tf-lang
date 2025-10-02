import ChatDock from "../../components/ChatDock";

export const metadata = {
  title: "Game Master · TF-Studio",
};

export default function ChatPage() {
  const defaultL0 = "examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json";

  return (
    <main className="px-6 md:px-10 py-10 space-y-6">
      <h1 className="text-2xl font-semibold">Game Master</h1>
      <p className="text-sm text-zinc-300 max-w-2xl leading-relaxed">
        Launch quick probes against a known pipeline without leaving the browser. The actions below
        call the same in-repo APIs used elsewhere in the Studio.
      </p>
      <ChatDock filePath={defaultL0} />
    </main>
  );
}

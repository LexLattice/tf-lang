import "../styles/globals.css";
import type { Metadata } from "next";

export const metadata: Metadata = {
  title: "TF-Studio — TF-Lang Playground",
  description: "Compose anything from four primitives. Visualize, verify, and learn.",
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" className="dark">
      <body className="min-h-screen">{children}</body>
    </html>
  );
}

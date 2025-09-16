# Region Visualizer (Static)

A single-page HTML/SVG that loads `regions.json` and `violations.json` to highlight out-of-bounds reads/writes.
- Input: emit from tests into `out/t1/regions.json` and `out/t1/violations.json`.
- Output: `visualizer/index.html` uses local JS (no external CDN).
- CI artifact: `out/t1/region-visualizer.zip`.

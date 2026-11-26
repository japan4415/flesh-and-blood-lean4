import { readFile } from "node:fs/promises";
import { createServer } from "node:http";
import { draftSignal } from "./draft-signaling.mjs";

const root = new URL("../", import.meta.url);
const paths = new Map([
  ["/", ["web/index.html", "text/html; charset=utf-8"]],
  ["/app.js", ["web/app.js", "text/javascript; charset=utf-8"]],
  ["/wasm.js", ["web/wasm.js", "text/javascript; charset=utf-8"]],
  ["/cards.js", ["web/cards.js", "text/javascript; charset=utf-8"]],
  ["/styles.css", ["web/styles.css", "text/css; charset=utf-8"]],
  ["/draft", ["web/draft.html", "text/html; charset=utf-8"]],
  ["/draft.js", ["web/draft.js", "text/javascript; charset=utf-8"]],
  ["/draft-play.js", ["web/draft-play.js", "text/javascript; charset=utf-8"]],
  ["/draft.css", ["web/draft.css", "text/css; charset=utf-8"]],
  ["/wasm/fab.js", [".lake/wasm/output/fab.js", "text/javascript; charset=utf-8"]],
  ["/wasm/fab.wasm", [".lake/wasm/output/fab.wasm", "application/wasm"]],
]);

const [source, images] = await Promise.all(
  ["data/normalized/wtr_cards.json", "web/card-images.json"].map(async (path) =>
    JSON.parse(await readFile(new URL(path, root), "utf8"))),
);
const cards = JSON.stringify(Object.fromEntries(source.cards.map((card) => [
  card.card_id,
  { name: card.name, number: card.primary_print_id, image: images[card.primary_print_id] },
])));

const port = Number(process.env.PORT ?? 4173);
const host = process.env.FAB_HOST ?? "127.0.0.1";
const server = createServer(async (request, response) => {
  response.setHeader("Cross-Origin-Opener-Policy", "same-origin");
  response.setHeader("Cross-Origin-Embedder-Policy", "credentialless");
  response.setHeader("Cache-Control", "no-store");
  const path = request.url.split("?")[0];
  if (path === "/draft/signal") {
    await draftSignal(request, response);
    return;
  }
  if (request.method !== "GET" && request.method !== "HEAD") {
    response.writeHead(405, { Allow: "GET, HEAD" }).end();
    return;
  }
  if (path === "/cards.json") {
    response.writeHead(200, { "Content-Type": "application/json" }).end(cards);
    return;
  }
  const asset = paths.get(path);
  if (!asset) {
    response.writeHead(404).end();
    return;
  }
  const [file, contentType] = asset;
  try {
    const contents = await readFile(new URL(file, root));
    response.writeHead(200, { "Content-Type": contentType }).end(contents);
  } catch (error) {
    if (error.code === "ENOENT") response.writeHead(404).end();
    else response.writeHead(500).end();
  }
});

server.listen(port, host, () => {
  console.log(`WTR booster simulator http://${host}:${server.address().port}/`);
});

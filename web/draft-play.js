import { cardMedia, loadCards } from "./cards.js";
import { loadWasm, sampleIndex } from "./wasm.js";

function decodeView(encoded) {
  if (typeof encoded !== "string") return null;
  const parts = encoded.split("\n");
  if (parts.length !== 4) return null;
  const [phase, round, pack, picks] = parts;
  const booster = Number(round);
  if (!["picking", "review", "complete"].includes(phase) || ![0, 1, 2, 3].includes(booster)) return null;
  const cards = (value) => value === "-" ? null : value ? value.split(" ") : [];
  return { phase, booster, pack: cards(pack), picks: cards(picks) };
}

function makeEngine(wasm) {
  const call = (method, result, types, args) => wasm.ccall(`fab_web_draft_${method}`, result, types, args);
  return {
    start() {
      const bounds = wasm.ccall("fab_web_bounds", "string").split(" ").map(Number);
      if (bounds.length !== 16 || bounds.some((n) => !Number.isSafeInteger(n) || n < 1)) return false;
      const packs = Array.from({ length: 24 }, () => bounds.map(sampleIndex).join(" ")).join("\n");
      return call("start", "number", ["string"], [packs]) === 1;
    },
    view: (seat) => call("view", "string", ["number"], [seat - 1]),
    pick: (seat, card) => call("pick", "number", ["number", "string"], [seat - 1, card]) === 1,
    next: () => call("next", "number") === 1,
    reset: () => call("reset", null),
  };
}

export function createDraftPlay({ session, connected, lock, send }) {
  const start = document.querySelector("#draft-start");
  const next = document.querySelector("#draft-next");
  const pick = document.querySelector("#draft-pick");
  const phase = document.querySelector("#draft-phase");
  const feedback = document.querySelector("#draft-feedback");
  const grid = document.querySelector("#draft-cards");
  let catalog = {};
  let pod;
  let view;
  let selected;
  let starting = false;
  let pending = false;
  let aborted = false;

  function renderCards() {
    const ids = view?.pack ?? view?.picks ?? [];
    grid.replaceChildren(...ids.map((id, index) => {
      const card = Object.hasOwn(catalog, id) ? catalog[id] : { name: id, number: id };
      const item = document.createElement("li");
      item.className = "card";
      const label = document.createElement("span");
      label.className = "draft-card-label";
      label.textContent = card.name;
      const media = cardMedia(card, true);
      if (view.pack) {
        const choice = document.createElement("button");
        choice.type = "button";
        choice.className = "draft-choice";
        choice.setAttribute("aria-label", `${card.name} ${card.number}`);
        choice.setAttribute("aria-pressed", String(selected === index));
        choice.addEventListener("click", () => {
          if (pending) return;
          grid.querySelector('[aria-pressed="true"]')?.setAttribute("aria-pressed", "false");
          selected = index;
          choice.setAttribute("aria-pressed", "true");
          refresh();
        });
        choice.append(media, label);
        item.append(choice);
      } else {
        item.append(media, label);
      }
      return item;
    }));
  }

  function abort() {
    if (pod) {
      for (const peer of pod.peers) send(peer, { kind: "draft-abort" });
      pod.engine.reset();
      pod = undefined;
    }
    aborted = true;
    view = undefined;
    renderCards();
  }

  function refresh() {
    const room = session();
    const peers = connected();
    const host = room?.seat === 1;
    if (pod && view?.phase !== "complete" && pod.peers.some((peer) => !peers.includes(peer))) abort();
    if (room && !host && view && view.phase !== "complete" && peers.length === 0) abort();
    start.hidden = !host || Boolean(view) || aborted;
    start.disabled = peers.length !== 7 || starting;
    next.hidden = !host || view?.phase !== "review";
    pick.hidden = !view?.pack;
    pick.disabled = selected === undefined || pending;
    let summary = room && !host ? "ホストの開始を待っています。" : "8席がそろうと開始できます。";
    if (aborted) summary = "接続が切れたためドラフトを終了しました。";
    else if (starting) summary = "Leanを起動し、24パックを用意しています…";
    else if (view?.phase === "complete") summary = `ドラフト完了 · 自分の取得カード ${view.picks.length}枚`;
    else if (view?.phase === "review") summary = `${view.booster - 1}パック目のレビュー · 自分の取得カード ${view.picks.length}枚`;
    else if (view?.phase === "picking") {
      summary = view.pack
        ? `${view.booster}パック目 · 残り ${view.pack.length}枚`
        : `${view.booster}パック目 · ピック済み。ほかの席を待っています。`;
    }
    if (summary !== phase.textContent) phase.textContent = summary;
  }

  function show(projection) {
    const focused = document.activeElement;
    const moveFocus = projection && (grid.contains(focused) || [start, next, pick].includes(focused));
    view = projection;
    selected = undefined;
    pending = false;
    feedback.textContent = "";
    renderCards();
    refresh();
    if (moveFocus) phase.focus({ preventScroll: true });
  }

  function publishViews() {
    const current = pod;
    for (const peer of [null, ...current.peers]) {
      if (pod !== current) return;
      const seat = peer?.seat ?? 1;
      const encoded = current.engine.view(seat);
      if (current.sent.get(seat) === encoded) continue;
      current.sent.set(seat, encoded);
      if (peer) send(peer, { kind: "draft-view", view: encoded });
      else show(decodeView(encoded));
    }
  }

  function acceptPick(seat, message) {
    const current = decodeView(pod.engine.view(seat));
    if (!current?.pack || current.booster !== message.booster || current.pack.length !== message.size ||
        typeof message.card !== "string" || !current.pack.includes(message.card)) return false;
    if (!pod.engine.pick(seat, message.card)) return false;
    publishViews();
    return true;
  }

  start.addEventListener("click", async () => {
    const room = session();
    const peers = connected();
    if (room?.seat !== 1 || peers.length !== 7 || starting || pod || aborted) return;
    starting = true;
    feedback.textContent = "";
    refresh();
    let engine;
    try {
      engine = makeEngine(await loadWasm());
      if (room !== session()) return;
      if (!engine.start()) throw new Error("Leanでドラフトを開始できませんでした。");
      await lock(room, peers);
      if (room !== session()) return;
      pod = { engine, peers, sent: new Map() };
      refresh();
      if (pod) publishViews();
    } catch (error) {
      if (room === session()) feedback.textContent = error.message;
    } finally {
      if (engine && !pod) engine.reset();
      starting = false;
      refresh();
    }
  });

  next.addEventListener("click", () => {
    if (pod?.engine.next()) publishViews();
  });

  pick.addEventListener("click", () => {
    if (!view?.pack || selected === undefined || pending) return;
    const message = { kind: "draft-pick", booster: view.booster, size: view.pack.length, card: view.pack[selected] };
    if (pod) {
      if (!acceptPick(1, message)) feedback.textContent = "ピックを受け付けられませんでした。";
    } else {
      pending = send(connected()[0], message);
      if (!pending) feedback.textContent = "ホストとの接続を確認してください。";
      refresh();
    }
  });

  void loadCards().then((data) => {
    catalog = data;
    if (view) renderCards();
  }).catch(() => {});

  return {
    refresh,
    reset() {
      pod?.engine.reset();
      pod = undefined;
      aborted = false;
      show(undefined);
    },
    receive(peer, message) {
      if (message.kind === "draft-pick") {
        if (!pod?.peers.includes(peer)) return;
        if (!acceptPick(peer.seat, message)) send(peer, { kind: "draft-rejected" });
      } else if (peer.seat === 1 && session()?.seat !== 1 && !aborted) {
        if (message.kind === "draft-abort") {
          abort();
          refresh();
        } else if (message.kind === "draft-rejected") {
          pending = false;
          feedback.textContent = "そのピックは受け付けられませんでした。";
          refresh();
        } else if (message.kind === "draft-view") {
          const projection = decodeView(message.view);
          if (projection) show(projection);
        }
      }
    },
  };
}

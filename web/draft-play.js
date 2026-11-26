import { cardMedia, loadCards } from "./cards.js";
import { createDuelBoard, decodeDuel } from "./duel.js";
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
  const duel = (method, result, types, args) => wasm.ccall(`fab_web_duel_${method}`, result, types, args);
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
    heroes: (seat) => duel("heroes", "string", ["number"], [seat - 1]).split(" ").filter(Boolean),
    startDuel: (pair, [first, second]) => duel("start", "number", ["number", "string", "string", "number"],
      [pair, first, second, crypto.getRandomValues(new Uint32Array(1))[0]]) === 1,
    duelView: (seat) => duel("view", "string", ["number"], [seat - 1]),
    move: (seat, index) => duel("move", "number", ["number", "number"], [seat - 1, index]) === 1,
  };
}

const pairIndex = (seat) => Math.floor((seat - 1) / 2);
const pairSide = (seat) => (seat - 1) % 2;

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
  let paused = false;
  let epoch = 0;
  let displayed;
  let displayedKey;
  let hostLink;
  let awaitingView = false;
  let duelView;
  let duelPending = false;
  const duelBoard = createDuelBoard((choice) => {
    refresh();
    if (!duelView || paused || awaitingView || duelPending) return;
    const message = { kind: "draft-duel", epoch, revision: duelView.revision, ...choice };
    if (pod) {
      if (!acceptDuel(1, message)) duelBoard.reject();
    } else {
      duelPending = send(connected()[0], message);
      if (!duelPending) duelBoard.reject();
      refresh();
    }
  });

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
          if (pending || paused || awaitingView) return;
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

  function refresh() {
    const room = session();
    const peers = connected();
    const host = room?.seat === 1;
    if (pod) {
      const live = pod.ids.map((id) => peers.find((peer) => peer.id === id));
      if (live.length !== pod.live.length || live.some((peer, index) => peer !== pod.live[index])) {
        // A restored link needs the latest projection even if its cards did not change.
        for (const previous of pod.live) if (previous && !live.includes(previous)) pod.sent.delete(previous);
        pod.live = live;
        const interrupted = live.some((peer) => !peer);
        if (interrupted && !pod.paused) pod.epoch++;
        pod.paused = interrupted;
        publishViews();
      }
    } else if (room && !host && hostLink !== peers[0]) {
      hostLink = peers[0];
      awaitingView = Boolean(view);
      if (hostLink) send(hostLink, { kind: "draft-sync" });
    }
    const stopped = paused || awaitingView;
    duelBoard.show(duelView, stopped, duelPending);
    start.hidden = !host || Boolean(view);
    start.disabled = peers.length !== 7 || starting;
    next.hidden = !host || view?.phase !== "review";
    next.disabled = stopped;
    pick.hidden = !view?.pack;
    pick.disabled = stopped || selected === undefined || pending;
    for (const choice of grid.querySelectorAll("button")) choice.disabled = stopped;
    let summary = room && !host ? "ホストの開始を待っています。" : "8席がそろうと開始できます。";
    if (stopped) summary = "一時停止中 · 全員の再接続を待っています。";
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
    if (moveFocus) phase.focus({ preventScroll: true });
  }

  function showPacket(packet) {
    const key = JSON.stringify(packet);
    const resynced = awaitingView;
    paused = packet.paused;
    epoch = packet.epoch;
    awaitingView = false;
    if (displayedKey === key && !resynced) return;
    if (displayed?.view !== packet.view || displayed?.epoch !== packet.epoch || resynced) show(decodeView(packet.view));
    displayed = packet;
    displayedKey = key;
    duelView = packet.duel ? decodeDuel(packet.duel) : undefined;
    duelPending = false;
  }

  function publishViews(force) {
    const current = pod;
    const packet = (seat) => {
      const encoded = current.engine.view(seat);
      const match = current.matches[pairIndex(seat)];
      const side = pairSide(seat);
      const duel = encoded.startsWith("complete\n")
        ? {
            seat, revision: match.revision,
            heroes: match.started ? [] : current.engine.heroes(seat),
            selected: match.heroes[side],
            board: match.started ? current.engine.duelView(seat) : "",
          }
        : undefined;
      return { kind: "draft-view", view: encoded, paused: current.paused, epoch: current.epoch, duel };
    };
    showPacket(packet(1));
    for (const peer of current.live) {
      if (!peer) continue;
      const message = packet(peer.seat);
      const key = JSON.stringify(message);
      if (peer !== force && current.sent.get(peer) === key) continue;
      if (send(peer, message)) current.sent.set(peer, key);
    }
  }

  function acceptDuel(seat, message) {
    refresh();
    if (pod.paused || message.epoch !== pod.epoch || view?.phase !== "complete") return false;
    const pair = pairIndex(seat);
    const match = pod.matches[pair];
    const side = pairSide(seat);
    if (match.revision !== message.revision) return false;
    if (match.started) {
      if (!Number.isSafeInteger(message.index) || message.index < 0 || message.index > 0xffffffff ||
          !pod.engine.move(seat, message.index)) return false;
      match.revision++;
    } else {
      if (match.heroes[side] || !pod.engine.heroes(seat).includes(message.hero)) return false;
      match.heroes[side] = message.hero;
      if (match.heroes.every(Boolean)) {
        if (!pod.engine.startDuel(pair, match.heroes)) {
          match.heroes[side] = undefined;
          return false;
        }
        match.started = true;
        match.revision++;
      }
    }
    publishViews();
    refresh();
    return true;
  }

  function acceptPick(seat, message) {
    refresh();
    if (pod.paused || message.epoch !== pod.epoch) return false;
    const current = decodeView(pod.engine.view(seat));
    if (!current?.pack || current.booster !== message.booster || current.pack.length !== message.size ||
        typeof message.card !== "string" || !current.pack.includes(message.card)) return false;
    if (!pod.engine.pick(seat, message.card)) return false;
    publishViews();
    refresh();
    return true;
  }

  start.addEventListener("click", async () => {
    const room = session();
    const peers = connected();
    if (room?.seat !== 1 || peers.length !== 7 || starting || pod) return;
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
      const matches = Array.from({ length: 4 }, () => ({ heroes: [undefined, undefined], started: false, revision: 0 }));
      pod = { engine, ids: peers.map((peer) => peer.id), live: [], sent: new WeakMap(), paused: false, epoch: 0, matches };
      refresh();
    } catch (error) {
      if (room === session()) feedback.textContent = error.message;
    } finally {
      if (engine && !pod) engine.reset();
      starting = false;
      refresh();
    }
  });

  next.addEventListener("click", () => {
    refresh();
    if (pod && !pod.paused && pod.engine.next()) {
      publishViews();
      refresh();
    }
  });

  pick.addEventListener("click", () => {
    refresh();
    if (!view?.pack || selected === undefined || pending || paused || awaitingView) return;
    const message = { kind: "draft-pick", epoch, booster: view.booster, size: view.pack.length, card: view.pack[selected] };
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
    duelBoard.setCatalog(data);
    if (view) renderCards();
  }).catch(() => {});

  return {
    refresh,
    reset() {
      pod?.engine.reset();
      pod = undefined;
      paused = false;
      awaitingView = false;
      epoch = 0;
      duelView = undefined;
      duelPending = false;
      hostLink = undefined;
      displayed = undefined;
      displayedKey = undefined;
      show(undefined);
      refresh();
    },
    receive(peer, message) {
      if (message.kind === "draft-pick") {
        if (!pod?.ids.includes(peer.id) || !connected().includes(peer)) return;
        if (!acceptPick(peer.seat, message)) send(peer, { kind: "draft-rejected", epoch: message.epoch });
      } else if (message.kind === "draft-duel") {
        if (!pod?.ids.includes(peer.id) || !connected().includes(peer)) return;
        if (!acceptDuel(peer.seat, message)) send(peer, { kind: "draft-duel-rejected", epoch: message.epoch });
      } else if (message.kind === "draft-sync" && pod?.ids.includes(peer.id)) {
        refresh();
        publishViews(peer);
      } else if (peer.seat === 1 && session()?.seat !== 1 && connected().includes(peer)) {
        if (message.kind === "draft-rejected" && message.epoch === epoch) {
          pending = false;
          feedback.textContent = "そのピックは受け付けられませんでした。";
          refresh();
        } else if (message.kind === "draft-duel-rejected" && message.epoch === epoch) {
          duelPending = false;
          duelBoard.reject();
          refresh();
        } else if (message.kind === "draft-view" && typeof message.paused === "boolean" &&
                   Number.isSafeInteger(message.epoch) && message.epoch >= epoch && decodeView(message.view)) {
          showPacket(message);
          refresh();
        }
      }
    },
  };
}

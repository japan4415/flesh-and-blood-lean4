import { createDraftPlay } from "./draft-play.js";

const enter = document.querySelector("#enter");
const reconnect = document.querySelector("#reconnect");
const probe = document.querySelector("#probe");
const leave = document.querySelector("#leave");
const invite = document.querySelector("#invite");
const inviteUrl = document.querySelector("#invite-url");
const status = document.querySelector("#draft-status");
const count = document.querySelector("#connection-count");
const table = document.querySelector("#connections");
const invitedRoom = new URL(location.href).searchParams.get("room");
const savedSeat = `draft-seat:${invitedRoom}`;
const batchSize = 10;
const links = new Map();
let session;
let pollTimer;
let reconnectTimer;
let reconnecting = false;
let run = 0;

async function signal(message, keepalive = false) {
  const response = await fetch("/draft/signal", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(message),
    keepalive,
  });
  const payload = await response.json();
  if (!response.ok) throw Object.assign(new Error(payload.error), { status: response.status });
  return payload;
}

const ready = (link) => link?.pc.connectionState === "connected" && link.channel?.readyState === "open";
const connected = () => [...links.values()].filter(ready);
const play = createDraftPlay({
  session: () => session,
  connected,
  lock: (room, peers) => signal({ ...room, action: "lock", peers: peers.map((peer) => peer.id) }),
  send(link, message) {
    if (!ready(link)) return false;
    link.channel.send(JSON.stringify(message));
    return true;
  },
});

function render() {
  const host = session?.seat !== undefined ? session.seat === 1 : !invitedRoom;
  const seats = host ? [2, 3, 4, 5, 6, 7, 8] : [1];
  const active = connected().length;
  reconnect.hidden = !session || host || active > 0;
  reconnect.disabled = reconnecting;
  const total = `${active} / ${seats.length} 接続`;
  if (count.textContent !== total) count.textContent = total;
  probe.disabled = active === 0;
  table.replaceChildren(...seats.map((seat) => {
    const link = [...links.values()].find((peer) => peer.seat === seat);
    const row = document.createElement("tr");
    row.dataset.seat = seat;
    const state = ready(link) ? "open" : link?.state ?? "waiting";
    row.dataset.state = state;
    const labels = { open: "接続済み", connecting: "接続中", closed: "切断", failed: "失敗", waiting: "待機中" };
    for (const value of [
      seat === 1 ? "ホスト" : `席 ${seat}`, labels[state],
      link?.sent ? `${link.acked} / ${link.sent}` : "—", link?.received || "—",
    ]) {
      const cell = document.createElement("td");
      cell.textContent = value;
      row.append(cell);
    }
    return row;
  }));
  play.refresh();
}

function receive(link, data) {
  if (typeof data !== "string" || data.length > 4096 || links.get(link.id) !== link) return;
  let message;
  try { message = JSON.parse(data); } catch { return; }
  if (typeof message?.kind !== "string") return;
  if (message.kind.startsWith("draft-")) {
    play.receive(link, message);
    return;
  }
  if (!Number.isSafeInteger(message.run) || !Number.isSafeInteger(message.number) ||
      message.number < 1 || message.number > batchSize) return;
  if (message.kind === "ping") {
    if (message.number === 1 && message.run > link.incomingRun) {
      link.incomingRun = message.run;
      link.received = 0;
    }
    if (message.run !== link.incomingRun || message.number !== link.received + 1) return;
    link.received++;
    link.channel.send(JSON.stringify({ ...message, kind: "pong" }));
  } else if (message.kind === "pong" && message.run === link.outgoingRun &&
             message.number === link.acked + 1 && message.number <= link.sent) {
    link.acked++;
  }
  render();
}

function attachChannel(link, channel) {
  link.channel = channel;
  channel.addEventListener("open", () => connectionChanged(link));
  channel.addEventListener("message", (event) => receive(link, event.data));
  channel.addEventListener("close", () => {
    if (link.state !== "failed") link.state = "closed";
    connectionChanged(link);
  });
  render();
}

function connectionChanged(link) {
  if (links.get(link.id) !== link) return;
  if (ready(link)) {
    clearTimeout(reconnectTimer);
    if (session?.seat !== 1) status.textContent = `席 ${session.seat} として参加中`;
  } else if (session?.seat !== 1 && !reconnecting &&
             (["closed", "failed", "disconnected"].includes(link.pc.connectionState) ||
              link.channel?.readyState === "closed")) {
    clearTimeout(reconnectTimer);
    reconnectTimer = setTimeout(reconnectGuest, 2200);
  }
  render();
}

function createLink({ id, seat, generation }) {
  const pc = new RTCPeerConnection({ iceServers: [] });
  const previous = links.get(id);
  const link = { id, seat, generation, pc, state: "connecting", sent: 0, acked: 0, received: 0, incomingRun: 0 };
  links.set(id, link);
  previous?.pc.close();
  pc.addEventListener("connectionstatechange", () => {
    if (pc.connectionState === "failed") {
      link.state = "failed";
      pc.close();
    } else if (pc.connectionState === "disconnected") {
      link.state = "closed";
    }
    connectionChanged(link);
  });
  pc.addEventListener("datachannel", ({ channel }) => {
    if (link.channel || channel.label !== "draft-test") channel.close();
    else attachChannel(link, channel);
  });
  render();
  return link;
}

async function publishDescription(link, current) {
  const { pc } = link;
  await pc.setLocalDescription();
  if (pc.iceGatheringState !== "complete") {
    await new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        pc.removeEventListener("icegatheringstatechange", onChange);
        reject(new Error("ICE候補の収集がタイムアウトしました"));
      }, 10_000);
      function onChange() {
        if (pc.iceGatheringState !== "complete") return;
        clearTimeout(timer);
        pc.removeEventListener("icegatheringstatechange", onChange);
        resolve();
      }
      pc.addEventListener("icegatheringstatechange", onChange);
    });
  }
  if (session === current && links.get(link.id) === link) {
    await signal({ ...current, action: "description", target: link.id,
      generation: link.generation, description: pc.localDescription });
  }
}

async function handleEvent(event, current) {
  if (event.kind === "left") {
    const previous = links.get(event.id);
    links.delete(event.id);
    previous?.pc.close();
    render();
    return;
  }
  try {
    if (event.kind === "joined") {
      const link = createLink(event);
      attachChannel(link, link.pc.createDataChannel("draft-test", { ordered: true }));
      await publishDescription(link, current);
    } else if (event.kind === "description") {
      const existing = links.get(event.id);
      if (current.seat === 1 ? existing?.generation !== event.generation : current.generation !== event.generation) return;
      const link = existing ?? createLink(event);
      await link.pc.setRemoteDescription(event.description);
      if (event.description.type === "offer") await publishDescription(link, current);
    }
  } catch (error) {
    const link = links.get(event.id);
    if (session === current && link?.generation === event.generation) {
      link.state = "failed";
      link.pc.close();
      status.textContent = error.message;
      connectionChanged(link);
    }
  }
}

async function poll(current) {
  try {
    const { events } = await signal({ ...current, action: "poll" });
    if (session !== current || reconnecting) return;
    for (const event of events) {
      current.after = event.sequence;
      void handleEvent(event, current);
    }
  } catch (error) {
    if (session !== current || reconnecting) return;
    status.textContent = error.status === 404 ? "ルームが終了しました" : error.message;
    if (error.status === 403 || error.status === 404) stop(false);
  }
  if (session === current) pollTimer = setTimeout(() => poll(current), 350);
}

function clearLinks() {
  const previous = [...links.values()];
  links.clear();
  for (const link of previous) link.pc.close();
}

async function reconnectGuest() {
  const current = session;
  if (!current || current.seat === 1 || reconnecting || connected().length) return;
  reconnecting = true;
  clearTimeout(reconnectTimer);
  clearTimeout(pollTimer);
  clearLinks();
  status.textContent = "元の席に再接続中…";
  render();
  try {
    const room = await signal({ ...current, action: "reconnect" });
    if (session !== current) return;
    session = room;
    reconnecting = false;
    render();
    void poll(room);
  } catch (error) {
    if (session !== current) return;
    status.textContent = error.message;
    reconnecting = false;
    if (error.status === 403 || error.status === 404) stop(false);
    else reconnectTimer = setTimeout(reconnectGuest, 2200);
  } finally {
    if (session === current) render();
  }
}

function stop(notify) {
  if (!session) return;
  if (notify) void signal({ ...session, action: "leave" }, true).catch(() => {});
  session = undefined;
  reconnecting = false;
  clearTimeout(pollTimer);
  clearTimeout(reconnectTimer);
  clearLinks();
  play.reset();
  enter.disabled = false;
  enter.hidden = false;
  invite.hidden = true;
  leave.hidden = true;
  if (invitedRoom) enter.textContent = sessionStorage.getItem(savedSeat) ? "同じ席に再接続" : "ルームに参加";
  render();
}

enter.addEventListener("click", async () => {
  enter.disabled = true;
  status.textContent = "ルームに接続中…";
  try {
    let room;
    const key = invitedRoom && sessionStorage.getItem(savedSeat);
    if (key) {
      try {
        room = await signal({ action: "reconnect", roomId: invitedRoom, key });
      } catch (error) {
        if (error.status !== 403) throw error;
        sessionStorage.removeItem(savedSeat);
      }
    }
    room ??= await signal(invitedRoom ? { action: "join", roomId: invitedRoom } : { action: "create" });
    if (invitedRoom) sessionStorage.setItem(savedSeat, room.key);
    session = room;
    enter.hidden = true;
    leave.hidden = false;
    status.textContent = room.seat === 1 ? "ホストとして参加中" : `席 ${room.seat} として参加中`;
    if (room.seat === 1) {
      const url = new URL("/draft", location.origin);
      url.searchParams.set("room", room.roomId);
      inviteUrl.value = url.href;
      invite.hidden = false;
    }
    render();
    void poll(session);
  } catch (error) {
    enter.disabled = false;
    status.textContent = error.message;
  }
});

probe.addEventListener("click", () => {
  run++;
  for (const link of connected()) {
    link.outgoingRun = run;
    link.acked = 0;
    link.sent = batchSize;
    for (let number = 1; number <= batchSize; number++) {
      link.channel.send(JSON.stringify({ kind: "ping", run, number }));
    }
  }
  render();
});

leave.addEventListener("click", () => {
  stop(true);
  status.textContent = "ルームから退出しました";
});
reconnect.addEventListener("click", reconnectGuest);
inviteUrl.addEventListener("click", () => inviteUrl.select());
window.addEventListener("pagehide", () => stop(true));
if (invitedRoom) {
  enter.textContent = sessionStorage.getItem(savedSeat) ? "同じ席に再接続" : "ルームに参加";
  status.textContent = "参加するとホストとの接続を開始します。";
}
if (!globalThis.RTCPeerConnection) {
  enter.disabled = true;
  status.textContent = "このブラウザではWebRTCを利用できません。";
}
render();

const enter = document.querySelector("#enter");
const probe = document.querySelector("#probe");
const leave = document.querySelector("#leave");
const invite = document.querySelector("#invite");
const inviteUrl = document.querySelector("#invite-url");
const status = document.querySelector("#draft-status");
const count = document.querySelector("#connection-count");
const table = document.querySelector("#connections");
const invitedRoom = new URL(location.href).searchParams.get("room");
const batchSize = 10;
const links = new Map();
let session;
let pollTimer;
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

function render() {
  const host = session?.seat !== undefined ? session.seat === 1 : !invitedRoom;
  const seats = host ? [2, 3, 4, 5, 6, 7, 8] : [1];
  const active = [...links.values()].filter((link) => link.channel?.readyState === "open").length;
  const total = `${active} / ${seats.length} 接続`;
  if (count.textContent !== total) count.textContent = total;
  probe.disabled = active === 0;
  table.replaceChildren(...seats.map((seat) => {
    const link = [...links.values()].find((peer) => peer.seat === seat);
    const row = document.createElement("tr");
    row.dataset.seat = seat;
    const state = link?.channel?.readyState === "open" ? "open" : link?.state ?? "waiting";
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
}

function receive(link, data) {
  if (typeof data !== "string" || data.length > 256) return;
  let message;
  try { message = JSON.parse(data); } catch { return; }
  if (!message || !Number.isSafeInteger(message.run) || !Number.isSafeInteger(message.number) ||
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
  channel.addEventListener("open", render);
  channel.addEventListener("message", (event) => receive(link, event.data));
  channel.addEventListener("close", () => {
    if (link.state !== "failed") link.state = "closed";
    render();
  });
  render();
}

function createLink({ id, seat }) {
  const pc = new RTCPeerConnection({ iceServers: [] });
  const link = { id, seat, pc, state: "connecting", sent: 0, acked: 0, received: 0, incomingRun: 0 };
  links.set(id, link);
  pc.addEventListener("connectionstatechange", () => {
    if (pc.connectionState === "failed") {
      link.state = "failed";
      pc.close();
    }
    render();
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
    await signal({ ...current, action: "description", target: link.id, description: pc.localDescription });
  }
}

async function handleEvent(event, current) {
  if (event.kind === "left") {
    links.get(event.id)?.pc.close();
    links.delete(event.id);
    render();
    return;
  }
  try {
    if (event.kind === "joined") {
      const link = createLink(event);
      attachChannel(link, link.pc.createDataChannel("draft-test", { ordered: true }));
      await publishDescription(link, current);
    } else if (event.kind === "description") {
      const link = links.get(event.id) ?? createLink(event);
      await link.pc.setRemoteDescription(event.description);
      if (event.description.type === "offer") await publishDescription(link, current);
    }
  } catch (error) {
    const link = links.get(event.id);
    if (session === current && link) {
      link.state = "failed";
      link.pc.close();
      status.textContent = error.message;
      render();
    }
  }
}

async function poll(current) {
  try {
    const { events } = await signal({ ...current, action: "poll" });
    if (session !== current) return;
    for (const event of events) {
      current.after = event.sequence;
      void handleEvent(event, current);
    }
  } catch (error) {
    if (session !== current) return;
    status.textContent = error.status === 404 ? "ルームが終了しました" : error.message;
    if (error.status === 403 || error.status === 404) stop(false);
  }
  if (session === current) pollTimer = setTimeout(() => poll(current), 350);
}

function stop(notify) {
  if (!session) return;
  if (notify) void signal({ ...session, action: "leave" }, true).catch(() => {});
  session = undefined;
  clearTimeout(pollTimer);
  for (const link of links.values()) link.pc.close();
  links.clear();
  enter.disabled = false;
  enter.hidden = false;
  invite.hidden = true;
  leave.hidden = true;
  render();
}

enter.addEventListener("click", async () => {
  enter.disabled = true;
  status.textContent = "ルームに接続中…";
  try {
    const room = await signal(invitedRoom ? { action: "join", roomId: invitedRoom } : { action: "create" });
    session = { ...room, after: 0 };
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
  for (const link of links.values()) {
    if (link.channel?.readyState !== "open") continue;
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
inviteUrl.addEventListener("click", () => inviteUrl.select());
window.addEventListener("pagehide", () => stop(true));
if (invitedRoom) {
  enter.textContent = "ルームに参加";
  status.textContent = "参加するとホストとの接続を開始します。";
}
if (!globalThis.RTCPeerConnection) {
  enter.disabled = true;
  status.textContent = "このブラウザではWebRTCを利用できません。";
}
render();

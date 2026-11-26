import { randomUUID } from "node:crypto";

const rooms = new Map();
const leaseMs = 120_000;
const seatCount = 8;

function reply(response, status, body) {
  response.writeHead(status, { "Content-Type": "application/json" }).end(JSON.stringify(body));
}

function addMember(room, seat) {
  const member = { id: randomUUID(), key: randomUUID(), seat, seen: Date.now(), next: 1, events: [], generation: 1 };
  room.members.set(member.key, member);
  return member;
}

function sendEvent(member, event) {
  member.events.push({ ...event, sequence: member.next++ });
}

function credentials(room, member) {
  return { roomId: room.id, key: member.key, seat: member.seat, generation: member.generation, after: member.next - 1 };
}

function removeMember(room, member) {
  if (member.seat === 1) {
    rooms.delete(room.id);
    return;
  }
  if (room.locked) {
    member.generation++;
    member.events = [];
  } else {
    room.members.delete(member.key);
  }
  sendEvent(room.host, { kind: "left", id: member.id });
}

setInterval(() => {
  const expiredBefore = Date.now() - leaseMs;
  for (const room of rooms.values()) {
    if (room.host.seen < expiredBefore) {
      rooms.delete(room.id);
      continue;
    }
    if (!room.locked) {
      for (const member of room.members.values()) {
        if (member.seen < expiredBefore) removeMember(room, member);
      }
    }
  }
}, 5_000).unref();

async function readMessage(request) {
  let size = 0;
  const chunks = [];
  for await (const chunk of request) {
    size += chunk.length;
    if (size > 64 * 1024) throw new Error("Signaling message is too large");
    chunks.push(chunk);
  }
  const message = JSON.parse(Buffer.concat(chunks).toString());
  if (!message || typeof message !== "object" || Array.isArray(message)) throw new Error("Invalid message");
  return message;
}

export async function draftSignal(request, response) {
  if (request.method !== "POST") {
    response.setHeader("Allow", "POST");
    reply(response, 405, { error: "POST required" });
    return;
  }
  if (request.headers["content-type"]?.split(";")[0] !== "application/json") {
    reply(response, 415, { error: "JSON signaling message required" });
    return;
  }
  let message;
  try {
    message = await readMessage(request);
  } catch {
    reply(response, 400, { error: "Invalid signaling message" });
    return;
  }
  const { action, roomId, key } = message;
  if (action === "create") {
    const room = { id: randomUUID(), members: new Map() };
    room.host = addMember(room, 1);
    rooms.set(room.id, room);
    reply(response, 201, credentials(room, room.host));
    return;
  }
  const room = rooms.get(roomId);
  if (!room) {
    reply(response, 404, { error: "ルームが見つかりません" });
    return;
  }
  if (action === "join") {
    if (room.locked) {
      reply(response, 409, { error: "ドラフトは開始済みです" });
      return;
    }
    const occupied = new Set([...room.members.values()].map((member) => member.seat));
    const seat = Array.from({ length: seatCount - 1 }, (_, i) => i + 2)
      .find((number) => !occupied.has(number));
    if (!seat) {
      reply(response, 409, { error: "ルームは満員です" });
      return;
    }
    const member = addMember(room, seat);
    sendEvent(room.host, { kind: "joined", id: member.id, seat, generation: member.generation });
    reply(response, 201, credentials(room, member));
    return;
  }
  const member = room.members.get(key);
  if (!member) {
    reply(response, 403, { error: "接続の有効期限が切れました" });
    return;
  }
  member.seen = Date.now();
  if (action === "reconnect" && member !== room.host) {
    member.generation++;
    member.events = [];
    sendEvent(room.host, { kind: "joined", id: member.id, seat: member.seat, generation: member.generation });
    reply(response, 200, credentials(room, member));
    return;
  }
  if (member !== room.host && message.generation !== member.generation) {
    reply(response, 403, { error: "この席は再接続されました" });
    return;
  }
  if (action === "poll") {
    const after = message.after;
    if (!Number.isSafeInteger(after) || after < 0 || after >= member.next) {
      reply(response, 400, { error: "Invalid signaling cursor" });
      return;
    }
    member.events = member.events.filter((event) => event.sequence > after);
    reply(response, 200, { events: member.events });
    return;
  }
  if (action === "leave") {
    removeMember(room, member);
    reply(response, 200, {});
    return;
  }
  const host = member === room.host;
  if (action === "lock") {
    if (!host) {
      reply(response, 403, { error: "ホストだけがドラフトを開始できます" });
      return;
    }
    const { peers } = message;
    if (!Array.isArray(peers) || peers.length !== seatCount - 1 || room.members.size !== seatCount ||
        [...room.members.values()].some((peer) => peer !== member && !peers.includes(peer.id))) {
      reply(response, 409, { error: "参加者が変わりました。接続状況を確認してください。" });
      return;
    }
    room.locked = true;
    reply(response, 200, {});
    return;
  }
  const target = host
    ? [...room.members.values()].find((peer) => peer.seat !== 1 && peer.id === message.target)
    : room.host;
  const description = message.description;
  const generation = host ? target?.generation : member.generation;
  if (action !== "description" || !target ||
      message.generation !== generation ||
      description?.type !== (host ? "offer" : "answer") || typeof description.sdp !== "string") {
    reply(response, 400, { error: "Invalid peer description" });
    return;
  }
  sendEvent(target, {
    kind: "description", id: member.id, seat: member.seat, generation,
    description: { type: description.type, sdp: description.sdp },
  });
  reply(response, 200, {});
}

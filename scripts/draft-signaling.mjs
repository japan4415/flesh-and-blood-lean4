import { randomUUID } from "node:crypto";

const rooms = new Map();
const leaseMs = 120_000;
const seatCount = 8;

function reply(response, status, body) {
  response.writeHead(status, { "Content-Type": "application/json" }).end(JSON.stringify(body));
}

function addMember(room, seat) {
  const member = { id: randomUUID(), key: randomUUID(), seat, seen: Date.now(), next: 1, events: [] };
  room.members.set(member.key, member);
  return member;
}

function sendEvent(member, event) {
  member.events.push({ ...event, sequence: member.next++ });
}

function removeMember(room, member) {
  if (member.seat === 1) {
    rooms.delete(room.id);
    return;
  }
  room.members.delete(member.key);
  sendEvent(room.host, { kind: "left", id: member.id });
}

setInterval(() => {
  const expiredBefore = Date.now() - leaseMs;
  for (const room of rooms.values()) {
    if (room.host.seen < expiredBefore) {
      rooms.delete(room.id);
      continue;
    }
    for (const member of room.members.values()) {
      if (member.seen < expiredBefore) removeMember(room, member);
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
    reply(response, 201, { roomId: room.id, key: room.host.key, seat: 1 });
    return;
  }
  const room = rooms.get(roomId);
  if (!room) {
    reply(response, 404, { error: "ルームが見つかりません" });
    return;
  }
  if (action === "join") {
    const occupied = new Set([...room.members.values()].map((member) => member.seat));
    const seat = Array.from({ length: seatCount - 1 }, (_, i) => i + 2)
      .find((number) => !occupied.has(number));
    if (!seat) {
      reply(response, 409, { error: "ルームは満員です" });
      return;
    }
    const member = addMember(room, seat);
    sendEvent(room.host, { kind: "joined", id: member.id, seat });
    reply(response, 201, { roomId, key: member.key, seat });
    return;
  }
  const member = room.members.get(key);
  if (!member) {
    reply(response, 403, { error: "接続の有効期限が切れました" });
    return;
  }
  member.seen = Date.now();
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
  const target = host
    ? [...room.members.values()].find((peer) => peer.seat !== 1 && peer.id === message.target)
    : room.host;
  const description = message.description;
  if (action !== "description" || !target ||
      description?.type !== (host ? "offer" : "answer") || typeof description.sdp !== "string") {
    reply(response, 400, { error: "Invalid peer description" });
    return;
  }
  sendEvent(target, {
    kind: "description", id: member.id, seat: member.seat,
    description: { type: description.type, sdp: description.sdp },
  });
  reply(response, 200, {});
}

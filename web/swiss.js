const isSeat = (n) => Number.isInteger(n) && n >= 1 && n <= 8;

export function decodeSwiss(encoded) {
  if (typeof encoded !== "string") return undefined;
  const [head, ...rows] = encoded.split("\n");
  const [type, current, total, status] = head.split("\t");
  const round = Number(current);
  const rounds = Number(total);
  if (type !== "v" || rounds !== 3 || !Number.isInteger(round) || round < 1 || round > rounds ||
      !["playing", "review", "final"].includes(status)) return undefined;
  const tables = [], standings = [];
  for (const row of rows) {
    const [kind, first, second, third, fourth] = row.split("\t");
    const seat = Number(first);
    if (!isSeat(seat)) return undefined;
    if (kind === "p" && isSeat(Number(second)) && ["-", "first", "second", "draw"].includes(third)) {
      tables.push({ first: seat, second: Number(second), result: third });
    } else if (kind === "s" && [second, third, fourth].every((value) => /^[0-3]$/.test(value))) {
      standings.push({ seat, record: [second, third, fourth] });
    } else return undefined;
  }
  if (tables.length !== 4 || new Set(tables.flatMap(({ first, second }) => [first, second])).size !== 8 ||
      standings.length !== 8 || new Set(standings.map(({ seat }) => seat)).size !== 8) return undefined;
  return { round, rounds, status, tables, standings };
}

export function decodeSwissSeat(encoded, seat, event) {
  if (typeof encoded !== "string" || !isSeat(seat)) return undefined;
  const [header, heroes] = encoded.split("\n", 2);
  if (heroes === undefined) return undefined;
  const [opponent, side, revision, selected] = header.split("\t");
  const pair = event.tables.find((p) => p.first === seat || p.second === seat);
  if (!pair || (pair.first === seat ? side !== "0" || Number(opponent) !== pair.second
      : side !== "1" || Number(opponent) !== pair.first) ||
      !Number.isSafeInteger(Number(revision)) || Number(revision) < 0) return undefined;
  const { round, rounds, status } = event;
  return { seat, opponent: Number(opponent), side, revision: Number(revision),
    selected: selected || undefined, heroes: heroes.split(" ").filter(Boolean),
    board: encoded.slice(header.length + heroes.length + 2), round, rounds, status,
    rank: event.standings.findIndex((row) => row.seat === seat) + 1 };
}

function setRows(body, rows) {
  body.replaceChildren(...rows.map(({ values, mine }) => {
    const row = document.createElement("tr");
    row.toggleAttribute("data-mine", mine);
    for (const [index, label] of values.entries()) {
      const cell = document.createElement(index === 0 ? "th" : "td");
      if (index === 0) cell.scope = "row";
      cell.textContent = label;
      row.append(cell);
    }
    return row;
  }));
}

export function createSwissResults(nextRound) {
  const panel = document.querySelector("#swiss-results");
  const details = document.querySelector("#swiss-details");
  const summary = document.querySelector("#swiss-summary");
  const next = document.querySelector("#swiss-next");
  const tables = document.querySelector("#swiss-tables");
  const standings = document.querySelector("#swiss-standings");
  const caption = document.querySelector("#swiss-caption");
  let previous;
  let key;
  next.addEventListener("click", nextRound);
  return {
    show(event, seat, paused) {
      panel.hidden = !event;
      next.hidden = seat !== 1 || event?.status !== "review";
      next.disabled = paused;
      if (!event) {
        previous = undefined;
        key = undefined;
        details.open = false;
        return;
      }
      const encoded = JSON.stringify([event, seat]);
      if (key === encoded) return;
      key = encoded;
      const complete = event.status !== "playing";
      const finished = event.status === "final";
      if (previous?.status !== event.status || previous?.round !== event.round) details.open = complete;
      previous = event;
      const decided = event.tables.filter((table) => table.result !== "-").length;
      summary.textContent = finished ? "最終順位と対戦結果" : `対戦表・順位 · ${decided} / 4卓終了`;
      const scored = complete ? event.round : event.round - 1;
      caption.textContent = finished ? "最終順位" : scored > 0 ? `第${scored}ラウンド終了時点の順位` : "順位はラウンド終了時に集計";
      setRows(tables, event.tables.map(({ first, second, result }, i) => ({
        values: [`卓 ${i + 1}`, `席 ${first}`, `席 ${second}`,
          result === "-" ? "未確定" : result === "draw" ? "引き分け" : `席 ${result === "first" ? first : second}の勝利`],
        mine: first === seat || second === seat,
      })));
      setRows(standings, scored ? event.standings.map(({ seat: player, record }, index) => ({
        values: [String(index + 1), `席 ${player}`, ...record],
        mine: player === seat,
      })) : []);
      standings.closest("table").hidden = scored === 0;
    },
  };
}

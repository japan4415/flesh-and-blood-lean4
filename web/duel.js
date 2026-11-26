import { cardMedia } from "./cards.js";

const zones = {
  hero: "ヒーロー", weapon: "武器", head: "頭", chest: "胴", arms: "腕", legs: "脚",
  permanent: "場", deck: "山札", hand: "手札", arsenal: "アーセナル", pitch: "ピッチ",
  graveyard: "墓地", banished: "追放", inventory: "取得カードと支給品", soul: "ソウル",
  chain: "戦闘チェーン", stack: "解決待ち",
};

const actionLabels = {
  first: "先攻", equip: "装備する", deck: "デッキに入れる", ready: "デッキを確定",
  fill: "30枚まで自動で入れる", pass: "パス", play: "プレイ", instant: "インスタントでプレイ",
  attack: "攻撃", ability: "能力", defend: "防御", defendDone: "防御を確定", pitch: "ピッチ",
  cancel: "プレイを取り消す", mode: "モード", heroTarget: "ヒーローを対象にする",
  weaponTarget: "武器を対象にする", yes: "実行する", no: "見送る", resources: "追加リソース",
  handToDeck: "デッキに戻す", discard: "捨てる", select: "選ぶ", confirm: "選択を確定",
  handCost: "コストに使う", graveCost: "コストで追放する", top: "山札の上へ", bottom: "山札の下へ",
  arsenal: "アーセナルに置く", skipArsenal: "アーセナルに置かない", pitchReturn: "山札の下へ戻す",
  concede: "投了", triggerStart: "誘発の開始席", trigger: "誘発効果", graveTarget: "墓地から選ぶ",
  replacement: "置換効果", choose: "選ぶ",
};

const phases = { setup: "デッキ準備", startPhase: "開始フェーズ", actionPhase: "アクションフェーズ", endPhase: "終了フェーズ" };
const results = { win: "勝利", loss: "敗北", draw: "引き分け" };
const equipment = ["hero", "weapon", "head", "chest", "arms", "legs", "permanent"];

export function decodeDuel(data) {
  if (!data || !Number.isSafeInteger(data.seat) || data.seat < 1 || data.seat > 8 ||
      !Number.isSafeInteger(data.revision) || data.revision < 0 || typeof data.board !== "string" ||
      !Array.isArray(data.heroes) || !data.heroes.every((hero) => typeof hero === "string") ||
      (data.selected !== undefined && typeof data.selected !== "string")) return undefined;
  if (!data.board) return data;
  const [header, ...rows] = data.board.split("\n");
  const [kind, phase, turn, active, acting, life, opponentLife, resources, points, chi, result] = header.split("\t");
  if (kind !== "v" || !phase) return undefined;
  const board = { phase: phase.split(".").at(-1), turn, active, acting, life, opponentLife,
    resources, points, chi, result, zones: {}, actions: [] };
  for (const row of rows) {
    const [type, ...fields] = row.split("\t");
    if (type === "z") {
      const [name, count, cards] = fields;
      if (!Object.hasOwn(zones, name.split(".").at(-1)) || !Number.isSafeInteger(Number(count)) ||
          typeof cards !== "string") continue;
      board.zones[name] = { count: Number(count), cards: cards ? cards.split(" ").map((token) => {
        const [id, card] = token.split(":");
        return { id, card };
      }) : [] };
    } else if (type === "c") {
      const [attack, defense] = fields;
      board.combat = { attack, defense };
    } else if (type === "a") {
      const [index, action, object, card, detail = ""] = fields;
      if (Object.hasOwn(actionLabels, action) && Number.isSafeInteger(Number(index))) {
        board.actions.push({ index: Number(index), action, object, card, detail });
      }
    }
  }
  return { ...data, board };
}

function node(tag, label, className) {
  const element = document.createElement(tag);
  if (label) element.textContent = label;
  if (className) element.className = className;
  return element;
}

export function createDuelBoard(submit) {
  const panel = document.querySelector("#duel");
  const status = document.querySelector("#duel-status");
  const seats = document.querySelector("#duel-seats");
  const notice = document.querySelector("#duel-feedback");
  const controls = document.querySelector("#duel-controls");
  const grid = document.querySelector("#duel-board");
  let catalog = {};
  let current;
  let paused = false;
  let pending = false;
  let confirming;

  function cardInfo(id) {
    return Object.hasOwn(catalog, id) ? catalog[id] : { name: id, number: id };
  }

  function button(label, action, click) {
    const item = node("button", label);
    item.type = "button";
    item.dataset.action = action;
    item.addEventListener("click", click);
    return item;
  }

  function send(choice) {
    if (paused || pending) return;
    notice.textContent = "";
    submit(choice);
  }

  const side = () => String((current.seat - 1) % 2);
  const otherSeat = () => current.seat % 2 ? current.seat + 1 : current.seat - 1;
  const person = (id) => id === side() ? "自分" : "相手";

  function actionButton(move, withCard = false) {
    const label = actionLabels[move.action];
    let detail = move.detail === "-" ? "" : move.detail;
    if (["first", "heroTarget", "triggerStart"].includes(move.action)) detail = person(detail);
    if (withCard && move.card !== "-") detail = [cardInfo(move.card).name, detail].filter(Boolean).join(" · ");
    const result = button([label, detail].filter(Boolean).join(" · "), move.action, () => {
      if (move.action === "concede") {
        confirming = move.index;
        renderControls();
        controls.querySelector('[data-action="back"]').focus();
      } else {
        send({ index: move.index });
      }
    });
    result.dataset.index = move.index;
    return result;
  }

  function renderControls() {
    const actions = current.board.actions;
    if (confirming !== undefined) {
      const back = button("戻る", "back", () => {
        confirming = undefined;
        renderControls();
        controls.querySelector('[data-action="concede"]')?.focus();
      });
      controls.replaceChildren(node("span", "この対戦を投了しますか？"), back,
        button("投了を確定", "confirmConcede", () => send({ index: confirming })));
    } else {
      const present = new Set(Object.entries(current.board.zones).flatMap(([name, value]) => {
        if (name.endsWith(".deck") || name === "opponent.inventory" ||
            (name === "self.inventory" && current.board.phase !== "setup")) return [];
        return value.cards.map(({ id }) => id);
      }));
      controls.replaceChildren(...actions.filter((move) => !present.has(move.object))
        .map((move) => actionButton(move, true)));
    }
    setDisabled();
  }

  function setDisabled() {
    for (const item of panel.querySelectorAll("button")) item.disabled = paused || pending;
    panel.toggleAttribute("data-paused", paused);
  }

  function zone(key, actions) {
    const area = current.board.zones[key];
    if (!area) return undefined;
    const name = key.split(".").at(-1);
    const section = node("div", "", "duel-zone");
    section.dataset.zone = key;
    section.append(node("h4", `${zones[name]} · ${area.count}`));
    // Deck identities, if temporarily visible during a search, appear in the action list.
    if (!area.cards.length || name === "deck") return section;
    const cards = node("ul", "", "duel-cards");
    for (const { id, card } of area.cards) {
      const entry = node("li");
      const media = card && card !== "?" ? cardMedia(cardInfo(card), true)
        : node("div", card === "?" ? "効果" : "裏向き", "card-media");
      entry.append(media);
      if (card && card !== "?") entry.append(node("span", cardInfo(card).name, "duel-card-name"));
      const available = actions.filter((move) => move.object === id);
      if (available.length) {
        const choices = node("div", "", "duel-card-actions draft-actions");
        choices.append(...available.map((move) => actionButton(move)));
        entry.append(choices);
      }
      cards.append(entry);
    }
    section.append(cards);
    return section;
  }

  function zoneGroup(title, keys, actions) {
    const section = node("section", "", "duel-side");
    const layout = node("div", "", "duel-zones");
    for (const key of keys) {
      const item = zone(key, actions);
      if (item) layout.append(item);
    }
    section.append(node("h3", title), layout);
    return section;
  }

  function draw() {
    if (!current) return;
    const board = current.board;
    seats.textContent = `自分 席 ${current.seat} ／ 相手 席 ${otherSeat()}`;
    if (!board) {
      const cards = node("ul", "", "duel-cards duel-heroes");
      for (const id of current.heroes) {
        const card = cardInfo(id);
        const item = node("li");
        const select = button(card.name, "hero", () => send({ hero: id }));
        select.dataset.hero = id;
        item.append(cardMedia(card, true), select);
        cards.append(item);
      }
      controls.replaceChildren();
      grid.replaceChildren(...(current.selected ? [] : [cards]));
    } else {
      const player = (name, keys) => keys.map((key) => `${name}.${key}`);
      const arena = ["chain", "stack"].filter((key) => board.zones[key]?.count);
      const opponent = player("opponent", [...equipment, "hand", "deck", "arsenal", "pitch", "graveyard", "banished", "soul"]);
      const mine = player("self", [...equipment, "hand", "deck", "arsenal", "pitch", "graveyard", "banished", "soul"]);
      const parts = [zoneGroup(`相手 · ライフ ${board.opponentLife}`, opponent, board.actions)];
      if (arena.length) {
        const totals = board.combat ? ` · 攻撃 ${board.combat.attack} ／ 防御 ${board.combat.defense}` : "";
        parts.push(zoneGroup(`戦闘と効果${totals}`, arena, board.actions));
      }
      parts.push(zoneGroup(`自分 · ライフ ${board.life}`, mine, board.actions));
      if (board.phase === "setup") parts.push(zoneGroup("デッキと装備を選ぶ", ["self.inventory"], board.actions));
      grid.replaceChildren(...parts);
      renderControls();
    }
    setDisabled();
  }

  function updateStatus() {
    if (!current) return;
    const board = current.board;
    let summary;
    if (board && Object.hasOwn(results, board.result)) summary = results[board.result];
    else if (paused) summary = "一時停止中 · 全員の再接続を待っています。";
    else if (pending) summary = "ホストの確認を待っています…";
    else if (!board) {
      summary = current.selected ? `${cardInfo(current.selected).name}を選択済み · 相手の準備を待っています。`
        : "ヒーローを選ぶと、取得カードの中からデッキを組めます。";
    } else if (board.phase === "setup") {
      summary = board.acting !== side() ? "相手の準備を待っています。"
        : board.actions.some(({ action }) => action === "first") ? "先攻を選んでください。"
        : "装備を選び、30枚以上のデッキを確定してください。";
    } else {
      const turn = board.active === "-" ? "" : ` · ${person(board.active)}のターン`;
      const decision = board.acting === "-" ? "" : ` · ${person(board.acting)}が操作`;
      const chi = board.chi === "0" ? "" : ` · 気 ${board.chi}`;
      summary = `ターン ${board.turn}${turn} · ${phases[board.phase] ?? "対戦中"}${decision} · リソース ${board.resources} · アクション点 ${board.points}${chi}`;
    }
    if (status.textContent !== summary) status.textContent = summary;
  }

  return {
    show(data, stopped, waiting) {
      const changed = data?.seat !== current?.seat || data?.revision !== current?.revision ||
        data?.selected !== current?.selected;
      const advanceFocus = changed && panel.contains(document.activeElement);
      if (changed) {
        current = data;
        confirming = undefined;
        notice.textContent = "";
      }
      paused = stopped;
      pending = waiting;
      panel.hidden = !data;
      if (changed && data) draw();
      setDisabled();
      updateStatus();
      if (advanceFocus && data) status.focus({ preventScroll: true });
    },
    setCatalog(data) {
      catalog = data;
      draw();
      updateStatus();
    },
    reject() { notice.textContent = "その操作は受け付けられませんでした。"; },
  };
}

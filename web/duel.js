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
const equipment = ["head", "chest", "arms", "legs", "hero", "weapon", "permanent"];
const piles = ["deck", "arsenal", "graveyard", "pitch", "banished", "soul"];

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
  const hand = document.querySelector("#duel-hand");
  const inspect = document.querySelector("#duel-inspect");
  const inspectTitle = document.querySelector("#duel-inspect-title");
  const inspectImage = document.querySelector("#duel-inspect-image");
  let catalog = {};
  let current;
  let paused = false;
  let pending = false;
  let confirming;
  let selectedCard;

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

  function preview(id) {
    const card = cardInfo(id);
    inspectTitle.textContent = card.name;
    inspectImage.replaceChildren(cardMedia(card));
    inspect.showModal();
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
    const board = current.board;
    if (confirming !== undefined) {
      const back = button("戻る", "back", () => {
        confirming = undefined;
        renderControls();
        controls.querySelector('[data-action="concede"]')?.focus();
      });
      controls.replaceChildren(node("span", "この対戦を投了しますか？"), back,
        button("投了を確定", "confirmConcede", () => send({ index: confirming })));
    } else {
      const present = new Set(Object.entries(board.zones).flatMap(([name, value]) => {
        if (name.endsWith(".deck") || name === "opponent.inventory" ||
            (name === "self.inventory" && board.phase !== "setup")) return [];
        return value.cards.map(({ id }) => id);
      }));
      const general = board.actions.filter((move) => !present.has(move.object));
      const options = selectedCard ? board.actions.filter((move) => move.object === selectedCard.id) : [];
      const available = [...options, ...general];
      // Keep the confirmation control apart from ordinary play actions.
      const items = available.filter((move) => move.action !== "concede").map((move) => actionButton(move, true));
      if (selectedCard?.card && selectedCard.card !== "?") {
        items.push(button("カードを見る", "inspect", () => preview(selectedCard.card)));
      }
      const concede = general.find((move) => move.action === "concede");
      if (concede) items.push(actionButton(concede));
      controls.replaceChildren(...items);
    }
    setDisabled();
  }

  function setDisabled() {
    for (const item of panel.querySelectorAll("button[data-action]:not([data-action='inspect'])")) {
      item.disabled = paused || pending;
    }
    panel.toggleAttribute("data-paused", paused);
  }

  function selectCard(id, card, opener) {
    const previous = panel.querySelector(".duel-card[aria-pressed='true']");
    confirming = undefined;
    if (previous === opener) {
      selectedCard = undefined;
      opener.setAttribute("aria-pressed", "false");
      renderControls();
      return;
    }
    previous?.setAttribute("aria-pressed", "false");
    selectedCard = { id, card };
    opener.setAttribute("aria-pressed", "true");
    renderControls();
    controls.querySelector("button:not(:disabled)")?.focus();
  }

  function zone(key, expanded, fold = false) {
    const board = current.board;
    const area = board.zones[key];
    if (!area) return null;
    const name = key.split(".").at(-1);
    const hasCards = Boolean(area.cards.length) && name !== "deck";
    const section = node(fold && hasCards ? "details" : "div", "", "duel-zone");
    section.dataset.zone = key;
    section.toggleAttribute("data-empty", area.count === 0);
    const label = node(section.tagName === "DETAILS" ? "summary" : "div", "", "duel-zone-label");
    label.append(node("span", zones[name]), node("span", String(area.count), "duel-count"));
    section.append(label);
    if (section.tagName === "DETAILS") {
      section.open = expanded.has(key) || area.cards.some(({ id }) => board.actions.some((move) => move.object === id));
    }
    if (key === "opponent.hand") {
      const backs = node("div", "", "duel-backs");
      backs.setAttribute("aria-hidden", "true");
      for (let i = 0; i < area.count; i++) backs.append(node("span"));
      section.append(backs);
    }
    if (!hasCards) return section;
    const cards = node("ul", "", "duel-cards");
    for (const { id, card } of area.cards) {
      const entry = node("li");
      const visible = card && card !== "?";
      const media = visible ? cardMedia(cardInfo(card), true)
        : node("div", card === "?" ? "効果" : "裏向き", "card-media");
      media.setAttribute("aria-hidden", "true");
      const available = board.actions.filter((move) => move.object === id);
      const selectable = available.length > 0 && board.phase !== "setup";
      const cardName = visible ? cardInfo(card).name : media.textContent;
      const face = selectable || visible
        ? button("", selectable ? "selectCard" : "inspect", () => {
            if (selectable) selectCard(id, card, face);
            else preview(card);
          })
        : node("div");
      face.className = "duel-card";
      if (selectable) face.setAttribute("aria-pressed", String(selectedCard?.id === id));
      face.append(media);
      if (visible) face.append(node("span", cardName, "duel-card-name"));
      if (face.tagName === "BUTTON") face.title = cardName;
      if (selectable) face.setAttribute("aria-label", `${cardName}の操作を選ぶ`);
      entry.append(face);
      if (available.length && board.phase === "setup") {
        const choices = node("div", "", "duel-card-actions draft-actions");
        choices.append(...available.map((move) => actionButton(move)));
        entry.append(choices);
      }
      cards.append(entry);
    }
    section.append(cards);
    return section;
  }

  function playerStats(life, pool) {
    const stats = node("div", "", "duel-player-stats");
    const score = node("div", "", "duel-life");
    score.append(node("span", "ライフ"), node("strong", life));
    stats.append(score);
    if (pool) {
      const assets = node("dl", "", "duel-assets");
      const values = [["リソース", pool.resources], ["アクション点", pool.points]];
      if (pool.chi !== "0") values.push(["気", pool.chi]);
      for (const [label, value] of values) {
        const asset = node("div");
        asset.append(node("dt", label), node("dd", value));
        assets.append(asset);
      }
      stats.append(assets);
    }
    return stats;
  }

  function playerField(who, expanded) {
    const board = current.board;
    const own = who === "self";
    const name = own ? "自分" : "相手";
    const hero = board.zones[`${who}.hero`]?.cards[0]?.card;
    const section = node("section", "", "duel-side");
    section.dataset.player = who;
    section.toggleAttribute("data-active", board.active === (own ? side() : String(1 - Number(side()))));
    const header = node("div", "", "duel-player");
    const identity = node("div");
    identity.append(node("h3", name), node("p", hero ? cardInfo(hero).name : "", "duel-player-hero"));
    header.append(identity);
    const opponentHand = !own && zone("opponent.hand", expanded);
    if (opponentHand) header.append(opponentHand);
    if (!own || board.phase === "setup") header.append(playerStats(own ? board.life : board.opponentLife));
    const field = node("div", "", "duel-player-field");
    const gear = node("div", "", "duel-gear");
    const storage = node("div", "", "duel-piles");
    gear.append(...equipment.map((key) => zone(`${who}.${key}`, expanded)).filter(Boolean));
    storage.append(...piles.map((key) => zone(`${who}.${key}`, expanded, true)).filter(Boolean));
    field.append(gear, storage);
    section.append(header);
    section.append(field);
    return section;
  }

  function arenaField(expanded) {
    const board = current.board;
    const arena = node("section", "", "duel-arena");
    const header = node("div", "", "duel-arena-header");
    header.append(node("h3", "戦闘"));
    if (board.combat) {
      const { attack, defense } = board.combat;
      header.append(node("p", `攻撃 ${attack} ／ 防御 ${defense}`, "duel-combat-total"));
    }
    const slots = node("div", "", "duel-arena-slots");
    slots.append(...["chain", "stack"].map((key) => zone(key, expanded)).filter(Boolean));
    arena.append(header, slots);
    return arena;
  }

  function draw() {
    if (!current) return;
    const board = current.board;
    panel.dataset.stage = !board ? "hero" : board.phase === "setup" ? "setup" : "play";
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
      hand.replaceChildren();
      grid.replaceChildren(...(current.selected ? [] : [cards]));
    } else {
      const expanded = new Set([...grid.querySelectorAll("details[open]")].map((item) => item.dataset.zone));
      const opponent = playerField("opponent", expanded);
      const self = playerField("self", expanded);
      const inventory = board.phase === "setup" && zone("self.inventory", expanded);
      const ownHand = board.phase !== "setup" && zone("self.hand", expanded);
      if (ownHand) ownHand.firstElementChild.append(playerStats(board.life, board));
      grid.replaceChildren(opponent, arenaField(expanded), self, ...(inventory ? [inventory] : []));
      hand.replaceChildren(...(ownHand ? [ownHand] : []));
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
      summary = `ターン ${board.turn}${turn} · ${phases[board.phase] ?? "対戦中"}${decision}`;
    }
    if (status.textContent !== summary) status.textContent = summary;
  }

  return {
    show(data, stopped, waiting) {
      const opened = Boolean(data && !current);
      const changed = data?.seat !== current?.seat || data?.revision !== current?.revision ||
        data?.selected !== current?.selected;
      const advanceFocus = changed && panel.contains(document.activeElement) && !inspect.open;
      if (changed) {
        current = data;
        confirming = undefined;
        selectedCard = undefined;
        notice.textContent = "";
      }
      paused = stopped;
      pending = waiting;
      panel.hidden = !data;
      if (!data && inspect.open) inspect.close();
      if (changed && data) draw();
      setDisabled();
      updateStatus();
      if (opened) status.focus();
      else if (advanceFocus && data) status.focus({ preventScroll: true });
    },
    setCatalog(data) {
      catalog = data;
      draw();
      updateStatus();
    },
    reject() { notice.textContent = "その操作は受け付けられませんでした。"; },
  };
}

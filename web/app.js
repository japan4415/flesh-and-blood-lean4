import { cardMedia, loadCards } from "./cards.js";
import { loadWasm, sampleIndex } from "./wasm.js";

const runtime = document.querySelector("#runtime");
const openButton = document.querySelector("#open-pack");
const buttonLabel = document.querySelector("#button-label");
const resultStatus = document.querySelector("#result-status");
const grid = document.querySelector("#cards");

const slots = [
  ...Array(4).fill("Generic Common"),
  ...Array(7).fill("Class Common"),
  "Rare", "Rare以上", "装備", "Foil", "トークン",
];

function cardElement(id, slot, cards) {
  const card = cards[id];
  const item = document.createElement("li");
  item.className = "card";
  if (slot === "Foil") item.dataset.slot = "foil";
  const category = document.createElement("p");
  category.className = "card-slot";
  category.textContent = slot;
  const name = document.createElement("h3");
  name.className = "card-name";
  name.textContent = card.name;
  const number = document.createElement("p");
  number.className = "card-id";
  number.textContent = card.number;
  item.append(cardMedia(card), category, name, number);
  return item;
}

try {
  const [wasm, cards] = await Promise.all([loadWasm(), loadCards()]);
  const bounds = wasm.ccall("fab_web_bounds", "string").split(" ").map(Number);
  if (bounds.length !== slots.length || bounds.some((bound) => !Number.isSafeInteger(bound) || bound < 1)) {
    throw new Error("Invalid WASM slot layout");
  }

  let packCount = 0;
  openButton.addEventListener("click", () => {
    const choices = bounds.map(sampleIndex).join(" ");
    const ids = wasm.ccall("fab_web_open", "string", ["string"], [choices]).split(" ");
    if (ids.length !== slots.length || ids.some((id) => !Object.hasOwn(cards, id))) {
      resultStatus.textContent = "開封できませんでした。もう一度お試しください。";
      return;
    }
    grid.replaceChildren(...ids.map((id, index) => cardElement(id, slots[index], cards)));
    packCount += 1;
    resultStatus.textContent = `${packCount}パック目 · ${ids.length}枚`;
    buttonLabel.textContent = "もう1パック開封";
  });
  runtime.dataset.state = "ready";
  runtime.textContent = "WASM 起動済み";
  openButton.disabled = false;
} catch (error) {
  console.error(error);
  runtime.dataset.state = "error";
  runtime.textContent = "起動に失敗しました";
  resultStatus.textContent = "WASMのビルドとWebサーバーの設定を確認してください。";
}

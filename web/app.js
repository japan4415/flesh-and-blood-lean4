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

function loadWasm() {
  return new Promise((resolve, reject) => {
    if (!globalThis.crossOriginIsolated) {
      reject(new Error("WASM requires cross-origin isolation"));
      return;
    }
    window.Module = {
      noInitialRun: true,
      onRuntimeInitialized() {
        const module = window.Module;
        if (module.ccall("fab_web_init", "number") === 1) resolve(module);
        else reject(new Error("Lean initialization failed"));
      },
      onAbort: reject,
    };
    const script = document.createElement("script");
    script.src = "/wasm/fab.js";
    script.onerror = () => reject(new Error("Could not load fab.js"));
    document.head.append(script);
  });
}

function sampleIndex(bound) {
  const value = new Uint32Array(1);
  const limit = 2 ** 32 - (2 ** 32 % bound);
  do {
    crypto.getRandomValues(value);
  } while (value[0] >= limit);
  return value[0] % bound;
}

function cardElement(id, slot, cards) {
  const card = cards[id];
  const item = document.createElement("li");
  item.className = "card";
  if (slot === "Foil") item.dataset.slot = "foil";
  const media = document.createElement("div");
  media.className = "card-media";
  const fallback = document.createElement("span");
  fallback.className = "card-fallback";
  fallback.textContent = card.number;
  fallback.setAttribute("aria-hidden", "true");
  media.append(fallback);

  const image = document.createElement("img");
  image.alt = card.name;
  image.referrerPolicy = "no-referrer";
  image.addEventListener("error", () => image.remove(), { once: true });
  image.src = card.image;
  media.append(image);

  const category = document.createElement("p");
  category.className = "card-slot";
  category.textContent = slot;
  const name = document.createElement("h3");
  name.className = "card-name";
  name.textContent = card.name;
  const number = document.createElement("p");
  number.className = "card-id";
  number.textContent = card.number;
  item.append(media, category, name, number);
  return item;
}

try {
  const [wasm, cards] = await Promise.all([
    loadWasm(),
    fetch("/cards.json").then((response) => {
      if (!response.ok) throw new Error("Could not load card catalogue");
      return response.json();
    }),
  ]);
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

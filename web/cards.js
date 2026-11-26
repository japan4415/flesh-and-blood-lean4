export async function loadCards() {
  const response = await fetch("/cards.json");
  if (!response.ok) throw new Error("カードカタログの読み込みに失敗しました。");
  return response.json();
}

export function cardMedia(card, lazy = false) {
  const media = document.createElement("div");
  media.className = "card-media";
  const fallback = document.createElement("span");
  fallback.className = "card-fallback";
  fallback.textContent = card.number;
  fallback.setAttribute("aria-hidden", "true");
  media.append(fallback);
  if (card.image) {
    const image = document.createElement("img");
    image.alt = card.name;
    image.referrerPolicy = "no-referrer";
    if (lazy) image.loading = "lazy";
    image.addEventListener("error", () => image.remove(), { once: true });
    image.src = card.image;
    media.append(image);
  }
  return media;
}

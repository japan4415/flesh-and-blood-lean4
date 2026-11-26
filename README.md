# flesh-and-blood-lean4

Flesh and Blood の公式ルール（Comprehensive Rules / Tournament Rules and Policy）を Lean 4 で形式化・検証するリポジトリです。

## ドキュメント

- [docs/README.md](docs/README.md) — ドキュメント一覧と読む順番
- [docs/original.md](docs/original.md) — 要求の正本（人間のみ編集）
- [docs/rules-model.md](docs/rules-model.md) — Flesh and Blood ルールの形式化メモ
- [docs/design.md](docs/design.md) — 全体設計・データモデル・エンジン仕様
- [docs/roadmap.md](docs/roadmap.md) — マイルストーン M0〜M10 と不変条件カタログ

## 検証

```bash
./scripts/verify.sh
```

## WebAssembly

リリース公開時の `Release Build` に `fab-wasm` アーティファクトが生成されます。
`fab.js` と `fab.wasm` を同じディレクトリに置き、Node.jsでWTRのパックを開封できます。
引数は封入枠ごとの0始まりの候補番号16個で、出力は枠順の論理カードIDです。

```bash
node fab.js 0 1 2 3 0 1 2 3 4 5 6 0 1 0 0 1
```

ローカルでは、`lean-toolchain` のLean、CMake、Emscripten 4.0.23をPATHに置いて
`bash scripts/build-wasm.sh` を実行すると `.lake/wasm/output/` に生成されます。

### ブラウザでパックを開封

WASMをビルドしてから `node scripts/serve-wasm.mjs` を実行し、
[ローカルの開封画面](http://127.0.0.1:4173/) を開きます。
開封に使う候補数とカードIDはWASMから取得し、ブラウザが各枠の候補を均等に抽選します。
カード画像は [公式Card Vault](https://cardvault.fabtcg.com/) のWTR収録番号ごとの画像URLを参照します。

## Disclaimer

Flesh and Blood, all associated logos, card names, card text, and rules content are trademarks and/or copyright © Legend Story Studios. All rights reserved.

`flesh-and-blood-lean4` is an unofficial, free, non-commercial fan / formal-verification project created in accordance with Legend Story Studios' Terms of Use for Game and Studio Assets and IP. Legend Story Studios does not endorse, sponsor, or affiliate with this project. Card images and flavor text are not included in this repository. See [NOTICE](NOTICE) for details.

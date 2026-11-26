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

### ブラウザで8人ドラフト

WASMをビルドしてから `node scripts/serve-wasm.mjs` を実行し、[ドラフト画面](http://127.0.0.1:4173/draft)を開きます。
ホストがルームを作成し、参加用リンクを7つのタブまたはブラウザに渡します。
`7 / 7 接続` になったらホストが「ドラフトを開始」を押します。各席はカードを選んで「選んだカードをピック」を押し、全席が確定すると次のパックが回ります。
1・2パック目を取り切ると自分の取得カードを確認できます。ホストが「次のパックを開く」を押すと再開し、3パック終了後は各席の取得カード45枚が表示されます。

ドラフト終了後は、同じ8人のポッド内で1ゲーム先取のスイス式を3ラウンド行います。初戦の組み合わせは抽選し、2戦目以降は再戦を避けて勝ち点の近い席を組み合わせます。4卓すべての結果が確定したら、ホストが「次のラウンドへ」を押します。第3ラウンド終了時に、全8席に最終順位を表示します。

選んだヒーローと取得カードは3ラウンドを通じて使用します。各ゲームで先攻を決め、取得カードと支給品から装備と30枚以上のデッキを確定します。「30枚まで自動で入れる」は利用可能なカードを取得順に追加します。ヒーローに合う取得カードが30枚に満たない席には必要枚数のCracked Baubleが支給されます。

勝利は1点、敗北と引き分けは0点です。同点の場合は累積マッチポイント、敗率、対戦相手の平均敗率、対戦相手の平均累積マッチポイントの順に比較し、最後まで同点なら開始時の抽選順で決めます。[公式大会規定 A.4](https://rules.fabtcg.com/en/trp/appendix/#a4-tiebreakers)

ホストのLean/WASMがドラフトと対戦を進行し、各参加者には自席の表示情報と操作候補をWebRTC DataChannelで送ります。
一人でも切断すると、ドラフト操作・デッキ準備・全卓の対戦が一時停止し、全員が元の席に戻ると再開します。自動で戻れない場合は「再接続」、参加者が画面を再読み込みした場合は「同じ席に再接続」を押します。
状態を保持するホストのブラウザタブは開いたままにします。「通信テストを送信」でDataChannelの往復を確認できます。
同じLANの端末で試す場合は `FAB_HOST=0.0.0.0 node scripts/serve-wasm.mjs` で起動し、ホストは `localhost` を使います。参加用リンクの `localhost` をホストのLAN側IPアドレスに置き換えて共有します。

## Disclaimer

Flesh and Blood, all associated logos, card names, card text, and rules content are trademarks and/or copyright © Legend Story Studios. All rights reserved.

`flesh-and-blood-lean4` is an unofficial, free, non-commercial fan / formal-verification project created in accordance with Legend Story Studios' Terms of Use for Game and Studio Assets and IP. Legend Story Studios does not endorse, sponsor, or affiliate with this project. Card images and flavor text are not included in this repository. See [NOTICE](NOTICE) for details.

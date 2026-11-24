# docs

| 文書 | 内容 | 編集者 |
|---|---|---|
| [original.md](original.md) | **要求の正本。** 他の文書と食い違う場合はこれを優先する | 人間のみ |
| [rules-model.md](rules-model.md) | Flesh and Blood Comprehensive Rules（`rules.fabtcg.com` / v2.11 以降）を形式化の観点で整理したもの。規則番号つき。FaB 固有の仕組み（ピッチサイクル、Combat Chain、Attack-Proxy、8 ステージ連続効果、4 区分置換効果など）を網羅 | エージェント・人間 |
| [tournament-model.md](tournament-model.md) | Flesh and Blood Tournament Rules and Policy（TRP）のうち形式化の対象にする部分（CC / Blitz / LL / Limited / UPF、試合前ロードアウト、Bo1 マッチ、時間切れ、ループ） | エージェント・人間 |
| [design.md](design.md) | 実装方針（要求の整理、前提とする版、設計原則、全体構成、データモデル、エンジンと `Legal` 仕様、イベント経路と 4 区分置換、効果 IR と Hook、証明の方針、版管理、権利、テストと検証、決定事項・要確認事項、リスク） | エージェント・人間 |
| [roadmap.md](roadmap.md) | マイルストーン M0〜M10（途中に M3b。M10 は完了判定）と、証明を積み上げる順序、不変条件カタログ（I1〜I20）、カードの実装状況の定義 | エージェント・人間 |
| [lean-guidelines.md](lean-guidelines.md) | Lean 4 のコーディング規約（ツールチェーン、Lake、module system、命名、証明しやすい書き方、テスト、作業の単位とローカルでの検証） | エージェント・人間 |
| [card-data.md](card-data.md) | カードデータの取り込み（`the-fab-cube/flesh-and-blood-cards` 等）、Name + Pitch の同一性、効果 IR への写像、FaB 特有の難しいカード、新カード・新キーワード追加手順、LSS の権利面の注意 | エージェント・人間 |

読む順番: `original.md` → `rules-model.md`（FaB 固有のルール用語・構造を押さえる）→ `design.md` → `roadmap.md`。`tournament-model.md`、`lean-guidelines.md`、`card-data.md` は作業に応じて参照する。

文書の前提（2026-11-24 時点）:
- ルール: Flesh and Blood Comprehensive Rules **v2.15.0**（2026-09-28、`rules.fabtcg.com`）と Tournament Rules and Policy（2025-05-30 更新）
- 初期スコープ: **1v1 Classic Constructed（CC）**、カードセットは **Welcome to Rathe（WTR）** から着手
- カードデータ: `the-fab-cube/flesh-and-blood-cards`（公式エラッタ反映済みの JSON データベース）および公式カードデータベース
- Lean: `leanprover/lean4:v4.36.0`（Mathlib 非依存、core + Std + Plausible）

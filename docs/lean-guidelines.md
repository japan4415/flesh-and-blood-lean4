# Lean 4 コーディング規約

このリポジトリで Lean 4 を書くときの規約。設計の背景は [design.md](design.md) を参照。

本規約は先行プロジェクト（`riftbound-lean4`）で Lean v4.36.0 により実機確認済みの知見を引き継いでいる。本文中の **[確認済]** は Lean v4.36.0 での動作確認済み事項を指す。

---

## 1. ツールチェーン

- `lean-toolchain` には `leanprover/lean4:v4.36.0` を指定する（rc 版は使わない）。
- 更新方針: 新しい stable が出たら専用 PR で上げ、破壊的変更と依存パッケージ（Plausible 等）の対応タグを確認する。
- **Mathlib は使わない**（[design.md §12](design.md#12-初期の決定事項と要確認事項) D1）。理由:
  - 1 ファイルあたりの読み込み時間・メモリ消費が大きく増える（v4.36.0 実測: Init のみ 1.2 秒 / 385 MB、`Std` 2.1 秒 / 609 MB、`Lean` 6.3 秒 / 1.3 GB）。
  - 数 GB のキャッシュ取得が必要になり、Lean 更新が Mathlib に縛られる。
  - 古典論理・`noncomputable` な定義が多く、実行可能なルールエンジンと相性が悪い。
- Lean 4 core + `Std` には `List.Perm`、`omega` / `lia`、`grind`、`simp`、`decide`、`Std.ExtTreeMap` があり、エンジンと不変条件の証明にはこれで足りる。どうしても `Finset` / `aesop` 等が必要になった場合のみ、検証コアとは分離した別パッケージでの利用を検討する。

---

## 2. Lake の設定

`lakefile.toml` を使い、`lake-manifest.json` をコミットする。

```toml
name = "fab"
version = "0.1.0"
defaultTargets = ["Fab"]
testDriver = "FabTest"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false
linter.missingDocs = true

[[require]]
name = "plausible"
scope = "leanprover-community"
rev = "v4.36.0"

[[lean_lib]]
name = "Fab"          # 検証コア（P8 禁止事項・lake check 公理監査の対象）

[[lean_lib]]
name = "FabCards"     # カード定義と具体的な CardDB

[[lean_lib]]
name = "FabDriver"    # 乱数供給・自動対戦・トレース出力（IO 可。監査対象外）

[[lean_lib]]
name = "FabTest"      # テストドライバ
```

設定の意図:
- `defaultTargets = ["Fab"]`: `lake check` が検証コアのみを公理監査するようにする。
- `autoImplicit = false` / `relaxedAutoImplicit = false`: 綴り誤りが暗黙変数として通るのを防ぐ。
- `linter.missingDocs = true`: 公開宣言（帰納型コンストラクタ含む）への docstring 記載を強制し、CR/TRP の規則番号引用を漏れなく残す。
- **`lake lint` は使わない**: [確認済] core には環境 linter が無く、構文系 linter は `--wfail` 付きビルドで実行されるため、`lake build ... --wfail` で足りる。

---

## 3. module system

- **すべてのファイルを `module` にする。**
- **検証コアとルールのファイルは `@[expose] public section` で始める。** [確認済] `@[expose]` が無いと下流モジュールから `decide` / `simp` による定義展開ができない。

```lean
module

public import Fab.State.GameState

/-!
# Combat Chain

Combat Chain の 7 ステップ進行（CR 7.0-7.7）。
-/

@[expose] public section

namespace Fab
-- ...
end Fab

end
```

- [確認済] **module 内の `#guard` には `meta import` が必要。** 評価に使う定義を持つモジュールを `import X` と `meta import X` の両方で読み込む。
- [確認済] テスト用 fixture モジュールは、`meta def` を `public section` に置き、型に使うモジュールを `public import` する。使う側は `meta import FabTest.Fixtures` とする。

---

## 4. 命名・ファイル・docstring

### 4.1 命名

| 対象 | 規則 | 例 |
|---|---|---|
| 型・structure・inductive・型クラス | UpperCamelCase | `GameState`, `ChainLink`, `CardDef` |
| `Prop` を返す述語 | UpperCamelCase | `WF`, `OwnerOk`, `Settled`, `DeckValid`, `Legal` |
| 関数・データ | lowerCamelCase | `moveObj`, `legalActions`, `pitchCard`, `closeChain` |
| 定理 | snake_case | `moveObj_preserves_wf`, `stack_lifo`, `goAgain_gains_ap` |
| 仮定の並び | `_of_` で出現順 | `wf_step_of_wf`, `drawOne_lengths_of_ownerOk` |
| 同値 | `_iff` | `legalActions_iff`, `deckValid_iff` |
| `Option` 返し / panic しうる関数 | 末尾に `?` / `!` | `findObj?`, `activeLink?` |

- **語彙は FaB 公式 CR の英語用語に合わせる**（`pitch`, `arsenal`, `combatChain`, `chainLink`, `attackProxy`, `goAgain`, `battleworn`, `bladeBreak`, `temper`, `guardwell`, `phantasm`, `spectra`, `transcend`, `meld`）。日本語やローマ字の識別子は使わない。
- 型に属する操作は型と同名の namespace に置き、dot notation（`s.moveObj` 等）を使えるようにする。

### 4.2 ファイル

- ファイル名は UpperCamelCase でモジュール名と一致させる（`Fab/Rules/Combat.lean` → `Fab.Rules.Combat`）。
- 1 ファイルの目安は 1,000 行以内。ただしカード定義（`FabCards/<Set>.lean`）はビルド高速化のため **1 弾 1 ファイル** を例外として認める（エディタ再検査が重くなったら `FabCards/WTR/Part1.lean` のように分割）。
- 行長 100 文字以内、インデント 2 スペース（複数行ヘッダ続きは 4 スペース）、`by` は行末、`fun x ↦ ...` を使う。

### 4.3 docstring と規則番号

- ファイル先頭に module docstring（`/-! # 題名 ... -/`）、公開宣言に `/-- ... -/` を書く。
- **ルール由来の定義には `(CR 7.6.2)` / `(TRP 4.3)` の形式で規則番号を書く。** 複数なら `(CR 6.4.10, 6.5.1)`、範囲は `(CR 7.1-7.7)`。括弧内に説明文を混ぜない（`scripts/cr_citations.py` で機械抽出するため）。
- docstring は英語を基本とし（CR 用語と揃える）、`docs/` の設計文書は日本語で書く。
- カード定義の docstring には公式の英語カードテキスト（最新エラッタ適用後）を載せる。

---

## 5. 証明しやすいコードの書き方

### 5.1 再帰と停止性

- **`Fab`（検証コア）では `partial` / `unsafe` を禁止する。** `FabDriver` と CLI のみ許可。
- 構造再帰を優先する。
- 測度が見えにくい自動処理（Game State Process、効果解決、戦闘ステップ進行）は、**非再帰の 1 歩関数 `microStep`** と、それを `fuel : Nat` で回す構造再帰 `advance` に分ける。
- 上限が内側で決まる反復（8 ステージ連続効果評価など）は、内側の上限回数による構造再帰とし、外から `fuel` を受け取らない。
- 整礎再帰（`termination_by`）は定義簡約が重いため、`decide` 評価対象には避ける。

### 5.2 状態・不変条件・`SameMeta`

- 状態は素直な `structure` / `inductive` とし、不変条件は別述語（`WF` / `OwnerOk` / `Settled`）で持つ。すべて `Decidable` を付与する。
- 状態の全構成型は `deriving DecidableEq, Repr` が通る形に保つ。
- **[確認済] `SameMeta` の活用**: `GameState` に新しいフィールドを追加したとき既存の `moveObj` 補題が大量に壊れるのを防ぐため、「ゾーン・オブジェクト表・カウンタ以外のメタ状態が変わらない」を単一の述語 `SameMeta` にまとめる。
- [確認済] 複数行の構造体更新 `{ s with a := ..., b := ... }` は続きの行を `{` より深く字下げする。長い場合は `let s1 := ...` に分けて 1 行で書く。

### 5.3 データ構造

- **基本は `List`**（証明補題が最も充実）。
- **検証コア内のマップは `Std.ExtTreeMap` を使う。**
  - [確認済] `Std.ExtTreeMap` は外延的等値性を持ち、structure の `deriving DecidableEq, Repr` が通る。
  - [確認済] `Std.TreeMap` は `deriving DecidableEq` が失敗し、`Std.HashMap` は kernel の `decide` で評価が止まる。
  - [確認済] `Std.ExtTreeMap` の鍵比較で残る `Ordering.eq = compare a k` は `Nat.compare_eq_eq` で等式に直す。
  - `Std.HashMap` は `FabDriver` とテスト補助でのみ使用する。

### 5.4 `deriving` と入れ子帰納型の回避

- 小さな列挙型・レコードは `deriving DecidableEq, Repr, Hashable`（`BEq` は `DecidableEq` から自動導出されるため別途 derive しない）。
- **[確認済] Lean v4.36.0 では `List Effect` や `Option Effect` をフィールドに持つ入れ子帰納型で `deriving DecidableEq` と `induction` が失敗する。**
  - 対策: 効果 IR の再帰型は `mutual` ブロック内に専用のリスト型（例: `EffectList`、`FilterList`）を定義して入れ子を避ける。これにより `deriving DecidableEq` が通る。
- カードを巨大な列挙型のコンストラクタにしない（データ `CardDef` として持つ）。HOAS は使わない。

### 5.5 `Decidable` と `decide +kernel`

- 検証コアでは **`native_decide` 禁止**。
- [確認済] **要素数が数十を超える定理（数百件の `CardDB.WF` や大規模状態の等式など）は、素の `decide` ではなく `decide +kernel` を使う。** `decide +kernel` は kernel で直接評価し、非標準公理を増やさず `lake check` も通る。
- 定理として残したい検査は `decide +kernel`、実行確認のみのテストは `#guard` を使い分ける。

### 5.6 タクティク・v4.36.0 注意点

- [確認済] **`omega` は `abbrev` 型を見通さない。** 算術を扱う定義・定理の引数は `Int` / `Nat` を直接書く（`abbrev Power := Int` のような別名経由で渡さない）。
- [確認済] core には `set`、`push_neg`、`by_contra` が無い（Mathlib のタクティク）。`obtain ⟨x, hx⟩ : ∃ x, x = e := ⟨_, rfl⟩`、`simp only [not_or, Decidable.not_not]`、`by_cases` + `exfalso` で代替する。
- [確認済] 無名 `instance` で `Decidable (x.Valid)` のような短い述語を別モジュールに作ると名前衝突する。必ず `instance GameConfig.decidableValid` のように明示名をつける。
- `simp`、`grind`、`omega` / `lia` を積極的に使い、`erw` は使わない。`maxHeartbeats` を上げる前に証明構造を見直す。

---

## 6. テスト

| 手段 | 用途 |
|---|---|
| `#guard e` / `#guard_msgs` | 定義直後の即時実行検査・エラーメッセージ固定 |
| `example : p := by decide` | 小さな性質の検査（大規模は `decide +kernel`） |
| `FabTest`（`lake test`） | シナリオテスト、公式 Release Notes 裁定の回帰テスト、列挙照合テスト |
| Plausible | ランダム合法手列での `WF` / `OwnerOk` / `Settled` 維持の性質ベーステスト |

- シナリオテスト DSL は、解釈器が指示を飛ばした際の診断イベントが 1 件も出ていないことを常に検査する。
- テスト内で `native_decide` を使う場合は、`Fab` ライブラリの定理から参照しない。

---

## 7. 作業の単位とローカルでの検証

- **1 単位＝1 定義または 1 定理**。単位ごとに以下を繰り返す：
  1. 定義または定理を書く。
  2. 定理なら証明、定義なら `#guard` / `example` を書く。
  3. `lake build Fab.<Module> --wfail` でエラー・警告・`sorry` ゼロを確認。
  4. 通ってから次の単位へ進む。
- ビルドと `git commit` は必ず `&&` で繋ぐ。
- コミット前は全ライブラリビルド＋`lake test`、マージ前は `scripts/verify.sh` を必ず通す：

```bash
# 1. 全ライブラリのビルド（警告・sorry をエラー化）
lake build Fab FabCards FabDriver FabTest --wfail
# 2. テスト実行
lake test
# 3. 公理監査（macOS では --inadvisably-no-sandbox を付与）
lake check --inadvisably-no-sandbox
# 4. カードデータ生成ブロックの陳腐化検査（M3b 以降）
uv run scripts/gen_lean.py --check
# 5. CR/TRP 引用抽出とカバレッジ更新
uv run scripts/cr_citations.py && uv run scripts/coverage.py --check
```

- `lean-beam`（v4.36.0 同梱）で対話的にゴールやタクティクを試してよいが、最終確認は必ずクリーンな `lake build --wfail` で行う。

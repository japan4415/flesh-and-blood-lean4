# Flesh and Blood Lean4 実装方針

本書は、要求の正本である [`docs/original.md`](original.md) を前提にした実装方針である。`original.md` は人間のみが編集する。本書と食い違う場合は `original.md` を優先する。

関連文書:
- [rules-model.md](rules-model.md) — Flesh and Blood Comprehensive Rules の形式化メモ（規則番号・FaB 固有特徴つき）
- [tournament-model.md](tournament-model.md) — Tournament Rules and Policy（TRP）の形式化対象
- [lean-guidelines.md](lean-guidelines.md) — Lean 4 コーディング規約とローカル検証手順
- [card-data.md](card-data.md) — カードデータの取り込み、Name + Pitch 同一性、効果 IR への写像
- [roadmap.md](roadmap.md) — マイルストーン M0〜M10 と、証明を積み上げる順序

---

## 1. 要求の整理

`original.md` の要求を次の 5 つに整理する。

| ID | 要求（original.md） | 設計上の解釈 |
|---|---|---|
| R1 | Lean4 で実装する | 実行可能なルールエンジンと、その性質の形式証明を同一の Lean 4 コードベースに置く |
| R2 | ルールは公式のルールに則る | 公式ルールは Comprehensive Rules（CR）と Tournament Rules and Policy（TRP）の両方とする。各定義から規則番号を辿れるようにし、合法性は CR/TRP から直接書く独立仕様 `Legal` として持つ |
| R3 | 新カードの追加時にその効果を反映できる | カードは「データ＋効果 IR（深い埋め込み）」で表す。エンジンは `CardDB` を受け取り、カード名で分岐しない。定理は `CardDB.WF` を満たす任意の `CardDB` について述べる |
| R4 | 小さいところから証明を積み上げる | ゾーン移動・資源会計などのプリミティブで一度だけ証明し、Combat Chain・プレイ手順・大域不変条件・効果 IR へと積み上げる |
| R5 | 全カードのルールをコード化し、カードでできること全てができる | ①全カードの効果が IR＋Hook で表現でき、②CR 上プレイヤーに許されるすべての選択（ロードアウト、ピッチ、防御組合せ、同時誘発の開始プレイヤー選択、Pitch→Deck 底の並び替え等）を漏れなく合法手として提示する |

R5 の「できること全て」は、次の 2 点の両立と定義する。

1. **表現の完全性**: 全カードの効果がモデル上に存在する（[roadmap.md](roadmap.md) M10 で判定）。
2. **選択の完全性**:
   - **答えの合法性**: エンジンが出した決定要求に対し、CR から直接書いた独立仕様 `Legal` と、構成的な列挙 `legalActions` の一致を定理（I6）で示す。
   - **問いの正しさ**: 正しいプレイヤーに正しい時点で決定要求が出ること。決定点の定理（I16〜I19: 優先権の受け渡し、`Settled` 性、任意の選択の強制質問、同時誘発のターンプレイヤー開始選択）とシナリオテストで担保する。

---

## 2. 前提とするバージョン

| 対象 | 版 | 備考 |
|---|---|---|
| ルール | Flesh and Blood **Comprehensive Rules v2.15.0**（2026-09-28、`rules.fabtcg.com`） | `Fab/Basic/RulesVersion.lean` に固定。規則番号はすべてこの版を基準とする |
| 大会ルール | **Tournament Rules and Policy（TRP）**（2025-05-30 更新、`rules.fabtcg.com`） | フォーマット・ロードアウト・Bo1・時間切れ・ループ（[tournament-model.md](tournament-model.md)） |
| 初期対象フォーマット・セット | **1v1 Classic Constructed（CC）** / **Welcome to Rathe（WTR）** から着手 | 型・手番走査は N 人・全フォーマット対応で作り、実装とカード転記は 1v1 CC・WTR から段階的に拡張する |
| カードデータ | `the-fab-cube/flesh-and-blood-cards`（公式エラッタ反映済み JSON）＋公式カード DB | Name + Pitch でユニークカードを識別（[card-data.md](card-data.md)） |
| Lean | `leanprover/lean4:v4.36.0` | Mathlib なし（core + Std + Plausible）。[lean-guidelines.md §1](lean-guidelines.md#1-ツールチェーン) |

---

## 3. 設計原則

| # | 原則 | 理由 |
|---|---|---|
| P1 | **状態遷移は実行可能な関数 `step` で定義し、合法性は CR/TRP から直接書く独立仕様 `Legal : Prop` として持つ。** `step` の受理判定には `Legal` の決定手続きを使い、`legalActions` との一致を定理で積む（§6.3） | `#eval` で対局を実行でき、`simp` で展開できる。独立仕様 `Legal` と構成的列挙 `legalActions` の一致が R2・R5 の根拠になる |
| P2 | **状態は素直なデータとし、不変条件は別の述語で持つ。** どの中間状態でも成り立つ構造条件 `WF` と、Game State Process（CR 1.10.2）の不動点で成り立つ `Settled` と、所有者整合 `OwnerOk` を分ける（§5.2） | 失敗しうる遷移（`Except`）と相性が良く、カード追加のたびに証明義務を増やさない。一時的に破れる条件（ライフ 0 の Ally 等）を `WF` から切り離せる |
| P3 | **エンジンは個別カードを知らない。** カード名で分岐せず、`GameState.cards : CardDB` から定義を読む。ルールを上書きするカードのための差し込み口（Hook）を最初から用意する | 拡張性（R3）と、カード集合に依存しない汎用定理の成立を両立するため |
| P4 | **プレイヤーの選択はすべて明示的な決定要求にする。** 継続のスタック `pending : List Frame` で管理し、**コアは選択肢が 1 つでも勝手に決めない**（省略や自動化は Driver の責務） | R5（選択の完全性）。ピッチするカード、ピッチをデッキ底へ戻す順、Defend Step の防御選択、同時誘発の開始プレイヤー選択をすべて忠実に表現できる |
| P5 | **乱数をコアに持たない。** シャッフルや先手決定のランダム選択は `Actor.chance` の決定として外から受け取り、`List.Perm` 等の妥当性だけを検査する | `step` が決定的な全域関数となり、「任意のシャッフル結果について成り立つ」を全称量化で証明できる |
| P6 | **ゾーン移動は単一のプリミティブ `moveObj` に集約する。** Arena 内の同一性維持移動と、Non-Arena 境界跨ぎの新規 `ObjId` 払い出し（CR 3.0.9）を 1 か所で制御する | 物理カード保存（I1）・位置の一意性（I2）・所有者整合（`OwnerOk`）・LKI 取得を一度だけ証明すれば全効果に波及する |
| P7 | **規則番号を辿れるようにする。** 公開宣言の docstring に `(CR 7.6.2)` / `(TRP ...)` の形式で根拠を書く | 公式ルール準拠（R2）の監査と、CR マイナー改訂時の影響範囲抽出を機械化するため |
| P8 | **検証コア（`Fab`）に `partial` / `unsafe` / `native_decide` / `sorry` を入れない。** `lake check` で標準 3 公理以外を監査する | `partial` は kernel から不透明で証明できず、`native_decide` はコンパイラを信頼境界に含めてしまうため |
| P9 | **盤面の変更はすべてイベント経路 `perform` を通す**（提案 → 4 区分置換・防止 → 適用 → 発行 → Outcome 置換。§6.6） | FaB の置換効果は Self/Identity・Standard・Prevention・Outcome の 4 段階（CR 6.4-6.5）を持つ。経路を最初から用意しないと後から全プリミティブの補題を書き直す羽目になる |

---

## 4. 全体構成

```text
 カードデータ（the-fab-cube/flesh-and-blood-cards 等）
        │  scripts/（uv + Python）: 取得・正規化・Lean 生成
        ▼
 FabCards（ライブラリ）: 1 弾 1 ファイルの CardDef と具体的な CardDB
        │ CardDB を初期状態に渡す（Fab 側は FabCards を import しない）
        ▼
 Fab（検証コア）
   Core ─→ Card ─→ State ─→ Rules ─→ Spec ─→ Engine ─→ Invariant
   基本型   効果IR   状態・    手続き・  Legal     step /        WF 保存・
            CardDef  ChainLink 1歩解釈器 （CR から  legalActions  一致定理・
            CardDB   フレーム  8ステージ 直接書く） / view        Reachable
 FabDriver（ライブラリ）: 乱数供給、自動対戦、トレース出力（IO を使う。監査対象外）
 FabTest: シナリオ・公式 Release Notes 回帰・性質ベーステスト（Plausible）
```

循環 import を避けるため、層の依存順序を厳密に固定する。

1. `Core`: ID、Supertype（Class / Talent / Generic）、CardType / Subtype、ColorStrip、Pitch、Cost（Resource / Chi / AP / Life）、Keyword、Format / Mode
2. `Card`: 効果 IR（`Syntax`、`Value`、`Env`、`Ability`）、`CardDef`、`CardDB`（`CardDB.WF`）。**この層は `GameState` を参照しない**
3. `State`: `Object`（Card / Token / Layer / AttackProxy）、`LkiSnapshot`、`Zone`、`CombatChain` / `ChainLink`、`AssetPool`、`Event`、`Frame` / `Action`、`GameConfig`、`GameState`、`WF` / `Settled` / `OwnerOk`
4. `Rules`: `moveObj`、`perform`（4 区分置換）、`characteristics`（8 ステージ連続効果）、ゲームアクション、Deck / Loadout / Setup、Turn / EndPhase、GameStateProcess、Stack / Play（9 手順＋巻き戻し）、Combat（7 ステップ）、`microStep`
5. `Spec`: 独立仕様 `Legal`（状態の読み出し、`characteristics`、Hook 導出関数のみを参照）
6. `Engine`: `step`、`legalActions`、`view`
7. `Invariant`: `WF` / `OwnerOk` / `Settled` 保存、一致定理 I6、`Reachable`、停止性 I12、非干渉 I10

### 4.1 ディレクトリ構成（案）

CR の章立てとモジュールを対応させ、規則番号から実装を引けるようにする。

```text
lean-toolchain                 -- leanprover/lean4:v4.36.0
lakefile.toml
Fab.lean                       -- ルート
Fab/
  Basic/
    ListLemmas.lean            -- List.Perm / Nodup 等の汎用補題
    RulesVersion.lean          -- 基準 CR / TRP の版番号と公開日
  Core/
    Ids.lean                   -- PlayerId / ObjId / PhysId / CardId / Timestamp / LinkId
    Supertype.lean             -- Class / Talent / Generic（CR 2.11）
    CardType.lean              -- CardType / Subtype（CR 2.10, 2.12）
    Property.lean              -- ColorStrip / Pitch / Numeric（CR 2.2-2.8）
    Cost.lean                  -- AssetCost（AP / Resource / Chi / Life）と EffectCost（CR 1.14）
    Keyword.lean               -- Keyword / KeywordInst（CR 8.1-8.3）
    Mode.lean                  -- Duel / UPF などのモード設定
  Card/
    IR/                        -- Basic, Value, Expr, Prim, Effect, Ability, Check, Build
    CardDef.lean               -- 論理カード定義（両面・分割 Meld 用の面構造を含む）
    CardDB.lean                -- CardDB と CardDB.WF（GameState を参照しない）
  State/
    Object.lean                -- Card / Token / Layer / AttackProxy、タップ・裏向き・カウンター・Evo 下層
    Lki.lean                   -- Last Known Information スナップショット（CR 1.2.3）
    Zone.lean                  -- Arena（Hero/Soul/Equip/Weapon/Permanent/CombatChain）と Non-Arena（CR 3）
    Combat.lean                -- CombatChain / ChainLink / CombatStep（CR 3.5, 7）
    Pool.lean                  -- プレイヤー資産（AP / Resource / Chi）と Hero ライフ
    Event.lean                 -- イベント（提案・置換・適用・発行・結果置換）
    Decision.lean              -- Actor / Action / Frame（決定フレーム・作業フレーム）
    GameConfig.lean            -- RuleSet / Format / Mode / BanList と GameConfig.Valid
    GameState.lean
    WF.lean                    -- WF / Settled / OwnerOk
  Rules/
    Move.lean                  -- 唯一のゾーン移動プリミティブ moveObj（Arena 内維持 / 境界跨ぎ新規 ObjId）
    Perform.lean               -- イベント経路 perform（4 区分置換・防止: CR 6.4-6.5）
    Characteristics.lean       -- 8 ステージ連続効果（CR 6.3.2-6.3.3）
    Actions/*.lean             -- Draw, Pitch, Discard, Banish, Destroy, Damage(Physical/Arcane), Opt, Intimidate, Charge, CreateToken, Tap, Transcend ...
    Interp.lean                -- 効果 1 歩解釈器 microStep（再帰なし）
    Deck.lean                  -- デッキ・Card-Pool・Loadout 合法性（CR 1.1, 4.1.4）
    Setup.lean                 -- Start-of-Game Procedure（Hero 公開 → 先手 → Loadout → 公開・シャッフル → Intellect ドロー: CR 4.1）
    Turn.lean                  -- Start / Action / End Phase（Turn 0 両者ドロー・Pitch→Deck 底: CR 4.2-4.4）
    GameStateProcess.lean      -- Game State Process（1.10.2: 敗北判定・クリア・誘発積み）
    Stack.lean                 -- Stack / 優先権 / レイヤー解決（CR 1.11, 5.3）
    Play.lean                  -- カードプレイ 9 手順と巻き戻し（CR 5.1-5.2）
    Trigger.lean               -- 誘発検出とターンプレイヤー開始選択の積み順（CR 6.6.6b）
    Combat.lean                -- Combat Chain 7 ステップ（CR 7.1-7.7）と Attack-Proxy / 装備摩耗
  Spec/
    Legal.lean                 -- 独立仕様 Legal（フレーム種別ごとに CR/TRP から直接記述）
    Combat.lean                -- 戦闘ダメージ・防御制約の関係仕様（L5）
    Stages.lean                -- 8 ステージ連続効果の関係仕様（L5）
  Engine/
    Step.lean                  -- microStep / advance / step
    LegalActions.lean          -- 構成的な合法手列挙
    View.lean                  -- プレイヤーごとの公開・非公開情報射影（Pitch 戻し順の秘匿を含む）
  Invariant/                   -- WF / OwnerOk / Settled / PhysIds / Resources / Combat / Turn / Progress / Termination / NonInterference
  Tournament/
    Format.lean                -- CC / Blitz / LL / Sealed / Draft / Commoner / UPF
    DeckLegality.lean          -- フォーマット別デッキ合法性（I13）
    TimeLimit.lean             -- 時間切れ（現行＋1 ターン: I14）
    Loop.lean                  -- ジャッジによるループ引き分け
    LoopDetect.lean            -- 強制ループ検出器（I19）
    Match.lean                 -- Bo1 / Top Cut マッチ進行
FabCards/
  WTR.lean  ARC.lean  CRU.lean ... -- 1 弾 1 ファイル（card-data.md §4）
  Tokens.lean                  -- 全トークン定義
  Registry.lean                -- 具体的な CardDB
FabDriver/                     -- 乱数供給・自動対戦・トレース出力（IO 可、監査対象外）
FabTest/                       -- Scenario / ReleaseNotes / Property（Plausible）
scripts/                       -- fetch.py, normalize.py, gen_lean.py, coverage.py, cr_citations.py, verify.sh
```

---

## 5. データモデル（FaB 固有の設計）

### 5.1 識別子

| 識別子 | 意味 | FaB 固有の根拠 |
|---|---|---|
| `PlayerId` | 席（手番順） | 1v1 および N 人（UPF）に対応 |
| `PhysId` | 物理カード（Card-Pool の 1 枚ずつ） | トークン・Layer・AttackProxy は `PhysId` を持たない。物理カード保存（I1）の単位 |
| `ObjId` | ゲームオブジェクトのインスタンス | **Arena 境界を跨ぐ移動、または Non-Arena 間の移動で新規払い出し**（CR 3.0.9）。**Arena 内移動（装備→Combat Chain→装備、武器→Chain Link→Weapon）では維持**する |
| `CardId` | 論理カード（**Name + Pitch 単位**） | 赤・黄・青は別々の `CardId` を持つ（CR 2.6, 2.8）。`name : String` フィールドを別に持ち、Legendary やカード名指定は `name` で判定する |
| `LinkId` | Combat Chain 上の Chain Link 番号（1, 2, ...） | Combo（前リンク参照）や複数リンクにまたがる効果参照のため |
| `Timestamp` | 継続効果・オブジェクト生成の論理時刻 | `nextTimestamp` から単調増加で払い出す（CR 6.3.3） |

### 5.2 オブジェクト構造（両面・分割・Evo・Attack-Proxy・LKI）

FaB 特有のカード形態を後から破綻させないため、`CardDef` と `Object` に最初から最小限の表現枠を持たせる。

- **カードの面（`CardFace`）**:
  - 通常の単面カードは `front` のみ。
  - **両面カード（Transcend / Transform / Demi-Hero 等）**: `back : Option CardFace` を持ち、`Object.faceState : FaceState`（`.front` / `.back`）で現在有効な面を表す。
  - **分割カード（Meld: CR 8.3.38）**: `splitRight : Option CardFace` を持ち、Meld プレイ時は両面の特性を合成した状態でスタックに載る。
- **`ObjectKind`**:
  - `card (phys : PhysId) (cardId : CardId)`
  - `token (cardId : CardId)`
  - `layer (sourceObj : ObjId) (sourceLki : LkiSnapshot) (abilityIdx : Nat) (isTrigger : Bool)`
  - `attackProxy (sourceObj : ObjId) (sourceLki : LkiSnapshot)` — 武器・アライ等の攻撃を表現（CR 1.4.3）
- **オブジェクトの状態フィールド**:
  - `owner : PlayerId`、`baseController : PlayerId`
  - `tapped : Bool`（CR 8.2 / Tap・Untap）、`faceDown : Bool`（Cloaked 装備、裏向き Arsenal、裏向き Banished）
  - `faceState : FaceState`（表面 / 裏面）
  - `counters : Std.ExtTreeMap CounterKind Int`（`-1{d}`, `+1{p}`, steam, aim, flow, verse 等）
  - `underCards : List ObjId`（**Evo** で下敷きになった装備や **Hero の Soul**。ただし Soul は専用サブゾーン `Zone.soul p` として持ち、`moveObj` で管理する方が保存則 I1 の証明が簡潔になる。Evo 下層も装備スロットのスタック `List ObjId` の末尾として表現する）
  - `timestamp : Timestamp`
- **Last Known Information（`LkiSnapshot`）**:
  - オブジェクトがゾーン移動・消滅する直前の導出済み `Characteristics`、カウンター、コントローラー、型・名前・キーワードを保持する不変データ（CR 1.2.3）。
  - `ChainLink` に `attackLki : Option LkiSnapshot` を保持することで、*Endless Arrow* が手札に戻ったり武器が次のリンクへ移動しても、Chain Link 上の Go Again や攻撃値・名前を正確に参照できる（CR 3.5.4b）。

### 5.3 ゾーンと不変条件（`WF` / `Settled` / `OwnerOk`）

- **全ゾーンの中身は `List ObjId` を真実の源とする。**
  - 装備スロット（Head / Chest / Arms / Legs）も `List ObjId` とし、先頭を現在の表層装備、後続を Evo で下に敷かれた装備とする（通常は長さ 0 または 1）。
  - Combat Chain は `CombatChain` 構造体内に `links : List ChainLink` を持ち、各 `ChainLink` が `attack : Option ObjId`、`attackSource : Option ObjId`、`defending : List ObjId`、`target : AttackTarget`、`hit : Bool`、`attackLki : Option LkiSnapshot` 等を持つ。
  - **注意（位置の一意性 I2）**: 武器が攻撃して Chain Link に載るとき、武器オブジェクトは Weapon ゾーンから `ChainLink.attackSource` へ論理移動する（Close Step で Weapon ゾーンへ戻す）。同様に防御した装備は Equipment ゾーンから `ChainLink.defending` へ論理移動し、Close Step で装備ゾーンへ戻す。これにより「各 `ObjId` は常にちょうど 1 つの場所にある（`Nodup`）」を破らずに、かつ `moveObj` の Arena 内移動モードで同一 `ObjId` とカウンターを維持できる！
- **オブジェクト表**: `Std.ExtTreeMap ObjId Object`（外延的等値性・`DecidableEq`・`decide +kernel` の相性による。[lean-guidelines.md §5.3](lean-guidelines.md#53-データ構造)）。
- **不変条件の 3 分割**:
  1. **`WF`（構造条件）**: どの中間状態・`microStep` でも保存。
     - 全ゾーン（Combat Chain の全リンク内オブジェクト・Inventory 含む）の `ObjId` 列の連結が `Nodup`
     - `objects` 表の定義域が全ゾーンの `ObjId` 集合と一致
     - 全 `ObjId < nextId`、全 `Timestamp < nextTimestamp`
  2. **`OwnerOk`（所有者整合）**: Non-Arena ゾーン（Deck / Hand / Arsenal / Pitch / Graveyard / Banished / Inventory）にある全オブジェクトの `owner` はそのゾーンの持ち主と一致する。
  3. **`Settled`（Game State Process 不動点条件）**: `priority` フレームが先頭にある到達可能状態で成り立つ（I17）。
     - 勝敗が決していないなら、生存プレイヤーの Hero ライフ > 0（CR 1.10.2a）
     - ライフ 0 以下の Ally / Living Card が Arena に残っていない（CR 1.10.2b）
     - 保留中の Triggered-layer が空である（CR 1.10.2d）
     - Non-Arena に Token や Attack-Proxy が残っていない

### 5.4 特性の導出（8 ステージ制: CR 6.3）

- 実効特性は `characteristics : GameState → ObjId → Characteristics` で毎回導出する（`GameState.cards` から `CardDB` を読む）。
- 全オブジェクトに対して Stage 1 → Stage 2 → … → Stage 8 を順に適用する。
- 同一ステージ内では、まず **サブステージ順** と **Timestamp 順** で実装し、依存関係（Dependency: CR 6.3.3）が必要なカードが出た時点（M6）で依存グラフのトポロジカル順（循環時は Timestamp へフォールバック）を実装し、L5 関係仕様で検証する。
- 継続効果の保持:
  - 盤面上の静的能力（Static Ability）はオブジェクトから動的に収集（Timestamp はオブジェクトのもの）。
  - 期間付き継続効果（`thisTurn`、`thisCombatChain`、`thisChainLink`、`nextAttack`、`permanent` 等）は `GameState.continuousEffects : List ContinuousEffectInst` として持ち、該当期間終了時に一括失効させる。

---

## 6. エンジンの形

### 6.1 中核 API

```lean
/-- どのルール体系で遊ぶか。 -/
inductive RuleSet where
  | coreOnly
  | tournament (stage : TournamentStage) -- swiss / topCut

/-- 対局の固定設定（GameState.config に入れ、対局中は変えない）。 -/
structure GameConfig where
  ruleSet : RuleSet
  format  : Format                       -- cc / blitz / livingLegend / sealed / draft / commoner / upf
  mode    : Mode                         -- duel / upf
  banList : FormatBanList

inductive GameResult where
  | won  (winners : List PlayerId)
  | draw (reason : DrawReason)           -- simultaneousHeroDeath / timeLimit / loop / agreed

inductive RuleError where
  | illegal (reason : IllegalReason)
  | fuelExhausted
  | internal (msg : String)              -- WF ∧ OwnerOk ∧ CardDB.WF の下では発生しないことを証明（I4）

/-- 現在の決定要求に対するプレイヤーの合法手をすべて列挙する（偶然・時計・ジャッジを除く）。 -/
def legalActions (s : GameState) : List Action
/-- 自動処理を 1 歩だけ進める（非再帰）。 -/
def microStep (s : GameState) : Except RuleError (GameState × List Event)
/-- 決定を 1 つ受理し、次の決定点または終局まで fuel の範囲で進める。 -/
def step (fuel : Nat) (s : GameState) (a : Action) :
    Except RuleError (GameState × List Event)
/-- プレイヤー p から見える情報への射影（Pitch 戻し順・手札・裏向きカード・山札を秘匿）。 -/
def view (p : PlayerId) (s : GameState) : PlayerView
```

- **`CardDB` は `GameState.cards` に格納する**: `riftbound-lean4` の実装経験から、`CardDB` を全関数の引数に引き回す代わりに `GameState.initial` で不変フィールドとして格納する（`SameMeta` が変更しないことを保証）。定理は `CardDB.WF s.cards` を仮定して任意のカード集合について述べる。
- **fuel の単調性（I15）**: `step` は `advance` を `fuel : Nat` の構造再帰で回す。「ある `fuel` で `.ok r` なら、それ以上の任意の `fuel` でも同じ `.ok r`」を M2 で即座に証明する。

### 6.2 決定要求と継続スタック（FaB 固有フレーム）

`pending : List Frame` は **決定フレーム**（入力待ち）と **作業フレーム**（`microStep` が進める）の 2 種からなる。フレームには盤面の古い写しを持たせず、問い（と分割選択の途中結果）だけを持つ。

FaB 固有の主要フレーム:

| フレーム | 種別 | 内容（CR 根拠） |
|---|---|---|
| `chanceFirstPlayer` / `chanceShuffle p` | 偶然決定 | 先手選択権のランダム決定、デッキシャッフル（4.1.3, 4.1.5） |
| `chooseFirstPlayer p` | 決定 | 先手・後手の選択（4.1.3） |
| `chooseLoadout p step` | 決定 | 試合前ロードアウト: Inventory から Head/Chest/Arms/Legs/Weapon を選び、残りを Deck と Inventory に分ける分割選択（4.1.4） |
| `priority p passCount` | 決定 | 優先権: タイミングに合うカードのプレイ、能力起動、パス（1.11, 4.3, 7.1-7.6） |
| `playProc state` | 作業 | カードプレイ 9 手順（5.1.1）の進行＋巻き戻し用スナップショット |
| `choosePitch p needed` | 決定 | 資産コスト支払い時のピッチ選択（オーバーピッチ禁止 1.14.3b、Chi / Resource 充当を 1 枚ずつ選択） |
| `defendPick p` | 決定 | Defend Step（7.3）で手札・装備から防御カードを 1 枚ずつ選ぶ分割選択（完了で同時に防御宣言として適用）。Dominate / Overpower 制約を各段で検査 |
| `chooseTriggerStart tp` / `chooseTriggerOrder p` | 決定 | 同時誘発の開始プレイヤーをターンプレイヤーが選び（6.6.6b）、時計回りに各自の誘発順序を 1 つずつ選択 |
| `chooseReplacement p stage` | 決定 | 同一置換区分で競合する置換効果の適用順選択（6.5.1） |
| `chooseArsenal p` | 決定 | End Phase（4.4.3b）に手札から 1 枚を空の Arsenal へ置くか置かないかの選択 |
| `choosePitchOrder p` | 決定 | End Phase（4.4.3c）に Pitch Zone のカードを Deck の底へ置く順序を 1 枚ずつ選ぶ分割選択（相手には非公開） |
| `choose` | 決定 | モード・対象・X・任意追加コスト・"may"・Opt の上下配置・Damage Prevention 選択など |
| `combatStep step` / `closeChain` | 作業 | Combat Chain 7 ステップ遷移（7.1-7.7）および Close Step の装備摩耗・カード回収 |
| `gameStateProcess` | 作業 | CR 1.10.2 の評価と誘発積み込みの挿入 |
| `endTurnProc` | 作業 | End Phase 4.4.3 の一連の手順（Turn 0 両者ドロー含む） |
| `run p src env todo` | 作業 | 効果 IR の 1 歩解釈の継続 |

> **決定の粒度**: Defend Step の防御組合せ、Loadout の装備・デッキ編成、Pitch→Deck 底の順列、同時誘発の順序など組合せ爆発する選択は、すべて「次の 1 つを選ぶ／完了する」分割選択フレームの列にする。列の途中では Game State Process も誘発も走らせず、完了時に 1 つの同時イベントとして確定する。

### 6.3 独立仕様 `Legal` と I6

- `def Legal (s : GameState) (a : Action) : Prop` をフレーム種別ごとに CR / TRP から直接書き、`Decidable` インスタンスを与える。
- `step` は受理判定に `decide (Legal s a)` を使用する。
- 目標定理（I6: `WF s ∧ OwnerOk s ∧ CardDB.WF s.cards` の下）:
  - **健全性**: `Legal s a → ∀ e, step fuel s a = .error e → e = .fuelExhausted`
  - **完全性**: `(∃ r, step fuel s a = .ok r) → Legal s a`
  - **列挙の一致**: `a ∈ legalActions s ↔ Legal s a ∧ a.actor.isPlayer`
- `legalActions` は構成的に列挙し、`step` の試し打ちフィルタリングで定義してはならない（テスト照合先としてのみ使用可）。

### 6.4 乱数・隠れ情報

- 乱数は `Actor.chance` の決定（順列 `List.Perm` 等）で外から供給し、コアは完全に決定的とする。
- `view p s` はプレイヤー `p` に見えない情報（相手の Hand、裏向き Arsenal / Banished / Cloaked 装備、Deck の順序、**相手が End Phase に Deck 底へ戻した Pitch の順序**、見えないオブジェクトの `ObjId`）を秘匿する。
- 後期定理（I10）: プレイヤー `p` の合法手は `view p s` のみに依存する（`ObjId` の付け替え同型のもとで）。

### 6.5 イベント経路 `perform`（CR 6.4-6.5 の 4 区分置換）

盤面を変える全操作は以下の 5 段パイプラインを通る：

1. **提案（Propose）**: `Event` データを生成（例: `dealDamage src target .arcane 3`、`moveCard obj dest`、`drawCard p`）。
2. **置換・防止（Replace & Prevent）**: 適用可能な置換効果を次の厳密な順で適用（1 イベントに同一置換は高々 1 回）：
   - `Stage A`: Self-replacement & Identity-replacement
   - `Stage B`: Standard-replacement
   - `Stage C`: Prevention（物理／秘術ダメージ防止、Ward、Arcane Barrier、Spellvoid、Quell、Shielding prevention）
   - 同区分内で複数競合すれば `chooseReplacement` フレームで当事者が順序を選ぶ。
3. **適用（Apply）**: 確定イベントを盤面に反映（移動は必ず `moveObj` を経由）。
4. **結果置換（Outcome-Replace）**: イベント結果（例: Clash 敗北、Hit 等）に対する Outcome-replacement（6.4.10e）があれば適用。
5. **発行（Emit）**: 確定イベントを `List Event` に記録し、誘発能力（6.6）の検出に渡す。

プリミティブの補題（L1）は「適用」の段に対して証明するため、M6 でカードの置換効果が増えても既存の補題を壊さない。

---

## 7. 効果 IR（深い埋め込み）と Hook

### 7.1 方針

- カード効果は閉じた帰納型の IR で表し、単一の 1 歩解釈器 `microStep` が全カードを実行する。
- **カード固有のコンストラクタは作らない。** CR の語彙（アクション・結合子・キーワード）のみを IR に置く。
- **入れ子帰納型を避ける**: Lean v4.36.0 では `List Effect` / `Option Effect` を直接持つ帰納型で `deriving DecidableEq` と `induction` が使えない（[lean-guidelines.md §5.4](lean-guidelines.md#54-deriving-と等値性)）。`mutual` ブロック内に専用リスト型を定義して `DecidableEq` を自動導出する。
- **`custom` 逃げ道**: 極めて特殊な効果のみ `Effect.custom (id : CustomId) (args : List Arg)` を許し、ハンドラは `CardDB` 内に `List Value → Effect` として持つ（`GameState` を受け取らず、展開は 1 段限り）。同じ形が 3 枚を超えたら IR に昇格する。
- **解釈器の全域性**: 未束縛変数や型不一致は `RuleError.internal` にせず「実行不可能な指示（CR 1.0.1b）」としてスキップ＋診断イベント発行にする。これにより I3（`WF` 保存）と I4（内部エラーなし）がハンドラの中身に依らず成り立つ。

### 7.2 IR の主要語彙（FaB 特化）

| 要素 | 内容 |
|---|---|
| **結合子（`Effect`）** | `nop`、`seq`、`chooseOne`、`ifThen`、`forEach`、`may`、`repeatN`、`bind`、`prim`、`grant`（継続効果付与）、`delayed`（遅延誘発）、`replaceNext` / `preventNext`、`custom` |
| **プリミティブ（`Prim`）** | `draw`、`discard`、`pitch`、`dealDamage (kind : DamageKind)`（Physical / Arcane）、`gainLife`、`loseLife`、`gainAP`、`gainResource`、`gainChi`、`banish (faceDown : Bool)`、`destroy`、`putInArsenal`、`putOnDeck (top/bottom)`、`putInSoul`、`opt`、`intimidate`、`charge`、`boost`、`createToken`、`addCounter`、`removeCounter`、`tap`、`untap`、`turnFaceUp`、`turnFaceDown`、`transcend`、`transform`、`clash`、`closeCombatChain`、`preventDamage`、`copyLayer`、`takeControl` |
| **選択宣言（`EffectDef`）** | プレイ時（5.1.2-5.1.3）に宣言するモード・対象枠・X・任意追加コストを本体から分離して宣言。本体からは `.slot i` で参照 |
| **フィルタ・参照（`Selector` / `Condition`）** | Zone（Arena/Hand/Arsenal/Pitch/Graveyard/Banished/Soul/CombatChain）、CardType/Subtype/Supertype、ColorStrip、Pitch、Power/Defense 比較、**Chain Link 履歴参照**（前リンクのカード名・Combo、今チェインの攻撃回数、防御カード有無・Reprise、ヒット有無・Crush、手札からプレイしたか、Arsenal からプレイしたか） |
| **誘発（`Trigger`）** | `onPlay`、`onAttack`、`onDefend`、`onHit`、`onDealDamage`、`onChainClose`、`onEnterArena`、`onLeaveArena`、`onDestroy`、`onBanish`、`onPitch`、`onDraw`、`onDiscard`、`onStartOfTurn`、`onEndPhaseBegin`、`onStateCondition`（Phantasm / Spectra 等の状態・条件誘発） |
| **期間（`Duration`）** | `thisChainLink`、`thisCombatChain`、`thisTurn`、`untilNextTurn`、`whileSourceInArena`、`permanent` |

### 7.3 ルールの差し込み口（Hook）

CR 1.0.1（カード優先・Can't beats Can）を実現する導出関数を最初から定義する（初期は空リストを返すスタブ）：

| Hook | FaB での具体例 |
|---|---|
| **防御制約** | Dominate（手札 1 枚まで）、Overpower（Action 1 枚まで）、Defense Reaction 禁止、装備防御禁止、防御値変更 |
| **プレイ許可・禁止** | Banished からのプレイ（Chane / Levia / Blood Debt）、Graveyard からのプレイ、Arsenal 追加スロット、Action を Instant タイミングでプレイ可能、コスト増減・代替コスト |
| **コスト計算・支払い** | 資産コストの置換・増減・下限、Chi 充当規則、追加コスト（Fusion / Boost / Discard / Banish 等） |
| **攻撃対象許可** | Spectra（オーラを攻撃可能）、Ally（アライを攻撃可能）、特定対象への攻撃禁止 |
| **ダメージ・ヒット置換** | Arcane Barrier / Spellvoid / Quell / Ward / Shielding Prevention、ダメージ倍化・置換、On-hit 抑止 |
| **Combat Chain 終了処理** | Battleworn / Temper / Blade Break / Guardwell、チェイン閉じ時の特殊回収先（Soul へ置く等） |
| **デッキ・ロードアウト** | 武器スロット変更（2H 武器・片手 2 刀・Off-Hand 等）、ヒーロー固有の開始時アリーナ配置（Evo / Companion 等） |

---

## 8. 証明を積み上げる方針

詳細は [roadmap.md](roadmap.md) を参照。証明は次の 7 層で下から積む。

| 層 | 内容 | FaB での代表例 |
|---|---|---|
| **L0 データ** | 判定可能性、コスト・ピッチ算術、デッキ・ロードアウト合法性 | 資産コスト計算の非負性、Class/Talent 適合、CC/Blitz 構築と Loadout の包含（I13） |
| **L1 プリミティブ** | `moveObj`、資産プール、ドロー・ピッチ・ダメージ適用 | 物理カード保存（I1: `List.Perm`）、位置一意性（I2）、Arena 内移動の `ObjId` 維持、AP/Resource/Chi 会計（I8） |
| **L2 手続き** | Start-of-Game、ターン 3 フェイズ、End Phase、Combat Chain 7 ステップ、Stack LIFO、Game State Process | 7 ステップの遷移順、Resolution Step での Go Again +1 AP、Close Step の装備復帰、Turn 0 両者ドロー、同時誘発のターンプレイヤー開始選択、時間切れ終了（I14）、GSP 停止（I12a） |
| **L3 大域** | `Reachable` 上の `WF` / `OwnerOk`、I4（内部エラーなし）、I5（進行性）、I6（`Legal` 一致）、I15（fuel 単調性） | 任意の到達可能状態でルール不整合が起きず、常に合法手が存在する |
| **L4 効果 IR** | `microStep` が任意の `Effect` で `WF` / `OwnerOk` を保存、任意選択の強制質問（I18） | IR で記述された全カードが自動的に構造不変条件を保つ（カード単位の証明義務をほぼゼロにする） |
| **L5 関係仕様** | 複雑な計算規則の独立仕様との一致 | 8 ステージ連続効果（CR 6.3）、4 区分置換効果（CR 6.4-6.5）、戦闘ダメージ計算（CR 7.5）、資産コスト計算（CR 5.1.5） |
| **L6 情報** | 隠れ情報の非干渉（I10）、`ObjId` 同型 | Pitch のデッキ底配置順や相手手札が合法手に漏れない |

---

## 9. ルールとカードの版管理

- `Fab/Basic/RulesVersion.lean` に CR と TRP の基準版番号・日付を定数として保持する。
- 規則引用はすべて `(CR x.y.z)` / `(TRP x.y)` 形式に統一し、`scripts/cr_citations.py` で機械抽出してカバレッジと改訂影響を追跡する。
- 新セット発売で CR が更新されたら、変更差分を確認し、規則番号・`Legal`・回帰テスト（Release Notes 由来）を順に更新する。
- カードは印刷文面ではなく **最新公式エラッタ適用後の現行文面** を `CardDef` の正とし、エラッタ出典を記録する。

---

## 10. カードデータと権利（法的助言ではない）

詳細は [card-data.md §10](card-data.md#10-権利面の注意法的助言ではない) を参照。

- コードのライセンスは Apache-2.0（予定）とし、カード名・カードテキスト・ルール文書は **Legend Story Studios（LSS）** の知的財産でありコードライセンスの対象外であることを `NOTICE` に明記する。
- LSS の **Terms of Use for Game and Studio Assets and IP** に従い、非商用・無料の研究／形式化プロジェクトとして運用し、`README.md` に公式非提携の免責文と `© Legend Story Studios` 表記を置く。
- カードアート画像やフレーバーテキストはリポジトリに含めない。

---

## 11. テストと検証

- **1 単位＝1 定義または 1 定理**: 単位ごとに `lake build <Module> --wfail` を通し、`sorry` を残したまま次へ進まない（[lean-guidelines.md §7](lean-guidelines.md#7-作業の単位とローカルでの検証)）。
- **テスト階層**:
  - 定義直後の `#guard` / `decide`（大規模データは `decide +kernel`）
  - シナリオテスト（`FabTest/Scenario`: 状態構築 → Action 列 → 結果検証＋診断イベント不在検査）
  - 公式 Release Notes / 裁定の回帰テスト（`FabTest/ReleaseNotes`: Phantasm、Endless Arrow LKI、Arcane Barrier vs Ward、Chi 支払い、同時誘発順、Turn 0 ドロー等）
  - Plausible による性質ベーステスト（ランダム合法手列での `WF` / `OwnerOk` / `Settled` 維持）
  - 列挙照合テスト（小状態で `legalActions` と `step` 試し打ちを比較）
- **ローカル一括検証**: `scripts/verify.sh`（全ライブラリ `--wfail` ビルド → `lake test` → `lake check --inadvisably-no-sandbox` による公理監査 → `gen_lean.py --check` → CR 引用・カバレッジ更新）をコミット・マージ前の関所とする。

---

## 12. 決定事項（2026-11-24）

| # | 論点 | 決定 |
|---|---|---|
| D1 | Mathlib を入れるか | **入れない**（core + Std + Plausible）。ビルド速度・メモリ・実行可能性を優先 |
| D2 | 初期スコープを 1v1 に絞るか | **絞る（1v1 Classic Constructed）**。型と手番走査は最初から N 人対応にし、UPF 固有規則は M9 で追加 |
| D3 | カード定義のファイル分割 | **1 弾 1 ファイル**（`FabCards/<Set>.lean`）＋生成ブロック／手書き部分の分離 |
| D4 | `CardDB` の渡し方 | **`GameState.cards` に不変フィールドとして格納**（引数引き回しを避け証明の簡潔さを維持） |
| D5 | 検証の実行場所 | **ローカル検証**（`scripts/verify.sh`）を基本とし、単位ごとにビルド＆証明確認 |
| Q1 | カード名・公式文面・スナップショットを公開リポジトリにコミットするか | **コミットする。** 1 弾 1 ファイルとし、各カードの定義の docstring に公式英語文面を入れる。LSS の Terms of Use に準拠した免責文と `NOTICE` を必須とする（§10） |
| Q2 | 最初の基準フォーマット・対象セット | **1v1 Classic Constructed（CC）** と **Welcome to Rathe（WTR）のみ** から着手し、段階的に他セット・他フォーマットへ広げる |
| Q3 | 基準 CR バージョン | **`rules.fabtcg.com` の現行最新確定版（CR v2.15.0 / 2026-09-28、TRP 2025-05-30）** を `Fab/Basic/RulesVersion.lean` に固定する |

---

## 13. リスクと対策

| リスク | 対策 |
|---|---|
| **FaB のカード総数が多い**（初期〜最新で数千種、さらに赤/黄/青の色違い） | 論理カードは Name + Pitch だが、赤/黄/青で数値のみ異なるカードは IR 構築ヘルパ（例: `vanillaAttack`、色別パラメータ関数）で重複記述を劇的に減らし、`transcribe.py` と段階的転記で進める |
| **Combat Chain＋LKI＋Attack-Proxy の複雑さ** | M2〜M5 でバニラカード・基本武器の 7 ステップと LKI を先に単体証明してから能力システム（M6）を載せる |
| **8 ステージ連続効果の依存関係と循環** | 初期はステージ＋サブステージ＋Timestamp 順で実装し、依存が必要なカードでトポロジカル評価＋L5 関係仕様を追加 |
| **4 区分置換効果とダメージ防止の競合** | `perform` 経路を M2 から 4 区分構造で用意し、M6 で置換効果を差し込む。L1 補題は適用段に分離 |
| **Defend Step や Loadout の組合せ爆発** | すべて「1 枚選ぶ／完了」の分割選択フレームにし、`legalActions` の爆発と探索の破綻を防ぐ |
| **オーバーピッチ禁止と可変コストの支払い検証** | 資産支払いフレームで「残額 > 0 のときのみピッチ可」を明示的に不変条件化し、巻き戻しスナップショットと併用する |
| **証明コストの膨張** | 証明をプリミティブ・手続き・解釈器に集約し、カード個別の証明義務をゼロに近づける。`SameMeta` で状態拡張時の補題破損を抑える |
| **IR 設計の手戻り** | 解釈器実装前の **M3b** で実カード（WTR 基本セット＋難しいカード群）を構文転記し、不足語彙・Hook を洗い出してから M4 に進む |

# ロードマップ: 証明を積み上げる順序

[`original.md`](original.md) の「小さいところから証明を積み上げて実装を行う」をマイルストーンの列に落とし込んだもの。全体設計は [design.md](design.md)、ルール用語は [rules-model.md](rules-model.md)、大会ルールは [tournament-model.md](tournament-model.md) を参照。

---

## 進め方の原則

- **小さな単位で進め、単位ごとに証明が通ることを確かめる。** 1 単位は 1 つの定義か 1 つの定理とする。`--wfail` ビルドが通ってから次へ進み、`sorry` を残したまま積まない（[lean-guidelines.md §7](lean-guidelines.md#7-作業の単位とローカルでの検証)）。
- **ルールの骨格を、バニラのカードと基本武器・基本装備で先に完成させる。** 複雑な能力システム（8 ステージ連続効果・4 区分置換効果・キーワード群）と全カード転記はその上に載せる。
- 各マイルストーンは **「実装」「テスト」「証明」** の 3 つを同時に満たして完了とする。
- 証明は下の層から積む: データ（L0）→ プリミティブ（L1）→ 手続き（L2）→ 大域（L3）→ 効果 IR（L4）→ 関係仕様（L5）→ 情報（L6）。
- 独立仕様 `Legal` と一致定理（I6）は、フレームを追加するマイルストーンごとに整備する。
- **差し込み口（Hook・4 区分置換経路）は最初から空の実装で用意する。** スタブに依存する証明は具体的な実装ではなく性質に対して書く。
- **IR の構文は解釈器を書く前に実カードで検証する**（M3b）。

---

## 不変条件・定理のカタログ（I1〜I20）

| ID | 内容 | 層 | 初出 |
|---|---|---|---|
| **I1** | **物理カードの保存**: Start-of-Game 以降、全ゾーン（Arena 全スロット・Soul・Combat Chain・Non-Arena・Inventory）の `PhysId` 列は、`step` の前後で常に `List.Perm` の関係にある。Token・Layer・Attack-Proxy は `PhysId` を持たないため影響しない | L1 | M2 |
| **I2** | **位置の一意性**: 各 `ObjId` は全ゾーン・全 Chain Link を通じてちょうど 1 か所に存在する（連結列が `Nodup`） | L1 | M2 |
| **I3** | **整形性の保存**: 初期状態は `WF` と `OwnerOk` を満たし、`step` はこれらを保存する（`Reachable s → WF s ∧ OwnerOk s`） | L3 | M2〜 |
| **I4** | **内部エラーが起きない**: `WF s ∧ OwnerOk s ∧ CardDB.WF s.cards` なら、`step` は `RuleError.internal` を返さない（ハンドラの中身に依らない） | L3 | M2〜 |
| **I5** | **進行性**: ゲームが終わっていなければ、投了以外の合法手があるか、偶然の決定が求められている。分割選択（Loadout / Defend / PitchOrder / TriggerOrder）の途中でも行き止まりにならない | L3 | M3 |
| **I6** | **`Legal` との一致**: `step` の健全性・完全性と、`legalActions` の構成的列挙の一致（[design.md §6.3](design.md#63-独立仕様-legal-と-i6)） | L3 | M2〜（フレーム種別ごと） |
| **I7** | **勝敗・引き分けの一意性**: 生存 Hero が 1 人ならそのプレイヤーの勝利、全残存 Hero が同時に 0 以下なら引き分け（CR 1.10.2a, 4.5） | L2 | M3 / M5 |
| **I8** | **資産（AP / Resource / Chi）とピッチ会計**: AP・Resource・Chi は非負。Pitch は手札から Pitch Zone へ 1 枚移し、カードのピッチ値分だけ対応資産を増やす。オーバーピッチ（不足 0 での追加ピッチ）は違法（CR 1.14.3b）。End Phase（4.4.3e）で全プレイヤーの AP・Resource・Chi が 0 になる | L1 | M3 |
| **I9** | **ターン・スタック・フェイズ構造**: Start → Action → End のフェイズ順が固定されている。Stack は LIFO（5.3.1）。レイヤーを積むと同一プレイヤーが優先権を保持し、解決後はターンプレイヤーが優先権を得る（1.11.3） | L2 | M3〜M4 |
| **I10** | **隠れ情報の非干渉**: プレイヤー `p` の合法手は `view p s` のみに依存する（偶然の決定を除く、`ObjId` 付け替え同型のもと）。特に相手手札・裏向き Arsenal/Banished/Cloaked・**相手が End Phase に Deck 底へ戻した Pitch 順**が漏れない | L6 | M9 |
| **I11** | **Combat Chain 7 ステップと装備・LKI 整合**: Layer → Attack → Defend → Reaction → Damage → Resolution → Close の順（Phantasm/Spectra の強制クローズを除く）。Resolution Step で Go Again（LKI 含む）があれば +1 AP（7.6.2）。Close Step で防御装備は同一 `ObjId`・カウンターを保ったまま装備ゾーンへ戻り、非装備カードはオーナー墓地へ移る（7.7） | L2 | M5 |
| **I12** | **自動処理の停止**: 到達可能な状態からの `advance` が有限歩で次の決定点・終局に達する。I12a（Game State Process 停止）、I12b（`run` 解釈器停止）、I12c（8 ステージ連続効果の有限性: 内側上限で常に停止）に分割して積む | L2 | M5〜 |
| **I13** | **構築とロードアウトの整合**: CC / Blitz / LL の合法な登録 Card-Pool と合法な Loadout 分割は、開始時状態条件を満たし、物理カードの多重集合（`List.Perm`）を保存する | L0 | M1 |
| **I14** | **時間切れ後の終了**: 時計が時間切れを通知した後、高々 2 ターン（現行ターン残余＋追加 1 ターン）でゲームが終了する（未決着なら引き分け: TRP End-of-Round） | L2 | M5b |
| **I15** | **fuel の単調性**: `step n s a = .ok r ∧ n ≤ m → step m s a = .ok r`。fuel 切れ以外のエラーも `fuel` に依らない | L3 | M2 |
| **I16** | **優先権の受け渡し**: パスで時計回りに優先権が移り、全員連続パスで最上位レイヤー解決または次ステップ遷移が起きる（1.11, 5.3） | L2 | M4 |
| **I17** | **`priority` の時点で `Settled`**: `priority` フレームが先頭にある到達可能状態は、Game State Process（1.10.2）の不動点（`Settled`）を満たす | L2 | M5 |
| **I18** | **任意選択の強制質問**: 解釈器は `may`・任意追加コスト・モード・対象・Pitch 戻し順・Arsenal 配置を勝手に決めず、必ず決定フレームを出す（P4） | L4 | M4 |
| **I19** | **同時誘発の開始プレイヤー選択とループ検出健全性**: 同時誘発時、ターンプレイヤーが開始プレイヤーを選んだ後、時計回りに各プレイヤーが自分の誘発順を選ぶ（6.6.6b）。また外部ループ検出器が強制ループを報告したら、同値状態へ戻り続ける | L2/L3 | M6 / M9 |
| **I20** | **End Phase の Pitch 回収と手札補充**: End Phase 完了時点で全プレイヤーの Pitch Zone は空（すべて Deck 底へ移動済み）。第 1 ターン（Turn 0）の End Phase では全プレイヤーが、通常ターンではターンプレイヤーのみが Intellect 枚まで引く（既に Intellect 枚以上なら引かない、Deck 切れでも敗北しない: 4.4.3c, 4.4.3f） | L2 | M3 |

---

## マイルストーン詳細（M0〜M10）

### M0: 基盤整備
**実装**
- `lean-toolchain`（`leanprover/lean4:v4.36.0`）、`lakefile.toml`（`Fab`, `FabCards`, `FabDriver`, `FabTest`、`defaultTargets = ["Fab"]`）。全ファイル `module` 形式。
- `Fab/Basic/RulesVersion.lean` に基準 CR / TRP の版番号と日付を固定。
- `scripts/verify.sh`（全ライブラリ `--wfail` ビルド、`lake test`、`lake check --inadvisably-no-sandbox`、`cr_citations.py`）を作成。
- `README.md` の免責文（LSS Terms of Use 準拠）と `NOTICE`（Apache-2.0 はコードのみ）を設置。

**完了条件**: `scripts/verify.sh` がローカルで通る。**2026-11-24 に達成済み**（`lake build --wfail` 17 jobs、`lake test`、`lake check` 標準 3 公理のみ、`cr_citations.py`）。

---

### M1: 静的データ・デッキ構築・ロードアウト（CR 1.1, 2.0-2.12, 4.1.4, TRP）
**実装**
- `Core/{Ids,Supertype,CardType,Property,Cost,Keyword,Mode}.lean`。
  - Name + Pitch のユニーク識別、ColorStrip（Red/Yellow/Blue/None）、AssetCost（AP / Resource / Chi / Life）、Class / Talent / Generic。
- `Card/{CardDef,CardDB}.lean`（メタデータ＋両面・分割面枠のみ。能力は空）。
- デッキ・Card-Pool 構築述語（`DeckValid`）とフォーマット別述語（`CCValid`、`BlitzValid`、`LLValid`、`LimitedValid`、`CommonerValid`）：
  - Hero（Adult / Young）、Card-Pool 上限（80 / 52）、Deck 枚数（60+ / 40 / 30+）、Name + Pitch 同名上限（3 / 2 / 無制限）、Class/Talent 適合、Specialization、Legendary（Name 単位 1 枚）、Banned / LL リスト。
- 試合前ロードアウト合法性 `LoadoutValid`（装備 4 部位＋武器 1H/2H/Off-Hand＋Deck＋残り Inventory が Card-Pool の順列）。

**証明（L0）**
- 各合法性述語の `Decidable` インスタンス。
- **I13**（CC / Blitz 合法デッキ＋ロードアウトの包含および物理カード保存）。
- 資産コスト算術（割引後も非負、Chi 充当規則の健全性）。

**実装の記録（2026-11-24）: 完了**
- 実装: `Fab/Core/{Ids,Supertype,CardType,Property,Cost,Keyword,Mode}.lean`、`Fab/Card/{CardDef,CardDB}.lean`、`Fab/Rules/Deck.lean`、`Fab/Tournament/DeckLegality.lean`、`FabTest/{Fixtures,Core,Deck}.lean`。
- 証明した主な定理:
  - `Supertype.matchesHero_generic` / `matchesHero_self` / `matchesHero_mono`
  - `clampNonNeg_of_nonneg` / `clampNonNeg_of_nonpos` / `clampNonNeg_mono`
  - `AssetCost.modifyResources_cancel` / `modifyResources_reduce_le`
  - `AssetPool.canPay_of_spend_some` / `exists_spend_of_canPay` / `spend_accounting` / `not_needsResources_of_canPay` / `not_canPay_chi_without_chi`
  - `CardDef.isHero_of_isAdultHero` / `not_isDeckCard_of_isHero`、`CardDB.mem_of_find?_some` / `wf_empty`
  - **I13**: `LoadoutValid.pool_perm` / `pool_length` / `allCards_allowed`、`ccDeckValid_coreDeckValid`、`ccLoadoutValid_deck_ge_60`、`ccLoadoutValid_total_le_80`、`ccLoadoutValid_sound`
- 検証: `./scripts/verify.sh`（45 jobs `--wfail` ビルド、`lake test`、`lake check` 標準 3 公理のみ、`cr_citations.py` 184 引用 / malformed 0）。

---

### M2: ゾーン・オブジェクト・Start-of-Game・エンジン骨格（CR 1.2-1.4, 3.0-3.16, 4.1）
M2a（状態・ゾーン・`moveObj`・イベント経路骨格・基本プリミティブ）と M2b（エンジン骨格・Start-of-Game Procedure・Driver）に分けて進める。

**実装**
- `State/{Object,Lki,Zone,Combat,Pool,Event,Decision,GameConfig,GameState,WF}.lean`。
- 唯一のゾーン移動プリミティブ `moveObj`：
  - Arena 内移動（`ObjId`・カウンター・タップ維持）と Non-Arena 境界跨ぎ（新規 `ObjId` 払い出し・状態リセット＋LKI 生成）を明示的に区別。
- イベント経路 `perform` の骨格（4 区分置換の差し込み口は空実装で用意）。
- 基本アクション: `drawOne`（山札空でもエラー／敗北にせず no-op）、`pitchCard`、`discardCard`、`banishCard`。
- エンジン骨格: `microStep`、`advance`、`step`、`Legal`、`legalActions`、`FabDriver`（seed 付き乱数）。
- **Start-of-Game Procedure（CR 4.1）**:
  - Hero 配置 → 先手決定（偶然＋選択）→ **試合前ロードアウト分割選択**（`chooseLoadout`: 装備・武器・Deck 選択）→ 装備同時公開 → シャッフル（偶然）→ Intellect 枚ドロー（マリガンなし）。

**証明（L1〜L3）**
- **I1**（物理カード保存）、**I2**（位置一意性）、**I3**（`WF` / `OwnerOk` 保存）、**I4**（内部エラーなし）、**I15**（fuel 単調性）。
- Arena 内 `moveObj` の `ObjId` 維持と、Non-Arena 境界跨ぎの `ObjId` 新規性（`moveObj_fresh`）。
- セットアップのフレーム群についての **I6**（`Legal` との一致）。
- Start-of-Game 完了時の初期手札枚数が `min intellect deckSize` であること。

**M2a 実装の記録（2026-11-24）: 完了**
- 実装: `Fab/Basic/ListLemmas.lean`、`Fab/State/{Zone,Lki,Object,GameConfig,Event,GameState}.lean`、`Fab/Rules/{Move,Add}.lean`、`Fab/Rules/Actions/{Draw,Pitch,Discard,Banish}.lean`、`FabTest/Actions.lean`。
- 証明した主な定理:
  - ゾーン・状態: `ZoneKind.idx_lt` / `idx_inj` / `all_nodup`、`Zone.key_inj`、`allZones_nodup`、`GameState.empty_wf` / `empty_ownerOk`、`GameState.zone_unique`（**I2**）、`GameState.locate_eq`
  - `moveObj` / `addObject`: `moveObj_wf`（**I3**）、`moveObj_physIds`（**I1**）、`moveObj_ownerOk`、`moveObj_fresh`、`moveObj_arena_preserves`（Arena 内移動での `ObjId`・`-1{d}` カウンター維持）、`addObject_wf` / `addObject_ownerOk`
  - 基本アクション: `drawOne_empty_noop`（デッキ切れ敗北なし）/ `drawOne_wf` / `drawOne_physIds` / `drawOne_ownerOk` / `drawOne_lengths_of_ownerOk`、`pitchOne_wf` / `pitchOne_physIds` / `pitchOne_ownerOk` / `pitchOne_adds_assets`（**I8** 1 歩）、`discardOne_*`、`banishOne_*`
- 検証: `./scripts/verify.sh`（73 jobs `--wfail` ビルド、`lake test`、`lake check` 標準 3 公理のみ、`cr_citations.py` 284 引用 / malformed 0）。

**M2b 実装の記録（2026-11-24）: 完了**
- 実装: `Fab/State/{Phase,Decision}.lean`、`Fab/Rules/{Reorder,Setup,Frames}.lean`、`Fab/Spec/Legal.lean`、`Fab/Engine/Step.lean`、`Fab/Invariant/Step.lean`、`FabDriver/Run.lean`、`FabTest/Setup.lean`。
- Start-of-Game Procedure（CR 4.1）を継続スタックフレーム（`chanceFirstPlayer` → `chooseFirstPlayer` → `chooseLoadout` → `revealLoadouts` → `chanceShuffle` → `openingDraws` → `draw`）および 1v1 投了として実装。
- 証明した主な定理:
  - 並べ替え・セットアップ: `GameState.wf_reorder` / `physIds_reorder` / `ownerOk_reorder`、`GameState.initial_inv` / `initial_wf` / `initial_ownerOk` / `initial_cards_wf`、`revealAllLoadouts_wf` / `ownerOk` / `physIds`
  - **I1 / I3 / `OwnerOk`**: `step_physIds`、`step_wf`、`step_ownerOk`、`Reachable`、`Reachable.inv`
  - **I4（内部エラーなし）**: `advance_not_internal`、`step_not_internal`、`Reachable.not_internal`
  - **I6（`Legal` 一致: 健全性・完全性・列挙一致）**: `legal_of_step_ok`、`step_illegal`、`step_sound`、`legalFrameActions_iff`、`concedeActions_iff`、`legalActions_iff`
  - **I15（fuel 単調性）**: `advance_mono`、`step_mono`
- 検証: `./scripts/verify.sh`（93 jobs `--wfail` ビルド、`lake test`、`lake check` 標準 3 公理のみ、`cr_citations.py` 345 引用 / malformed 0）。

---

### M3: ターン骨格・ピッチ＆資産会計・End Phase（CR 1.14, 4.2-4.5）
**実装**
- 3 フェイズ（Start → Action → End）と手番交代、投了（Concede）、Hero ライフ 0 による勝敗・同時引き分け（CR 4.5）。
- 資産プール（AP / Resource / Chi）とピッチ手順（不足分がある間のみピッチ可＝オーバーピッチ禁止 1.14.3b）。
- **End Phase（CR 4.4）**:
  - ターンプレイヤーの任意 Arsenal 配置（空のとき手札から裏向き 1 枚: `chooseArsenal`）
  - **Pitch Zone → Deck 底への順序選択**（`choosePitchOrder`: 1 枚ずつの分割選択）
  - アンタップ（4.4.3d）、全資産リセット（4.4.3e）
  - 手札補充（4.4.3f: **第 1 ターン Turn 0 は全プレイヤー、以降はターンプレイヤーのみ Intellect 枚まで引く**）
  - ターン継続効果の失効

**証明（L1〜L3）**
- **I5**（進行性）、**I7**（勝敗・引き分け一意性）、**I8**（資産・ピッチ会計とオーバーピッチ禁止）、**I9**（フェイズ順）、**I20**（Pitch 回収と Turn 0 / 通常ターン手札補充）。
- 新フレーム（`priority`, `chooseArsenal`, `choosePitchOrder`）についての **I6**。
- 何もせずパスし続ける 1v1 対局およびピッチ→デッキ底循環のシナリオテスト。

**M3 実装の記録（2026-11-24）: 完了**
- 実装・拡張モジュール: `Fab/State/Decision.lean`（`pass`, `arsenalPut`, `arsenalSkip`, `pitchReturnPick`, `beginTurn`, `startPhaseWork`, `actionPhaseStart`, `priority`, `endPhaseStart`, `chooseArsenal`, `returnPitch`, `choosePitchOrder`, `endTurnCleanup`）、`Fab/Rules/Objects.lean`（`untapPlayer`, `checkHeroDefeat`）、`Fab/Rules/Frames.lean`（`nextInOrder`, `refillCount`, `turnPlayerAt`, `turnFrames`, `endPhaseDrawFrames`）、`Fab/Spec/Legal.lean`、`Fab/Engine/Step.lean`、`Fab/Invariant/Step.lean`、`Fab/Invariant/Turn.lean`、`FabDriver/Run.lean`（`nextPassAction`, `runPassLoop`）、`FabTest/Setup.lean`、`FabTest/Turn.lean`。
- 証明した主な定理:
  - オブジェクト更新・勝敗（**I7**）: `untapPlayer_wf` / `ownerOk` / `physIds` / `untapPlayer_idem`、`checkHeroDefeat_wf` / `ownerOk` / `physIds`、`checkHeroDefeat_1v1`（1v1 勝利・同時引き分け一意性）
  - **I9（フェイズ順・手番交代）**: `turnFrames_eq`、`turnPlayerAt_alternates_1v1`
  - **I8（ターン資産会計）**: `actionPhaseStart_adds_ap`、`endTurnCleanup_clears_pools`（M1 の `payResourceCost` オーバーピッチ禁止と併せて完結）
  - **I20（End Phase Pitch 戻し・Turn 1 / Turn ≥ 2 手札補充）**: `returnPitch_empty_pops`、`returnPitch_nonempty_prompts`、`endPhaseDrawFrames_turn1`、`endPhaseDrawFrames_later`、`refillCount_zero_of_ge`
  - **I5（進行性・`TopIdle`）**: `advance_idle`、`step_idle`、`progress_turn_decisions`
  - **I1 / I3 / I4 / I6 / I15**: 新フレーム（`priority`, `chooseArsenal`, `choosePitchOrder` および全ワークフレーム）を含めて `step_physIds` / `step_wf` / `step_ownerOk` / `step_not_internal` / `step_sound` / `legalActions_iff` / `step_mono` を維持。
- 検証: `./scripts/verify.sh`（99 jobs `--wfail` ビルド、`lake test`、`lake check` 標準 3 公理のみ、`cr_citations.py` 394 引用 / malformed 0）。

---

### M3b: 効果 IR の構文先行検証（カードデータパイプライン＋実カード転記）
解釈器を書く前に、実際の FaB カードで IR の表現力を検証する（M1 完了後なら並行着手可、M4 前に完了）。

**実装**
1. [card-data.md](card-data.md) のパイプラインを構築（`fetch.py` → `normalize.py` → `gen_lean.py` → `coverage.py`）。まず **Welcome to Rathe（WTR）** のみを対象に取得・生成する（[design.md §12](design.md#12-決定事項2026-11-24) Q2）。
2. IR の構文型（`Fab/Card/IR/`）と静的検査 `CardDB.WF`（束縛検査、対象枠範囲検査、`Decidable`）を定義。入れ子帰納型を避け `mutual` リスト型にする。
3. **構文だけの転記（`status := .drafted`）**: WTR のカード群（4 クラス: Brute / Guardian / Ninja / Warrior ＋ Generic の装備・武器・攻撃・リアクション・インスタント・オーラ）を転記し、不足語彙・Hook を `docs/ir-gaps.md` に記録して IR を改訂。

**完了条件**: 不足語彙の洗い出しと IR 改訂が済み、`CardDB.WF` が `decide +kernel` で通る。

**M3b 実装の記録（2026-11-24）: 完了**
- データパイプライン: `scripts/fetch.py`（`the-fab-cube/flesh-and-blood-cards@3f16c0b4ad8a` から WTR 全 226 論理カードを取得、アート・フレーバー除去）、`scripts/normalize.py`（型・キーワード正規化、条件付き `go again` / `dominate` の誤抽出防止）、`scripts/gen_lean.py`（`FabCards/WTR/Meta.lean` 自動生成＋`--check` を `scripts/verify.sh` に統合）、`scripts/coverage.py`（`docs/coverage.md` 生成）。
- 効果 IR と静的検査: `Fab/Card/IR/Filter.lean`、`Fab/Card/IR/Effect.lean`（入れ子帰納型を避けた `mutual` リスト型＋`ModeSpec` モード別対象枠＋`ExtraCostSpec.cond`＋`DieBranchList`）、`Fab/Card/IR/WF.lean`、`Fab/Card/CardDef.lean`、`Fab/Card/CardDB.lean`（`CardDB.WF` に全カードの静的 IR 検査を統合し `Decidable` 化）、`Fab/Core/CardType.lean`（`Subtype.gem` 追加）、`Fab/Core/Property.lean`（`ReplacementStage` 一本化）。
- WTR 先行転記と検証: `FabCards/WTR.lean` へ 4 クラス＋Generic＋Gem＋Token の **117/226 論理カード（51.8%、`custom` 0 件）** を `.drafted` 転記し、`FabCards/Registry.lean` で **`theorem wtrDB_wf : wtrDB.WF := by decide +kernel`** を証明。発見したギャップと M4〜M8 申し送り事項を `docs/ir-gaps.md` に記録、`FabTest/IR.lean` に正常・異常系テストを追加。
- 検証: `./scripts/verify.sh`（113 jobs `--wfail` ビルド、`lake test`、`lake check` 標準 3 公理のみ、`gen_lean.py --check` OK、`cr_citations.py` 486 引用 / malformed 0）。

---

### M4: Stack・優先権・カードプレイ 9 手順・基本解釈器（CR 1.11, 5.1-5.4）
**実装**
- Stack（`card-layer`, `activated-layer`）と優先権受け渡し（プレイした側が優先権保持、全員パスで LIFO 解決、解決後はターンプレイヤーへ）。
- **カードプレイ 9 手順（CR 5.1.1）** と失敗時巻き戻し（スナップショット復元）。
- 資産コスト計算（設定→増減→下限 0）と支払い中ピッチ選択（`choosePitch`、Chi 充当含む）。
- Action / Instant のタイミング制御、Hand / Arsenal からのプレイ（Arsenal 裏向きはプレイ可・ピッチ不可）。
- 効果の 1 歩解釈器 `microStep`（基本プリミティブ: draw, discard, gainLife, loseLife, dealDamage(Arcane/Physical), gainAP, gainResource, banish, opt, createToken 等）と Go Again（非攻撃アクション解決時の +1 AP）。

**証明（L2〜L4）**
- **I9**（Stack LIFO・優先権保持）、**I16**（優先権受け渡し）、**I18**（任意選択の強制質問）。
- **L4**: 解釈器 `microStep` が任意の `Effect` で `WF` / `OwnerOk` / `PhysIds` を保存。
- `playProc` 巻き戻しで盤面が完全に元に戻ること。
- 新フレームについての **I6**。

**M4 実装の記録（2026-11-25）: 完了**
- 実装モジュール: `Fab/State/Decision.lean`（`playCard`, `pickMode`, `pitchCard`, `cancelPlay`, `pickMay`, `die6Roll`, `handToDeckPick`, `optPick`, `chooseMode`, `playPayCost`, `choosePitch`, `resolveStack`, `finishResolve`, `run`, `chooseMay`, `chooseModal`, `chanceDie6`, `chooseHandToDeck`, `optStep`, `chooseOpt`）、`Fab/State/GameState.lean`（`LayerInfo`, `BoardSnapshot`, `snapshot`/`restore`, `RollbackOk`）、`Fab/Rules/Add.lean`（`addObject_physIds`）、`Fab/Rules/Actions/Pitch.lean`（`canPitchCard`, `pitchOne_isSome`, `pitchOne_config_rollback`）、`Fab/Rules/Interp.lean`（任意の `Effect`/`Prim` に対する 1 歩解釈器 `interpRunStep`/`execPrim`）、`Fab/Rules/Frames.lean`（CR 5.1.1 カードプレイ 9 手順＋ピッチ支払い＋スナップショット巻き戻し＋Stack LIFO 解決＋Go Again +1 AP）、`Fab/Spec/Legal.lean`、`Fab/Engine/Step.lean`、`Fab/Invariant/Step.lean`（`StepPreserves` 一本化）、`Fab/Invariant/Stack.lean`、`FabTest/Stack.lean`。
- 証明した主な定理:
  - **L4（任意 `Effect` 解釈器保存）**: `execPrim_wf` / `ownerOk` / `physIds`、`interpRunStep_wf` / `ownerOk` / `physIds`（`createTokens_physIds` / `addObject_physIds` 含む）
  - **I9（Stack LIFO・優先権保持・Go Again）**: `playCard_pushes_stack_top`、`playPayCost_retains_priority`（オーバーピッチ禁止付き即時支払）、`resolveStack_lifo`、`finishResolve_returns_priority`
  - **I16（優先権受け渡し）**: `priority_pass_rotates`、`priority_all_passed_resolves_stack`、`priority_all_passed_ends_action_phase`
  - **I18（任意選択の強制質問）**: `interpRunStep_may_prompts`、`run_may_prompts`
  - **巻き戻し完全性**: `GameState.restore_snapshot`、`cancelPlay_restores_exact`、`playPayCost_unpayable_restores_exact`
  - **I1 / I3 / I4 / I5 / I6 / I15**: 新全フレームを含めて `step_preserves` / `Reachable.inv` / `Reachable.not_internal` / `step_sound` / `legalActions_iff` / `progress_m4_decisions` / `step_mono` を維持。
- 検証: `./scripts/verify.sh`（119 jobs `--wfail` ビルド、`lake test`、`lake check` 標準 3 公理のみ、`gen_lean.py --check` OK、`cr_citations.py` 548 引用 / malformed 0）。

---

### M5: Combat Chain 7 ステップ・Attack-Proxy・LKI・装備摩耗・GSP（CR 1.2.3, 1.4.3, 1.10.2, 3.5, 7.0-7.7）
FaB ルールの中核マイルストーン。

**実装**
- **Combat Chain 7 ステップ**: Layer (7.1) → Attack (7.2) → Defend (7.3) → Reaction (7.4) → Damage (7.5) → Resolution (7.6) → Close (7.7)。
- **Defend Step（7.3）**: 手札カード・未防御 Equipment を 1 枚ずつ選んで確定時に同時防御宣言（`defendPick`）。Dominate / Overpower の Hook 検査。
- **Reaction Step（7.4）**: Attack Reaction / Defense Reaction / Instant のスタック応酬。Defense Reaction の解決時防御参加。
- **Damage Step（7.5）**: Power `{p}` − Defense `{d}` 合計による物理ダメージイベント、Hit 判定。
- **Resolution Step（7.6）**: Go Again（Chain Link の LKI 含む）による +1 AP、連続攻撃による次 Chain Link（Link 2, 3, ...）の連結。
- **Close Step（7.7）**: Battleworn / Temper / Blade Break / Guardwell の適用、防御装備・武器の Arena 復帰（同一 `ObjId` 維持）、非装備カードのオーナー墓地移動、「this combat chain」効果失効。
- **Attack-Proxy（1.4.3）と LKI（1.2.3, 3.5.4b）**: 武器攻撃での Attack-Proxy 生成、同一武器の連続攻撃での旧 Proxy 消滅と LKI 保持、攻撃カード離脱時の Chain Link 永続（*Endless Arrow* 等）。
- **Game State Process（1.10.2）**: 優先権前の不動点処理（Hero 死亡・Ally クリア・Non-Arena トークン消滅）。

**証明（L2, L5）**
- **I11**（7 ステップ遷移・Go Again +1 AP・装備の同一 `ObjId` 復帰と摩耗・LKI 保持）。
- **I12a**（Game State Process の停止性: 辞書式測度で証明）。
- **I17**（`priority` 到達時の `Settled` 性）。
- **L5**: 戦闘ダメージ計算（CR 7.5）の独立関係仕様との一致。
- `defendPick` と戦闘関連フレームの **I6**。

---

### M5b: 大会ルール（TRP: 時間切れ・Bo1 マッチ・合意引き分け）
**実装**
- `Tournament/{TimeLimit,Match,Loop}.lean`。
- `Actor.clock` による時間切れ通知（現行ターン＋追加 1 ターン、終了時未決着なら引き分け）。
- スイス Bo1 での合意引き分け（ID）と Top Cut での ID 禁止。
- `Actor.judge` によるループ引き分け。

**証明（L2）**
- **I14**（時間切れ後、高々 2 ターンでゲーム終了）。
- Top Cut 設定で合意引き分けが `Legal` で拒否されること。

---

### M6: 効果システム完全化（8 ステージ連続効果・4 区分置換・誘発・Arcane Prevention）（CR Chapter 6）
**実装**
- **8 ステージ連続効果 `characteristics`（CR 6.3.2）**: Stage 1（Copy）〜 Stage 8（Modified Numeric & Counters）、サブステージ順、依存関係（Dependency: 6.3.3）と循環時 Timestamp フォールバック。
- **4 区分置換効果と Prevention（CR 6.4-6.5）**: Self/Identity → Standard → Prevention（Arcane Barrier / Spellvoid / Quell / Ward / Shielding Prevention）→ Outcome-replacement（Clash 等）。同一区分競合時の当事者選択フレーム `chooseReplacement`。
- **誘発能力と積み順（CR 6.6）**:
  - イベント誘発・状態誘発・遅延誘発（Delayed Trigger: Intimidate 等）。
  - **同時誘発のターンプレイヤー開始選択（6.6.6b）**: `chooseTriggerStart` → 時計回りの `chooseTriggerOrder`。
- 戦闘キーワードの完全統合: Combo, Crush, Reprise, Phantasm, Spectra, Boost, Stealth, Blood Debt 等。

**証明（L2, L5）**
- **I12c**（8 ステージ評価の内側上限による全域停止性）。
- **I19（誘発順）**: ターンプレイヤーが開始プレイヤーを選んだ順と時計回り積み込みの整合。
- **L5**: 8 ステージ連続効果・4 区分置換効果・資産コスト計算の独立関係仕様との一致。
- 公式 Release Notes 裁定の回帰テスト群（Ward 強制破壊 vs Arcane Barrier 任意支払い、Phantasm 強制クローズ、Endless Arrow LKI 等）。

---

### M7: 初期セット完全実装と段階的カード展開
**実装**
- 初期セット（WTR → ARC → CRU → MON → ELE → … と発売順、あるいは現行 CC リーガルセット優先）の全カードを `full` に引き上げ。
- 各カードのシナリオテストと `CardDB.WF` の `decide +kernel` 検査。
- 頻出パターンの IR 昇格と `custom` 数の最小化。

---

### M8: 高度メカニクス（両面・Transcend・Meld・Evo・Cloaked・Ally・Tap・Soul）（CR Chapter 8-9）
**実装**
- **両面カード**: Transcend（表面→裏面反転＋手札移動＋Chi 発生）、Transform、Demi-Hero。
- **分割カード**: Meld（代替コストで左右両面を同時プレイ・合成特性: CR 8.3.38）。
- **装備拡張**: Evo（装備スロット重ね置き・下層カード参照）、Modular、Cloaked（裏向き装備・表向き化）。
- **パーマネント戦闘**: Ally（独自ライフ・攻撃元・攻撃対象・End Phase ライフリセット）、Spectra、Landmark 一意性。
- **Tap / Untap**（CR 8.2 / 2025 High Seas 以降のタップコスト・タップ状態管理）。
- **Soul / Charge**、**Clash / Wager / Mark / Gold / Fealty** 等のセット固有メカニクス。

**証明**: 新規プリミティブ・状態遷移に対する I1〜I4, I6, I11 の維持確認。

---

### M9: 多人数戦（UPF）・隠れ情報非干渉（I10）・ループ検出器（I19）・停止性総仕上げ（I12）
**実装・証明**
- **UPF（Ultimate Pit Fight）**: 3 人以上の手番順、隣接プレイヤー攻撃制限、脱落プレイヤーのオブジェクト除去。
- **I10（隠れ情報非干渉）**: `view p s` の定義と、`ObjId` 付け替え同型のもとでプレイヤー `p` の合法手が `view p s` のみに依存することの証明（特に Pitch 戻し順・手札・裏向き Arsenal の秘匿）。
- **I19（強制ループ検出器）**: `Fab/Tournament/LoopDetect.lean` と健全性証明。
- **I12（自動処理停止性の総仕上げ）**: `run` 解釈器（`repeatN` / `forEach` 含む多重集合測度）とフレームスタック全体の停止性。

---

### M10: 完了判定（`original.md` 最終目的の達成条件）
以下をすべて満たしたとき、リポジトリの最終目的を達成したと判定する：

1. **全カードの実装完了**: 対象カードプール内の全論理カードが `ImplStatus.full` であり、個別のシナリオテストを持つ。
2. **公理・警告ゼロ**: `scripts/verify.sh`（`--wfail` ビルド、`lake test`、`lake check`、`gen_lean.py --check`）がエラー・警告・`sorry`・非標準公理なしで通る。
3. **カタログ定理の全証明**: I1〜I20 のすべて（および全決定フレームの `Legal` 一致 I6）が検証コア `Fab` 内で証明済みである。

---

## カードの実装状況（`ImplStatus`）と 1 枚の完了条件

```lean
inductive ImplStatus where
  | todo        -- 生成ブロックのみ。効果未着手
  | drafted     -- 構文のみ IR に転記済み（解釈器・テスト未検証）
  | «partial»   -- 一部の能力・多人数規則などが未対応（理由をコメント記載）
  | full        -- 全能力を実装し、完了条件を満たした状態
```

**1 枚のカードが `full` になるための完了条件**:
1. 最新公式エラッタに基づく全能力・全特性が `CardDef` に反映されていること。
2. `CardDB.WF` の静的検査を通ること。
3. 効果テキストを持つカードは、`FabTest` に少なくとも 1 つのシナリオテストがあり、期待どおりの盤面遷移と診断イベント不在が確認されていること（テキストを持たないバニラカード・定義済みキーワードのみのカードは、そのキーワードのテストで代替可）。

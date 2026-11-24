# 効果 IR ギャップ分析と Hook 要件（M3b 先行検証）

Welcome to Rathe（WTR、全 226 論理カード / 116 ユニークカード名）から 4 クラス（Brute / Guardian / Ninja / Warrior）＋ Generic ＋ Gem ＋ Token を横断して **117 論理カード**（`custom` 使用数 **0**）を `FabCards/WTR.lean` へ構文転記し、M4〜M8 の解釈器・Hook 設計へ向けた過不足を整理した記録。

---

## 1. M3b 中に発見・解決済みの IR 改訂

実カード転記によって解釈器実装前に発見し、`Fab/Card/IR/` と `Fab/Core/CardType.lean` へ反映した項目：

| 発見元カード | ギャップ内容 | M3b での解決 |
|---|---|---|
| *Heart of Fyendal* (`WTR_000_B`) | `Generic Resource - Gem` の `Gem` サブタイプが `Subtype` に未登録 | `Fab/Core/CardType.lean` に `Subtype.gem` を追加 |
| *Scar for a Scar*, *Breakneck Battery*, *Open the Center* | `the-fab-cube` JSON の `card_keywords` に条件付き言及（`this gets go again` / `this gets dominate`）も混在する | `scripts/normalize.py` で独立行の `Go again` / `Dominate` のみを静的キーワードとし、`Intimidate` は効果語（CR 8.5）として `Prim.intimidate` へ分離 |
| *Pummel* (`WTR_206_R`), *Razor Reflex* (`WTR_209_R`) | モーダル選択肢ごとに**異なる対象制約**を持つ（CR 5.1.2a モード宣言 → 5.1.2c 対象宣言） | `ModeSpec`（モードごとの `targets` と `body`）を `EffectDef.modes` に追加し、`CardDB.WF` で各モードの対象枠境界を独立検査 |
| *Lord of Wind* (`WTR_081_B`) | `Combo` 条件成立時のみ支払える任意追加コスト `{x}` と、`X` を参照する効果本体 | `ExtraCostSpec.cond : Option Condition` を追加し、`hasXCost` による `NumExpr.xValue` の静的束縛検査を `CardDB.WF` に導入 |
| *Blessing of Deliverance* (`WTR_054_R`) | デッキ上 N 枚公開のうち条件一致枚数を束縛してライフ回復に使う | 静的スコープ検査を綺麗に保つため `Effect.bindRevealTopCount` を導入（`VarId` 束縛） |
| *Scabskin Leathers*, *Barkbone Strapping*, *Bone Head Barrier*, *Crazy Brew* | 6 面ダイス出目（値束縛＋切り捨て半減＋出目範囲分岐 1-2/3-4/5-6） | `Effect.rollDie6` + `DieBranchList`（`1 ≤ lo ≤ hi ≤ 6` を静的検査）+ `NumExpr.halfRoundDown` を導入 |
| *Pummel*, *Razor Reflex*, *Whelming Gustwave*, *Hurricane Technique*, *Steelblade Supremacy* | 攻撃や武器へ一時的に誘発能力（`When this hits, ...`）を付与する | `ContinuousMod` を `Effect` と同一 `mutual` ブロックに置き、`ContinuousMod.grantTrigger` で入れ子帰納型なし・`DecidableEq` 自動導出のまま表現 |

---

## 2. M4〜M6 のエンジン・Hook 実装へ申し送る要件

IR 構文には収まったが、実行意味論（M4〜M6）で専用のフレーム・状態・Hook が必要な項目：

### M4（Stack・カードプレイ 9 手順・基本解釈器）
1. **モード先行選択と対象枠バインド（CR 5.1.2a → 5.1.2c）**: `playProc` 内で `EffectDef.modes` が非空ならモード選択フレームを先に出し、選ばれた `ModeSpec.targets` のみ対象選択する。
2. **追加コストの支払いと `lastDiscarded` 記録（Brute 全般・*Enlightened Strike*・*Staunch Response*・*Lord of Wind*）**: `playProc` で `ExtraCost` を支払い、ランダム捨て札には `Actor.chance` フレームを使い、捨てたカードの `LkiSnapshot` をレイヤーに保持して `Condition.lastDiscardedMatches` を判定する。
3. **6 面ダイス偶然フレーム（*Scabskin Leathers* 等）**: `Frame.chanceDie6` と `ActionKind.chanceDie6 (roll : Fin 6)` を追加する。
4. **デッキ検索・墓地/手札シャッフルの分割選択（*Katsu*, *Remembrance*, *Hope Merchant's Hood*）**: 対象選択後に必ず `Frame.chanceShuffle` を積む。
5. **起動型能力の回数制限（`oncePerTurn`）**: オブジェクトごとの「今ターン起動回数」を `GameState` で追跡し、ターン終了時にクリアする。

### M5（Combat Chain 7 ステップ・Attack-Proxy・LKI）
1. **Chain Link 履歴と連続ヒット数（*Combo* 全般, *Fluster Fist*, *Mask of Momentum*, *Dawnblade*）**: `CombatChain` に前リンクの `attackLki`、チェイン内総ヒット数（`chainHits`）、連続ヒット長（`consecutiveHits`）、および武器ごとの今ターンヒット回数（*Dawnblade* の 2 回目判定・*Dorinthea* の 1 回目判定・*Braveforge Bracers* の起動条件）を保持する。
2. **武器の追加攻撃許可 Hook（*Dorinthea*）**: `ContinuousMod.additionalWeaponAttack` により武器の `oncePerTurn` 制限を +1 緩和する Hook を設ける。
3. **非装備防御枚数判定と Reprise 判定（*Barraging Beatdown*, *Reprise* 全般）**: 各 `ChainLink` に「手札から防御に出されたカードが存在するか」および「防御中の非装備カード枚数」を導出関数として持つ。
4. **Attack-Proxy と武器付与能力の継承（*Steelblade Supremacy*, *Ironsong Determination*）**: 武器オブジェクトに付与された `+X{p}` や `grantTrigger` を、その武器が生成する `attackProxy` へ継承する（CR 1.4.3）。

### M6（8 ステージ連続効果・4 区分置換・誘発・Hook）
1. **次ターン遅延継続効果（*Spinal Crush*, *Cranial Crush*, *Cartilage Crush*, *Debilitate*, *Crush Confidence*）**: `Duration.nextActionPhase` / `Duration.untilEndOfNextTurn` および `ModScope.firstActionNextTurn` / `firstAttackNextTurn` を管理するキューを `GameState` に持たせる。
2. **追放領域からのプレイ許可 Hook（*Katsu*, *Singing Steelblade*）**: `Prim.searchDeck` の `playableDuration := some ...` により、対象オブジェクトへ追放領域からのプレイ許可継続効果を付与する。
3. **4 区分置換とダメージ防止（*Drone of Brutality*, *Pounding Gale*, *Bone Head Barrier*）**: `perform` パイプラインの Stage B（標準置換）・Stage C（Shielding Prevention）へ接続する。
4. **残り WTR 109 枚（`todo`）の完全転記**: 残りは同系統パターン（*Savage Swing*, *Wrecker Romp*, *Smash Instinct*, *Forged for War*, *Show Time!*, *Emerging Power*, *Stonewall Confidence*, *Singing Steelblade*, *Ironsong Determination*, *Stroke of Foresight*, *Driving Blade*, *Nature's Path Pilgrimage*, *Demolition Crew*, *Flock of the Feather Walkers*, *Nimble Strike*, *Regurgitating Slog*, *Unmovable*, *Nimblism*, *Sloggism* 等）であり、既存 IR 語彙のみで表現可能（`custom` 不要）であることを確認済み。

---

## 3. WTR 以降のセットで見込まれる拡張（M6〜M8）

- **ARC（Arcane Rising）**: Arcane Damage Prevention（Arcane Barrier / Spellvoid）、Opt、Mechanologist の Boost / Steam カウンター、Ranger の Arsenal 裏表操作と Arrow（*Endless Arrow* LKI）。
- **MON（Monarch）**: Soul / Charge、Blood Debt、Phantasm、Spectra、追放領域からのプレイ。
- **EVO / MST / ROS**: Evo 重ね装備、Transcend 両面反転と Chi `{c}` 支払い、Meld 分割カード（`CardDef.splitRight`）。

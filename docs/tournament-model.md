# Tournament Rules and Policy（TRP）の形式化メモ

Flesh and Blood の公式 **Tournament Rules and Policy（TRP）** のうち、Lean 4 で形式化の対象にする部分（フォーマット、デッキ構築、試合前ロードアウト、マッチ、時間切れ、ループ）を整理したもの。Comprehensive Rules 側は [rules-model.md](rules-model.md)、全体設計は [design.md](design.md) を参照。

> **これは公式ルールの代わりではない。** 規則文は要約であり、厳密な規定は公式ポータル（`https://rules.fabtcg.com`）の Tournament Rules and Policy を確認すること。

---

## 0. 出典と版

| 項目 | 内容 |
|---|---|
| 正とする文書 | Flesh and Blood **Tournament Rules and Policy（TRP）**（`https://rules.fabtcg.com`）。基準版は M0 着手時に `Fab/Basic/RulesVersion.lean` に固定する |
| 引用形式 | `(TRP ...)`。Comprehensive Rules の `(CR ...)` と区別する |
| CR との関係 | 大会ルールはフォーマット制約・マッチ構成・時間切れ・意図的引き分け・ループ裁定を定め、ゲーム内進行は CR に従う |

---

## 1. 形式化の範囲

| 区分 | 対象にするもの | 概要 |
|---|---|---|
| **フォーマットとデッキ構築** | Classic Constructed（CC）、Blitz、Living Legend（LL）、Limited（Sealed / Draft）、Commoner、UPF | Card-Pool 上限、最小／固定デッキ枚数、Name + Pitch 同名制限、Hero（Adult / Young）、Class / Talent 一致、Legendary、Specialization、Banned & Suspended / Living Legend 制限 |
| **試合前ロードアウト** | Card-Pool（Inventory）から Arena（装備・武器）と Main Deck への分割 | CR 4.1.4 と TRP の登録リスト整合性。登録した Card-Pool の範囲内で各試合ごとに編成する |
| **マッチ** | スイスラウンドの **Bo1**、Top Cut / プレイオフの無制限時間または BoN、勝敗と引き分け | FaB のスイスは原則 1 ゲーム先取（Bo1）。引き分け時は双方がドロー |
| **時間切れ** | End-of-Round Procedure（現行ターン終了＋**追加 1 ターン**） | 終了時に決着がつかなければ引き分け（ライフ差判定は原則行わない） |
| **投了と合意の引き分け** | Concede、スイスでの Intentional Draw（ID）許可、Top Cut での ID 禁止 | 行為者・状態遷移としてモデル化 |
| **ループ** | 強制ループ・任意ループの扱いとジャッジ介入による決着／引き分け | エンジンは自動検出せず、ジャッジ行為者 `Action` として受ける（検出器は Driver 側に分離） |

**対象外**:
- イベント運営、参加登録、デッキチェック、座席、GEM によるペアリングとタイブレーク。
- Penalty Procedure Guide（PPG）の罰則（Warning / Game Loss / DQ）、スロープレイやストーリングの主観的判定。
- 誘発の忘れ（Missed Trigger）: エンジンは誘発を忘れないためモデルに現れない。

---

## 2. フォーマットとデッキの合法性

### 2.1 主要 Constructed フォーマット

| 項目 | Classic Constructed（CC） | Blitz | Living Legend（LL） | Commoner |
|---|---|---|---|---|
| **Hero** | Adult Hero 1 枚（Young / Pit-Fighter 不可） | Young Hero 1 枚 | Adult Hero 1 枚（LL 殿堂入りヒーロー使用可） | Young Hero 1 枚 |
| **Card-Pool 上限** | Hero 1 枚 ＋ **最大 80 枚**（装備・武器・デッキ合計） | Hero 1 枚 ＋ **最大 52 枚** | Hero 1 枚 ＋ **最大 80 枚** | Hero 1 枚 ＋ **最大 52 枚** |
| **ゲーム開始時 Deck 枚数** | **60 枚以上** | **ちょうど 40 枚** | **60 枚以上** | **ちょうど 40 枚** |
| **ユニークカード上限** | Name + Pitch ごとに **最大 3 枚** | Name + Pitch ごとに **最大 2 枚** | Name + Pitch ごとに **最大 3 枚**（制限カードは 1 枚） | Name + Pitch ごとに **最大 2 枚** |
| **レアリティ制限** | なし | なし | なし | デッキは Common のみ、装備・武器は Rare 以下（詳細規定は TRP 確認） |
| **禁止・殿堂入り** | Banned リスト ＋ Living Legend（1,000 点到達ヒーローと Signature 武器） | Blitz Banned ＋ Blitz LL（500 点到達） | LL Banned / Restricted リスト | Commoner Banned リスト |

### 2.2 全フォーマット共通のデッキ構築規則（CR 1.1 / 2.11 / 8.3）

1. **Class / Talent 一致（Supertype 適合）**: Card-Pool 内の全カード（Hero 除く）の Supertype は、Hero が持つ Supertype の部分集合であるか、または `Generic`（あるいは `Universal` 等の例外能力）でなければならない。
2. **Specialization（8.3.16）**: `[Hero Name] Specialization` を持つカードは、対応する Hero 名を持つヒーローのデッキにのみ入れられる。
3. **Legendary（8.3.15）**: `Legendary` を持つカードは、Pitch 値にかかわらず**カード名単位で 1 枚まで**。
4. **Unlimited**: 枚数制限の例外（例: *Cracked Bauble* 等）はカード属性で表現する。
5. **試合開始時の編成整合（CR 4.1.4）**:
   - 登録した Card-Pool（Inventory）の多重集合と、`Arena に配置した装備・武器 ＋ Main Deck ＋ 残り Inventory` の多重集合が一致すること（`List.Perm`）。
   - 各装備スロット（Head / Chest / Arms / Legs）は最大 1 枚、Weapon はスロット制約（1H 最大 2、2H 最大 1、1H + Off-Hand 等。ヒーローの meta-static 能力による変更を含む）を満たすこと。

### 2.3 Limited（Sealed / Draft）

| 項目 | Sealed / Draft |
|---|---|
| Hero | 対象セットの Young Hero 1 枚。Draft で登録が必須の場合はイベント中固定 |
| Main Deck | 本文の原則は **30 枚ちょうど**。Appendix F で上書きされる WTR・ARC は **30 枚以上** |
| 同名枚数制限 | 構築フォーマットの同名制限と Legendary の1枚制限は Draft に適用しない |
| Card-Pool | Sealed は開封、Draft はピックで取得したカードと、そのセットで利用可能な Basic レアリティのカード |
| Class / Talent | Hero の Supertype 適合規則は引き続き適用 |

#### Booster Draft の実行

- `BoosterDraft.State.start` にカードデータベース、製品規定、登録の要否、座席ごとの3パックを渡す。製品規定は `FabCards.wtrDraft` と `FabCards.arcDraft` を用意している。両セットとも各パックの先頭15枠がドラフト対象で、末尾1枠を除外する。番号から論理カードIDへの変換には `FabCards.earlyPrintingCardId?` を使う。
- 参加者には本人の `State.view` を渡し、`State.pick` で1枚を確定する。全席が確定すると残りを第1・第3パックでは左へ、第2パックでは右へ渡す。ピック中は過去の取得カードを伏せ、各パックの間は本人が確認できる。レビュー後は `State.openNext` で次のパックを開く。パック内の並びは意味を持たないため、表示順をカードID順に統一している。
- 登録必須のイベントでは `State.register` にHeroと全ピックを渡す。クラス不一致で対戦に使えないカードも登録対象に含まれる。各対戦では `State.deck` がHeroに合うピックと、指定した Basic の武器や Cracked Bauble からカードプールを作る。`GameState.initialDraft` で同じポッドの異なる2席を対戦に渡し、通常の試合前ロードアウトでデッキと装備を選ぶ。

座席割り当て、ジャッジによる呼び出し、持ち時間は大会運営側の入力として扱う。パックは外部から供給でき、WTRでは以下の開封モデルの出力も使える。 [公式TRP 8.2・Appendix F](https://fabtcg.com/documents/604/FaB_Tournament_Rules_and_Policy_2025_05_30.pdf) · [ARC収録表](https://legacy.fabtcg.com/en/collectors-centre/arcane-rising/)

#### WTRのパック開封

- `FabCards.wtrBoosterLayout` はGeneric Common 4枠、4クラスのCommon 7枠、Rare 1枠、Rare・Super Rare・Majestic 1枠、装備1枠、プレミアムFoil 1枠、トークン1枠で構成する。Foil枠にはBasic以外のカードが入り、トークン枠は論理カード1面で表す。順番はモデル上のもので、最後の1枠をドラフトから除外する。 [公式製品仕様](https://legacy.fabtcg.com/en/products/booster-set/welcome-rathe/) · [WTR収録表](https://legacy.fabtcg.com/en/collectors-centre/welcome-rathe/)
- `FabCards.openWtrBooster` は枠ごとの候補番号16個を受け取り、`BoosterDraft.State.start` に渡せるパックを返す。正常に開封できた場合、各枠を対応する候補カードが1枚ずつ埋めることを `BoosterPack.openSlots_fits` で証明している。
- 参照先のWTR Unlimitedシミュレーターは各クラスのCommonを2・2・2・1枚引き、昇格枠でMajesticを1/12、Super Rareを1/6とする抽選を実装している。そのFoil抽選にはFabled枠がない。Leanモデルでは候補番号を決める側がクラス配分、封入率、版ごとの差を指定できる。 [WTR_Sealed公開ソース](https://github.com/ApartmentTom/WTR_Sealed/blob/07d92b80756bc1f6999037519cb2f68bde02aa97/index.html#L416-L475) · [Unlimited公式告知](https://legacy.fabtcg.com/en/articles/wtr-arc-unlimited-edition/)

### 2.4 定理の目標（I13）

- **包含・整合の定理**:
  1. Constructed（CC / Blitz / LL）で合法な登録 Card-Pool と、その合法なロードアウト分割（Arena 装備＋Main Deck＋残り Inventory）は、CR の開始条件（`LoadoutValid`）を常に満たす。
  2. ロードアウト前後で物理カードの多重集合が保存される（`List.Perm`）。

---

## 3. マッチと時間切れ

### 3.1 マッチ形式

- **スイスラウンド（原則 Bo1）**:
  - 試合前ロードアウトによって対策カード・装備の選択が 1 戦目の開始時に完結するため、FaB の標準競技スイスは **Best-of-One（1 ゲーム先取）** である。
  - 勝敗結果: `won [p]` または `draw reason`。
- **Top Cut / プレイオフ**:
  - 標準では時間制限なしの Bo1（または大会規定による Bo3）。時間制限のない環境では引き分け（時間切れ・合意引き分け）は発生しない。

### 3.2 時間切れ（End-of-Round Procedure）

1. ラウンド制限時間終了時、ジャッジ／時計が時間切れを宣言する（モデルでは `Actor.clock` の `Action`）。
2. **現行のターンプレイヤーがそのターンを最後まで終える**。
3. **続いて相手プレイヤーが追加で 1 ターンだけ行う**（計: 現行ターン＋追加 1 ターン）。
4. 追加 1 ターンの End Phase が完了した時点で勝敗が決していなければ、そのゲームは **引き分け（Draw）** となる。
   - **重要**: スイスの時間切れではライフ総量による勝敗判定は行わない（そのまま引き分け）。

**定理の目標（I14）**: 時計が時間切れを通知した後、ゲームは高々 2 ターン（現行ターン残余＋追加 1 ターン）で必ず終了する（`result.isSome`）。

### 3.3 投了と合意の引き分け

- **投了（Concede）**: ゲーム終了前ならいつでも合法。1v1 では相手が勝利する。
- **合意の引き分け（Intentional Draw）**: スイス設定でのみ合法。Top Cut / エリミネーション設定では違法（`Legal` で拒否）。

---

## 4. ループの扱い

- **任意ループ（プレイヤーが選択肢を持つループ）**:
  - プレイヤーが決定を出し続けるだけなのでエンジン側で特別扱いは不要。大会での「N 回繰り返す」省略宣言は Driver 層の機能として後から追加できる。
- **強制ループ（選択肢なく無限に循環する状態）**:
  - エンジン内部で状態同一性を自動検出して引き分けにすることはしない（Non-Arena 移動やレイヤー生成ごとに `ObjId` / `Timestamp` が単調増加するため、厳密な `=` には戻らない）。
  - 代わりに、大会設定では **ジャッジを行為者とする `Action`**（ループ引き分け宣言）を受け付ける。
  - 自動対戦用の強制ループ検出器（`ObjId` と `Timestamp` の順序同型を除いた状態同値による検出）はエンジン外の `Fab/Tournament/LoopDetect.lean` に置き、その健全性を定理（I19）で証明する。
  - 決定点を挟まない自動処理が無限ループに陥った場合の安全弁は `fuel`（`RuleError.fuelExhausted`）が担う。

---

## 5. 設計への反映まとめ

| 論点 | 決定 |
|---|---|
| `RuleSet` / `Format` | `GameConfig` に `ruleSet`（`coreOnly` / `tournament (swiss / topCut)`）、`format`（`cc` / `blitz` / `livingLegend` / `sealed` / `draft` / `commoner` / `upf`）、`mode`（`duel` / `upf`）を保持する |
| ロードアウト | セットアップ（M2）の正規手順として `Inventory → (Arena, Deck, Inventory)` の選択フレームをコアに組み込む |
| 時間切れ | `Actor.clock` の `Action` で受け取り、残りターン数カウンタ（現行＋1）で管理し、終了時に未決着なら `GameResult.draw .timeLimit` にする |
| 禁止・LL リスト | 時期により変動するため、`FormatBanList` データとして外から渡せる構造にし、定理は任意の `FormatBanList` について述べる |

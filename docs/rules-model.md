# Flesh and Blood ルールの形式化メモ（Comprehensive Rules 準拠）

Flesh and Blood（以下 FaB）の公式 Comprehensive Rules を、Lean 4 で形式化する観点で整理したもの。設計方針は [design.md](design.md)、実装の順序は [roadmap.md](roadmap.md) を参照。

> **これは公式ルールの代わりではない。** 規則文は要約であり、逐語引用は避けている。厳密な文言と最新の細部（特に v2.11 以降の細則番号）は、必ず公式ポータル（`https://rules.fabtcg.com`）で該当規則を引くこと。

---

## 0. 出典と版

| 項目 | 内容 |
|---|---|
| 正とする文書 | Flesh and Blood **Comprehensive Rules**（Legend Story Studios 公式ポータル `https://rules.fabtcg.com`）。v2.11.0（2025-06-06）より Web 配信へ移行し、セット発売ごとにマイナー版（v2.12, v2.13, ...）が更新される |
| 基準版の固定 | 実装着手時（M0）に公式ポータルの現行版番号と公開日を `Fab/Basic/RulesVersion.lean` に固定する。本リポジトリでは「CR」と書けばその基準版を指す |
| 大会ルール | **Tournament Rules and Policy（TRP）**。フォーマット、デッキ登録、Bo1 マッチ、時間切れ、ループ等を定める。形式化の範囲は [tournament-model.md](tournament-model.md) |
| 補助資料 | 各セットの Release Notes、公式 Card Legality / Errata / Living Legend リスト。解釈に迷う場合は CR が優先し、Release Notes を回帰テストの根拠に使う |

規則番号の引用形式: docstring やコメントに `(CR 6.3.2)` や `(TRP 4.3)` の形で書く。

---

## 1. Comprehensive Rules の章立て

| 章 | 名称 | 主な内容 |
|---|---|---|
| 1 | Game Concepts | 黄金律、プレイヤー、オブジェクト・LKI（1.2-1.3）、カードと攻撃・Attack-Proxy（1.4）、レイヤー（1.6）、能力（1.7）、効果（1.8）、イベント（1.9）、ゲーム状態と Game State Process（1.10）、優先権（1.11）、コスト（1.14） |
| 2 | Object Properties | 数値・非数値特性: Name（2.6）、Color Strip、Pitch（2.8）、Cost（2.2）、Power（2.7）、Defense（2.3）、Intellect（2.4）、Life（2.5）、Types / Subtypes / Supertypes（2.10-2.12）、Text Box |
| 3 | Zones | Arena と Non-Arena（3.0）、Arms / Chest / Head / Legs / Hero（Soul 含む）/ Weapon / Permanent / Combat Chain（Chain Link）、Deck / Hand / Arsenal / Pitch / Graveyard / Banished / Stack / Inventory |
| 4 | Game Structure | ターン進行（4.0）、Start-of-Game Procedure（4.1）、Start Phase（4.2）、Action Phase（4.3）、End Phase（4.4）、Ending a Game（4.5） |
| 5 | Layers, Cards, and Abilities | カードのプレイ 9 手順（5.1）、能力の起動（5.2）、レイヤーの解決（5.3）、静的能力・誘発能力・起動能力（5.4） |
| 6 | Effects | 離散効果（6.1）、継続効果（6.2）、**8 ステージ連続効果相互作用（6.3）**、**置換効果の 4 区分と適用順（6.4-6.5）**、誘発効果と誘発レイヤー（6.6） |
| 7 | Combat | Combat Chain 一般（7.0）、**Layer (7.1) → Attack (7.2) → Defend (7.3) → Reaction (7.4) → Damage (7.5) → Resolution (7.6) → Close (7.7)** の 7 ステップ |
| 8 | Keywords | ラベルキーワード（8.1）、効果キーワード（8.2）、能力キーワード（8.3: Go Again, Dominate, Overpower, Phantasm, Spectra, Ward, Battleworn, Temper, Blade Break, Guardwell, Arcane Barrier, Spellvoid, Quell, Blood Debt, Boost, Fusion, Transcend, Meld, Tap/Untap 等） |
| 9 | Additional Rules | 両面カード（Double-Faced）、分割カード（Split / Meld）、Evo、Cloaked、Token、Companion、Demi-Hero、Macro、Clash、Wager、Mark 等 |

---

## 2. FaB 固有の設計上の核心（他 TCG との本質的な違い）

形式化モデルを設計するうえで、最初に押さえるべき FaB 固有の特徴を 8 点にまとめる。

1. **手札＝攻撃・防御・資源の 3 役を兼ねる「ピッチサイクル」**: 土地やマナ用デッキが無い。手札のカードを **Pitch** して資源（`{r}`）や気（`{c}`）を生み、ピッチしたカードは **End Phase に所有者が任意の順（非公開）で山札の底へ戻す**（CR 4.4.3c）。山札切れ敗北（Mill / Burn Out）は無く、デッキが一周する「ピッチスタッキング」と枯渇戦（Fatigue）がゲームの中核をなす。
2. **Name + Pitch が論理カードの同一性**: 赤（Pitch 1）・黄（Pitch 2）・青（Pitch 3）の同名カードは、デッキ枚数制限上は**別々のユニークカード**として扱われる（CR 2.6, 2.8）。一方、Legendary（名前単位で 1 枚制限）やカード名指定効果は Name のみを参照する。
3. **試合前ロードアウト（Inventory → Arena / Deck）が第 1 戦のセットアップに組み込まれている**: ヒーローを公開し先手を決めた後、Card-Pool（Inventory）から相手のヒーローに応じて装備品・武器・メインデッキ構成を選ぶ（CR 4.1.4）。Bo1 でもサイドボーディングに相当する決定が Start-of-Game Procedure に存在する。
4. **Action Points（AP）と Go Again**: ターンプレイヤーは Action Phase 開始時に 1 AP を得て、アクション実行で 1 AP 消費する。**Go Again** は非攻撃レイヤーなら解決時、攻撃なら Combat Chain の **Resolution Step（7.6）** で +1 AP を与える。
5. **7 ステップの Combat Chain、Attack-Proxy、Chain Link の永続と LKI**: 攻撃は 1 つの開いた Combat Chain 上に Chain Link を連ねる（7.0-7.7）。武器等の攻撃は **Attack-Proxy** を生成し（1.4.3）、同一武器で再攻撃すると旧 Proxy は消えて **Last Known Information（LKI: 1.2.3）** が Chain Link に残る。攻撃カードが場から離れても Chain Link は存続し、LKI で Go Again 等を判定する（3.5.4b）。
6. **物理ダメージと秘術ダメージ（Arcane Damage）の分離**: 物理ダメージは Defend Step / Reaction Step の防御値 `{d}` で軽減できるが、Arcane Damage は防御値で防げず、Arcane Barrier / Spellvoid / Quell / Ward などの置換・防止効果で対処する。
7. **8 ステージの連続効果（6.3.2）と 4 区分の置換効果（6.4-6.5）**: 連続効果は Copy → Controller → Name/Color/Text → Type/Subtype → Supertype → Ability → Base Numeric → Modified Numeric & Counters の 8 段階で評価される。置換効果は Self/Identity → Standard → Prevention →（実行）→ Outcome の 4 段階で適用される。
8. **同時誘発の積み順は「ターンプレイヤーが開始プレイヤーを選ぶ」**: 一般的な APNAP ではなく、ターンプレイヤーが開始プレイヤーを選び、そこから時計回りに各プレイヤーが自分の誘発レイヤーをスタックに積む（CR 6.6.6b, 1.10.2d）。1v1 ではターンプレイヤーが自分と相手の誘発の解決順を完全に選べる。

---

## 3. 基本原則とオブジェクト・同一性（1.0-1.5）

### 3.1 黄金律・禁止優先・できる範囲で実行

| 規則 | 内容 | モデル化 |
|---|---|---|
| 1.0.1 | カードテキストがルールと矛盾するときはカードテキストが優先する | ルールの各所に差し込み口（hook）を置く（[design.md §7.3](design.md#73-ルールの差し込み口hook)） |
| 1.0.1a | **禁止は許可に優先する（Can't beats Can）** | restriction を permission より常に優先して評価する |
| 1.0.1b / 1.8 | 指示はできる範囲で実行し、不可能な部分は無視する | 解釈器は不可能な指示をエラーにせず飛ばして続ける |
| 1.2.3 | **Last Known Information（LKI）**: オブジェクトが消滅・ゾーン移動した直前の状態（特性・カウンター・適用中効果）のスナップショット。変更不可 | 消滅・移動時に LKI スナップショットを `ChainLink` や誘発 `Env` に保存する |

### 3.2 オブジェクトの種類と同一性（1.3-1.4）

- **オブジェクトの種別**:
  1. **Card（物理カード）**: デッキ・装備・ヒーロー等のカード（`PhysId` を持つ）。
  2. **Token**: 効果で生成されるオブジェクト（Frostbite、Runechant、Seismic Surge、Spectral Shield、Gold、Ash、Aether Ashwing、Ponder、Might、Vigor、Agility 等）。`PhysId` を持たない。Arena を離れると直後に消滅する。
  3. **Macro**: 特殊フォーマットや PvE / イベント用の非カードオブジェクト（将来拡張枠）。
  4. **Layer（スタック上のレイヤー）**:
     - `card-layer`: プレイされたカード自身
     - `activated-layer`: 起動された能力（発生源から独立してスタック上に存在）
     - `triggered-layer`: 誘発した能力（同上）
  5. **Attack-Proxy（1.4.3）**: 武器・アライ・その他攻撃元（attack-source）が攻撃するときに生成される攻撃オブジェクト。攻撃元と同じゾーン（Stack → Combat Chain の該当 Chain Link）に随伴し、攻撃元が別リンクへ移動すると旧 Proxy は消滅して LKI だけが残る。
- **オブジェクトの同一性（3.0.9）**:
  - **Arena と Non-Arena の境界を跨ぐ移動、または Non-Arena ゾーン間の移動**では、原則として**新しいオブジェクトになる**（新しい `ObjId` を払い出し、カウンター・一時的修正・ステータスを失う）。
  - **例外（同一オブジェクトを保つ移動）**:
    - Arena 内の移動（例: 装備品が Equipment ゾーンから Combat Chain へ防御参加し、Close Step で装備ゾーンへ戻る。武器が Weapon ゾーンから Chain Link へ移動し、Close Step で Weapon ゾーンへ戻る）では **同一オブジェクトを保つ**（`-1{d}` カウンターやタップ状態が維持される）。
    - Stack 上のカードが解決して Arena（Permanent や Combat Chain）へ移るとき、カード上の継続効果や指定された対象・モードを引き継ぐ（モデルではプレイ手続き・Chain Link 生成で明示的に引き継ぐ）。
    - **Transcend（8.3）**: 表面から裏面へ反転して手札に戻るが、裏面の状態（Chi を生む面）を保持する特殊遷移。

### 3.3 Owner と Controller（1.3.1）

- **Owner**: カードをゲームに持ち込んだプレイヤー（トークンはその生成を指示されたコントローラー／作成者）。Non-Arena ゾーンでは常に Owner のゾーンへ戻る。
- **Controller**: 盤面上のオブジェクトやレイヤーを支配するプレイヤー。継続効果（Stage 2）で変わりうるため、オブジェクト表には基底値を持ち、判定には `characteristics` で導出した実効 Controller を使う。

### 3.4 情報の公開度（3.0.4-3.0.5）

| 区分 | 説明 | 該当ゾーン・オブジェクト |
|---|---|---|
| **Public** | 全プレイヤーが全特性を参照できる | Arena 全体（ただし裏向きの Cloaked 装備等を除く）、Graveyard、Banished（表向き）、Stack、公開済み Combat Chain、表向き Arsenal |
| **Private** | Owner（または Controller）のみ参照でき、対戦相手は枚数・存在のみ見える | Hand、Pitch Zone の順序（ピッチしたカード自体は公開されて Pitch Zone に入るが、End Phase にデッキ底へ戻す順序は非公開！）、裏向き Arsenal、裏向き Banished、裏向き Cloaked 装備、Inventory の未公開カード |
| **Hidden / Secret** | どのプレイヤーも参照できない（効果で Look / Opt したカードを除く） | Deck の中身と順序（枚数は Public） |

> **FaB 特有の注意点**: Pitch Zone にあるカード自体は表向きで Public だが、End Phase（4.4.3c）にデッキ底へ置くときの**並べ順は非公開（Hidden Information）**である。これは隠れ情報非干渉（I10）の設計に直接影響する。

---

## 4. カード特性と分類（2.0-2.12）

### 4.1 特性一覧

| 特性 | 規則 | 型・意味 |
|---|---|---|
| Name | 2.6 | カード名。分割カード（Meld）は両面の名前を持つ |
| Color Strip | 2.0 / 2.8 | Red / Yellow / Blue / なし。通常 Pitch 1 / 2 / 3 に対応（Chi カード等は特殊） |
| Pitch `{p}` | 2.8 | `Option Nat`（1, 2, 3 等。ピッチで生む資源量または Chi 量。値を持たないカードはピッチ不可） |
| Cost `{r}` / `{c}` | 2.2 | 資産コスト（Resource Points、Chi Points、Life、Action Points 等） |
| Power `{p}` (Attack) | 2.7 | `Option Int`（攻撃値。攻撃や Phantasm 判定に使う） |
| Defense `{d}` | 2.3 | `Option Int`（防御値。Defend Step / Defense Reaction で物理ダメージを軽減。`-1{d}` カウンターで増減） |
| Intellect `{i}` | 2.4 | Hero の手札補充上限（通常 4。一部ヒーローは 3 や 5） |
| Life `{h}` | 2.5 | Hero / Ally のライフ値（Adult Hero は通常 40、Young Hero は通常 20 等） |
| Supertype | 2.11 | **Class**（Brute, Guardian, Ninja, Warrior, Wizard, Runeblade, Mechanologist, Ranger, Illusionist, Assassin, Bard, Merchant, Shapeshifter, Necromancer, Pirate, Thief 等）、**Talent**（Light, Shadow, Elemental, Earth, Ice, Lightning, Draconic, Mystic, Chaos, Royal, Revered, Reviled 等）、および **Generic** |
| Type | 2.10 | Hero, Weapon, Equipment, Action, Attack Reaction, Defense Reaction, Instant, Block, Resource, Mentor, Token, Demi-Hero, Macro, Companion |
| Subtype | 2.12 | Attack, Aura, Item, Ally, Arrow, Construct, Landmark, Affliction, Figment, Invocation, Ash, Arms, Chest, Head, Legs, Off-Hand, 1H, 2H, Bow, Claw, Club, Dagger, Flail, Gun, Hammer, Orb, Pistol, Polearm, Scepter, Scythe, Staff, Sword, Wrench, Base, Evo, Young, Pit-Fighter 等 |

### 4.2 数値特性の床（Floor）と負値

- Power・Defense・Cost などの数値特性は、Stage 7〜8 の修正やカウンター（例: `-1{d}`）によって計算される。
- ルール上、ダメージ計算や防御合計など多くの参照では負値を 0 として扱うが、途中の加算・減算のために内部表現は `Int` とし、参照時の床（0 クランプ）を規則ごとに明示する（CR 2.0.3 / 6.3）。

---

## 5. ゾーン（3.0-3.16）

| ゾーン | 区分 | 所属 | 順序 | 主な役割・FaB 固有規則 |
|---|---|---|---|---|
| **Hero** | Arena | プレイヤーごと | なし | Hero カードを置く。直下の副ゾーンとして **Soul**（Hero の下に裏または表で差し込まれたカード群）を持つ |
| **Head / Chest / Arms / Legs** | Arena | プレイヤーごと | あり（Evo 用） | 各スロットに基本 1 枚の Equipment を装備。**Evo** は既存の Base/Equipment の上に重ねて配置し、下のカードは下層に残る |
| **Weapon** | Arena | プレイヤーごと | なし | 通常 2 枠（1H を最大 2 つ、または 2H を 1 つ、あるいは 1H + Off-Hand）。ヒーローの静的能力で変動しうる |
| **Permanent** | Arena | プレイヤーごと | なし | Aura、Item、Ally、Landmark、Token 等の場に残るパーマネント |
| **Combat Chain** | Arena | **共有（全プレイヤーで 1 つ）** | **あり（Chain Link 列）** | 開閉状態を持つ。各 Chain Link が「攻撃（カードまたは Attack-Proxy＋攻撃元）」「防御カード列」「攻撃対象」「ヒット成否・LKI」を保持 |
| **Stack** | Non-Arena | **共有（全プレイヤーで 1 つ）** | **あり（LIFO）** | card-layer / activated-layer / triggered-layer が積まれる |
| **Deck** | Non-Arena | プレイヤーごと | **あり（Hidden）** | 上からドロー、下にピッチ戻し・Opt 下置き。空になっても敗北しない |
| **Hand** | Non-Arena | プレイヤーごと | なし（Private） | プレイ・ピッチ・防御の供給源。上限なし（End Phase は Intellect 枚**まで**引くのみ） |
| **Arsenal** | Non-Arena | プレイヤーごと | なし（裏=Private, 表=Public） | 通常容量 1（カード効果で拡張可能）。裏向きはプレイのみ可（Defense Reaction は裏向きでもプレイ可だが、通常の防御カードとしては出せず、ピッチも不可） |
| **Pitch** | Non-Arena | プレイヤーごと | なし（Public） | ターン中にピッチしたカードの置き場。End Phase（4.4.3c）に所有者が任意の順（非公開）で Deck の底へ戻す |
| **Graveyard** | Non-Arena | プレイヤーごと | あり（Public） | 解決後の非パーマネントカード、破壊されたカード、Combat Chain クローズ後の非装備カード等 |
| **Banished** | Non-Arena | プレイヤーごと | なし（表=Public, 裏=Private） | 追放領域。Blood Debt や Levia / Chane / Uzuri / Intimidate 等で多用される。表向き・裏向き（face-down）の区別が必須 |
| **Inventory** | Non-Arena | プレイヤーごと | なし（Private） | 試合開始前に選ばなかった装備・武器・デッキ候補カードを置く。ゲーム中の効果で Inventory から装備・参照するカード（例: 一部のヒーロー・アイテム・Evo 関連）が存在するため、エンジン内部でも明示的に保持する |

※ これに加え、エンジン内部の一時領域として `setAside`（Intimidate による一時追放や Opt / Look の一時退避等に使う場合。ただし Intimidate はルール上「裏向き Banished に置き、End Phase に手札に戻す遅延効果」なので、可能な限り CR どおり Banished＋タグ／遅延効果で表す）および `outsideGame` を必要に応じて検討する。

---

## 6. ターン構造とセットアップ（4.0-4.5）

### 6.1 Start-of-Game Procedure（4.1）

優先権は発生しない（4.1.1）。

1. **ヒーロー公開（4.1.2）**: 各プレイヤーが Hero カードを Hero ゾーンに表向きで置く。
2. **先手決定（4.1.3）**: ランダムに選ばれたプレイヤー（マッチ 2 戦目以降がある場合は敗者）が、誰が第 1 ターンを行うか選ぶ。
3. **ロードアウト選択（4.1.4）**: 各プレイヤーは登録済みの Card-Pool（Inventory）から、アリーナに置く装備・武器（Head/Chest/Arms/Legs/Weapon）を裏向きに配置し、メインデッキ（CC は 60 枚以上、Blitz はちょうど 40 枚）を編成する。残りは Inventory に置く。
4. **装備の同時公開とシャッフル（4.1.4-4.1.5）**: 全員が装備・武器を同時に表向きにし（Cloaked は裏向きのまま）、メインデッキをシャッフルする。
5. **初期手札ドロー（4.1.6）**: 全員が Hero の Intellect 枚まで引く。（FaB にはマリガンが無い！）
6. 第 1 ターン開始（Start Phase へ）。

### 6.2 ターンの 3 フェイズ（4.2-4.4）

| フェイズ | 優先権 | 処理内容 | 規則 |
|---|---|---|---|
| **1. Start Phase** | なし（誘発が積まれた場合のみ解決のため優先権が発生） | 「Start of turn」誘発イベント発生。全プレイヤーがパスしスタックが空になると Action Phase へ | 4.2 |
| **2. Action Phase** | あり（ターンプレイヤーから） | 開始時にターンプレイヤーが **1 Action Point** を得る（4.3.2）。アクション・インスタントのプレイ／起動、Combat Chain の開始と進行。スタックが空かつ Combat Chain が閉じた状態で全プレイヤーが連続パスすると End Phase へ（4.3.3） | 4.3 |
| **3. End Phase** | **なし**（ただし「Beginning of end phase」誘発が積まれた場合は解決する） | ① Beginning of end phase 誘発（Blood Debt 等）→ スタック解決（4.4.2）。② End-of-turn 手順（4.4.3）を厳密な順で実行：Ally ライフリセット → ターンプレイヤーは任意で手札 1 枚を空の Arsenal に裏向き配置（4.4.3b）→ **各プレイヤーが Pitch Zone の全カードを任意の順（非公開）で Deck の底へ置く（4.4.3c）** → ターンプレイヤーのタップ状態のパーマネントをアンタップ（4.4.3d）→ **全プレイヤーの全 AP・Resource・Chi を 0 にする（4.4.3e）** → **手札補充（4.4.3f）**: ターンプレイヤーは Intellect 枚まで引く。**第 1 ターン（Turn 0）のみ全プレイヤーが Intellect 枚まで引く** → 「until end of turn」継続効果の失効 → 次ターンへ | 4.4 |

### 6.3 勝敗と引き分け（4.5, 1.10.2）

- **Game State Process（1.10.2）**: 優先権をプレイヤーに渡す直前に毎回実行される。
  - `1.10.2a`: ライフが 0 以下の Hero（または Hero を失ったプレイヤー）は即座に敗北。残存全プレイヤーが同時に敗北条件を満たした場合は **引き分け（Draw）**。残り 1 人ならそのプレイヤーの勝利。
  - `1.10.2b`: ライフ 0 以下の Living Card（Ally 等）、一意性違反（Landmark 等）、不正な状態のカードをクリア。
  - `1.10.2d`: 保留中の Triggered-layer をスタックに積む（§8.3）。
- 投了（Concede）はいつでも可能。
- デッキが 0 枚でもドロー不能なだけで敗北しない（CR 4.5 にデッキ切れ敗北は無い）。

---

## 7. コスト・ピッチ・カードのプレイ・優先権（1.11, 1.14, 5.1-5.4）

### 7.1 資産（Assets）とコスト（1.14）

- **Asset-cost（資産コスト）**:
  1. **Action Point（AP）**: Action カードのプレイや Action 起動能力に 1 AP。
  2. **Resource Point `{r}`**: カードのピッチ（通常 1/2/3）や効果で生成。ターン終了まで保持。
  3. **Chi Point `{c}`**: Mystic / Transcend 等の Chi カードのピッチや効果で生成。Chi コストは Chi でしか払えず、通常 `{r}` コストに Chi を充当できる（CR 1.14.2b: Chi は `{r}` コストの支払いにも使える）。
  4. **Life Point `{h}`**: ライフ支払いコスト（ただし 0 以下になる支払いは不可等の制約を確認）。
- **Effect-cost（効果コスト）**: 捨て札、破壊、追放、タップ（`{t}`）、カウンター除去、ソウルからの追放など。

### 7.2 カードのプレイ手順（CR 5.1.1 の 9 ステップ）

1. **Announce**: プレイするカードを宣言し、Stack へ移動して `card-layer` とする（巻き戻し用スナップショット保存）。
2. **Declare Costs**: 代替コスト（Meld、フリープレイ等）、任意追加コスト、可変値 `X` を宣言。
3. **Declare Modes and Targets**: モード選択および合法な対象（攻撃なら攻撃対象: 相手ヒーロー、Ally、Spectra オーラ等）を宣言。
4. **Check Legal Play**: タイミング（Action / Instant / Attack Reaction / Defense Reaction）、ゾーン許可（Hand / Arsenal / Banished 等）、禁止効果（Can't play）、対象の合法性を検証。
5. **Calculate Asset-Costs**: 資産コストの最終額を計算（設定 → 増加 → 減少、下限 0）。
6. **Pay Asset-Costs**: AP・Resource・Chi・Life を支払う。**不足分の `{r}` / `{c}` を生むための Pitch はここで行う**（必要な分を超えてピッチしすぎることは原則禁止：オーバーピッチ禁止規則 CR 1.14.3b — 不足がある間だけピッチできる！）。
7. **Calculate Effect-Costs**: 効果コストを計算。
8. **Pay Effect-Costs**: 効果コストを支払う（ピッチ以外の支払い）。
9. **Play**: プレイ完了。`played` イベント発行（"When you play..." の誘発）→ 優先権の移行（5.1.9）。

> **重要（巻き戻し）**: ステップ 4・6・8 で失敗した場合、ゲーム状態をステップ 1 開始前のスナップショットへ巻き戻す（CR 5.1.1 / 1.9.3）。モデルでは `Legal` の側で支払い可能性を含めて検証するか、巻き戻しフレームで安全にロールバックする。

### 7.3 優先権（1.11）とレイヤー解決（5.3）

- 優先権は高々 1 人が持つ。
- プレイヤーがレイヤーを積むと、**同じプレイヤー（プレイした側）が続けて優先権を保持する**（CR 1.11.3a）。
- 全プレイヤーが連続してパスすると、Stack が非空なら**最上位レイヤーを解決（LIFO）**し、解決後は **ターンプレイヤー** が優先権を得る（CR 5.3.1, 1.11.3b）。
- Stack が空で全員が連続パスすると、現在のステップ／フェイズが次へ進む。
- **タイミング許可**:
  - `Action`: 自分のターンの Action Phase で、Stack が空かつ（Combat Chain が閉じているか、Resolution Step であること）。1 AP 必要。
  - `Instant`: 優先権があればいつでも（相手ターン・スタック上・Combat 中を含む）。AP 不要。
  - `Attack Reaction`: 自分のターンの Combat Chain の **Reaction Step（7.4）** で、優先権があるとき。AP 不要。
  - `Defense Reaction`: 相手のターンの Combat Chain の **Reaction Step（7.4）** で、防御側プレイヤーが優先権を持つとき。AP 不要。解決すると該当 Chain Link の防御カードとなる。

---

## 8. 効果システム（Chapter 6）

### 8.1 連続効果と 8 ステージ制（CR 6.2-6.3）

実効特性 `characteristics` は印刷値（基底）に全有効継続効果を以下の **8 ステージ** 順で適用して導出する（CR 6.3.2）：

| Stage | 対象特性 | 例 |
|---|---|---|
| **Stage 1** | Copyable properties | カードのコピー効果 |
| **Stage 2** | Controller | コントロール奪取 |
| **Stage 3** | Name, Color Strip, Text Box | 名前変更、色帯変更、テキスト書き換え |
| **Stage 4** | Types, Subtypes | カード型・サブタイプの追加・変更 |
| **Stage 5** | Supertypes | Class / Talent の付与・喪失 |
| **Stage 6** | Abilities | 能力・キーワードの付与（Go Again, Dominate 等）および喪失 |
| **Stage 7** | Base values of numeric properties | 基本 Power / Defense / Cost の設定 |
| **Stage 8** | Modified values of numeric properties & counters | `+N{p}`, `-N{d}`, `-1{d}` カウンター、条件依存の数値修正 |

- **同一ステージ内の順序（CR 6.3.3）**:
  1. **独立効果 → 依存効果（Dependency）**: 効果 A の適用有無が効果 B の存在・対象・結果を変えるなら B は A に依存し、A を先に適用する。
  2. **サブステージ（修正の種類）**: 制限・変更不可 → 設定（Set）→ 乗除 → 加算 → 減算。
  3. **Timestamp 順**: 上記が同列なら生成時刻（Timestamp）の古い順。

### 8.2 置換効果の 4 区分と適用順（CR 6.4-6.5）

イベント `ev` を実行する際、適用可能な置換効果は以下の 4 区分をこの厳密な順で適用する（同一の置換効果は 1 イベントに高々 1 回）：

1. **Self-replacement & Identity-replacement（6.4.10a, 6.4.10b）**: 同一能力内の「代わりに〜」および「〜の状態でアリーナに出る（カウンター付きで出る等）」。
2. **Standard-replacement（6.4.10c）**: 一般の「〜するなら代わりに〜」置換効果（例: 墓地へ行く代わりに追放、ドローの置換）。
3. **Prevention（6.4.10d）**: ダメージ防止効果（Arcane Barrier、Spellvoid、Quell、Ward、Shielding prevention 等）。
4. **（確定イベントの適用）** → **Outcome-replacement（6.4.10e）**: イベントの結果（Clash 敗北など）を別の結果へ置換する。

同一区分内で複数の置換が競合する場合、**影響を受けるイベントの当事者（影響を受けるオブジェクトの Controller または対象プレイヤー）が適用順を選択**する（CR 6.5.1）。

### 8.3 誘発効果と積み順（CR 6.6）

- 誘発条件（イベント誘発 / 状態誘発）が成立すると `triggered-layer` が生成され、保留キューに入る（発生源はイベント発生前から存在していなければならない: 6.6.5a）。
- Game State Process（1.10.2d / 6.6.6b）で、保留中の誘発レイヤーをスタックへ移すとき：
  1. **ターンプレイヤーが開始プレイヤーを 1 人選ぶ**。
  2. 開始プレイヤーから**時計回り**に、各プレイヤーが自分のコントロールする保留中誘発レイヤーを、**自身の選ぶ順序**でスタックに積む。
- **Delayed-triggered effect（遅延誘発: 6.6.3）**: 発生源が場を離れても指定時点まで待機して誘発する（例: Intimidate の「ターン終了時に手札に戻す」）。

---

## 9. コンバットチェイン（Chapter 7）

FaB の戦闘はすべて **Combat Chain** 上の **Chain Link** として処理される。

### 9.1 7 ステップの遷移

| Step | 規則 | 優先権 | 処理内容 |
|---|---|---|---|
| **1. Layer Step** | 7.1 | あり | 攻撃カードまたは攻撃起動能力が Stack に積まれ、Combat Chain が開く（既に開いていれば新しい Chain Link の準備）。スタック上の攻撃レイヤーに対し両者が Instant 等で応答可能。攻撃レイヤーが解決すると Attack Step へ |
| **2. Attack Step** | 7.2 | あり | 攻撃カード（または **Attack-Proxy**＋武器等の攻撃元）が新しい **Chain Link** に置かれ、攻撃状態になる。「When this attacks」誘発。両者パスで Defend Step へ |
| **3. Defend Step** | 7.3 | なし（防御宣言のみ）→ あり | **防御側プレイヤーが手札のカード（Defense 値を持つもの）および／または自分の未防御 Equipment を任意の枚数選んで同時に防御カードとして Chain Link に置く**（スタックを使わない）。Dominate / Overpower 等の制約を検査。「When this defends」や Phantasm 誘発。その後、優先権が回り両者パスで Reaction Step へ |
| **4. Reaction Step** | 7.4 | あり | ターンプレイヤーから優先権。攻撃側は **Attack Reaction**（および Instant）、防御側は **Defense Reaction**（および Instant）をスタックに積める。Defense Reaction は解決時に Chain Link の防御カードに加わる（手札からプレイされた場合は Dominate に計上される点に注意）。スタック空で両者パスすると Damage Step へ |
| **5. Damage Step** | 7.5 | あり（ダメージ計算後） | 攻撃の Power `{p}` と防御カードの Defense `{d}` 合計を比較し、差分が正なら攻撃対象（Hero / Ally 等）へ**物理ダメージ**を与えるイベントを発行（Prevention 等の置換を通る）。1 点以上与えたら **Hit** となり「On hit」誘発が発生。スタック処理・両者パスで Resolution Step へ |
| **6. Resolution Step** | 7.6 | あり | 攻撃（または Chain Link の LKI）が **Go Again** を持つなら、攻撃側コントローラーが **+1 AP** を得る（7.6.2）。ターンプレイヤーが優先権を得て、**続けて新しい攻撃を行えば新たな Chain Link の Layer Step へ遷移しチェインが継続**する。スタック空で両者パスすると Close Step へ |
| **7. Close Step** | 7.7 | なし | 「When the combat chain closes」処理（Battleworn / Temper / Blade Break / Guardwell 等）。チェイン上の非パーマネントカード（攻撃アクション・手札からの防御カード・リアクション）はオーナーの墓地へ、防御に参加した装備品・武器は各自のアリーナゾーンへ戻る（同一オブジェクト維持）。「this combat chain」継続効果が失効し、Combat Chain が閉じる → Action Phase の通常優先権へ戻る |

### 9.2 戦闘の特殊事項

- **Attack-Proxy の二重攻撃（1.4.3）**: 武器で Link 1 を攻撃し、Go Again で同じ武器で Link 2 を攻撃した場合、Link 2 に新しい Attack-Proxy と武器本体が移り、Link 1 の Attack-Proxy は消滅して LKI のみが Link 1 に残る。
- **チェインの強制クローズ**: Phantasm（非 Illusionist の Power 6 以上の Attack Action で防御されたときの誘発解決）や Spectra（攻撃対象に選ばれたときの誘発解決）は攻撃を破壊し、Damage Step 等を飛ばして直ちに Close Step へ遷移する。
- **防御不可カード**: Arsenal のカード（Defense Reaction 除く）、Defense 特性を持たないカード（`defense = none`）、同一チェインの別リンクで既に防御に使った装備品（チェイン上に既にあるため）は Defend Step に出せない。

---

## 10. 主要キーワード（Chapter 8）

FaB には 60 以上のキーワードが存在する。初期段階から枠組みを押さえておくべき代表的キーワードを分類する。

| 分類 | キーワード例 | 規則上の性質・モデル化 |
|---|---|---|
| **行動・テンポ** | **Go Again** (8.3.5) | 解決時（攻撃は 7.6 Resolution Step）に +1 AP |
| **防御制約** | **Dominate** (8.3.4), **Overpower** (8.3.26) | Defend Step / Defense Reaction の合法性 hook（手札 1 枚制限 / Action 1 枚制限） |
| **装備摩耗** | **Battleworn** (8.3.2), **Blade Break** (8.3.3), **Temper** (8.3.10), **Guardwell** (8.3.36) | Close Step（7.7）で防御参加した装備に `-1{d}` カウンターや破壊を適用 |
| **秘術・ダメージ防止** | **Arcane Barrier X** (8.3.1), **Spellvoid X** (8.3.11), **Quell X** (8.3.19), **Ward X** (8.3.21) | Prevention 置換効果（6.4.10d）。コスト支払い（任意）または自身破壊（Ward は強制） |
| **攻撃ギミック** | **Phantasm** (8.3.13), **Spectra** (8.3.14), **Combo** (8.3.6), **Crush** (8.3.7), **Reprise** (8.3.8), **Stealth** (8.3.24), **Boost** (8.3.9), **Piercing X**, **Ambush** | 誘発・条件・追加コスト・Chain Link 履歴参照（Combo は前リンクの名前参照、Reprise は防御側の手札からの防御有無参照、Crush は 4 点以上のダメージ参照） |
| **デッキ・追放・ソウル** | **Opt X** (8.2), **Intimidate** (8.2), **Charge** (8.2), **Blood Debt** (8.3.12), **Mark** (8.2), **Clash** (8.2) | 効果プリミティブおよび遅延誘発／End Phase 誘発 |
| **変身・構造変化** | **Transcend** (8.3), **Transform** (8.2), **Meld** (8.3.38), **Evo / Modular** (8.3), **Cloaked** (8.3), **Tap / Untap** (8.2) | 両面カード反転、分割カード両面プレイ、装備重ね置き、裏向き装備、タップ状態管理 |
| **構築制約（Meta-static）** | **Legendary** (8.3.15), **Specialization** (8.3.16), **Universal**, **Unlimited** | デッキ構築述語 `DeckValid` で検査 |

---

## 11. 曖昧な点・実装着手時に CR 原文で確定すべき事項

1. **基準 CR バージョンの確定**: M0 着手時点で `rules.fabtcg.com` の最新安定版（例: v2.15.x）の版番号と全規則番号を確定し、本メモおよびコード中の引用番号を厳密に照合する。
2. **オーバーピッチ禁止と任意コスト支払い（CR 1.14.3b, 5.1.6）**: 既に必要な `{r}` / `{c}` を満たしている状態では追加ピッチできないが、不足が 1 点のときに Pitch 3（青）を 1 枚ピッチして 2 点余ることは合法。可変コスト X や Chi と `{r}` が混在するコストの支払い順序・合法性判定を `Legal` で厳密化する。
3. **防御参加装備と Close Step の処理順（7.7）**: 複数装備の Battleworn / Temper / Blade Break / Guardwell の適用と破壊の順序、および破壊で誘発する効果のタイミング。
4. **Stage 6〜8 の循環依存（CR 6.3.3）**: 相互依存する連続効果が発生したときのループ解消規則（タイムスタンプへのフォールバック）を原文で照合し、L5 関係仕様に落とす。
5. **Arena 内のオブジェクト同一性の境界（CR 3.0.9）**: Evo で装備が下層へ入ったとき、Weapon が Attack-Proxy を伴って複数回攻撃したとき、および一時的裏向き化（Cloaked / Turn face-down）時の `ObjId` とカウンター維持条件。
6. **Multi-player（UPF: Ultimate Pit Fight）の攻撃対象・隣接プレイヤー・誘発順**: 型は最初から N 人対応で作るが、UPF 固有の隣接制限や開始プレイヤー選択の細則は M9 で原文照合する。

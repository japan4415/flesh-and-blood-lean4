# カードデータと効果 IR（Flesh and Blood）

Flesh and Blood のカードをどこから取り込み、どのように Lean のデータにし、どのように効果 IR へ落とすかの方針。効果 IR 本体の設計は [design.md §7](design.md#7-効果-ir深い埋め込みと-hook) を参照。

---

## 1. FaB カードプールの構造と特徴

Flesh and Blood の最初のブースターは、2019 年発売の **Welcome to Rathe（WTR）**。現在までに 15 以上のブースターセット・補助セットが存在する。カードデータの取り扱いには次の FaB 固有の事情がある。

1. **Name + Pitch（赤・黄・青）による 3 色展開**:
   - 多くのアクション・リアクション・インスタントカードは同一カード名で **Red（Pitch 1 / 高威力）**・**Yellow（Pitch 2 / 中威力）**・**Blue（Pitch 3 / 低威力）** の 3 バージョンが存在する。
   - ルール上、**Name + Pitch の組が 1 つの論理カード（Unique Card）** である（CR 2.6, 2.8）。
   - 一方で効果テキストの構造は 3 色で同一（数値パラメータのみ異なる）ケースが大半であるため、Lean 側の手書き IR では **色別パラメータ関数（ヘルパ）** を活用して重複を最小化する（§4.2）。
2. **両面カード・分割カード（Meld）・トークン・ヒーロー・装備・武器の多様性**:
   - 表裏両面を持つカード（Transcend の Chi 面、Transform、Demi-Hero、Invoke ドラゴンなど）
   - 分割カード（Meld: 左右 2 つの半面を持ち、片面プレイと両面合成プレイの両方が可能）
   - Hero（Adult / Young）、Weapon（1H / 2H / Off-Hand）、Equipment（Head / Chest / Arms / Legs、Evo、Base）
3. **公式エラッタと Living Legend / Banned リストの継続更新**:
   - カード文面は印刷時のものではなく、**最新公式エラッタ適用後の現行文面**を正とする。
   - フォーマットごとの禁止カード・Living Legend 殿堂入りリストはカード定義自体ではなく `FormatBanList` データとして分離管理する。

---

## 2. データ源

| 源 | 形式 | 長所 | 注意点 |
|---|---|---|---|
| **`the-fab-cube/flesh-and-blood-cards`**（GitHub オープンデータ） | JSON / CSV（スキーマ定義あり） | **Name + Pitch 単位で論理カード（`unique_id`）に正規化済み**。最新公式エラッタ反映済み。特性（pitch, cost, power, defense, health, intelligence, types, card_keywords, functional_text_plain, printings, double-sided / split 関連）が網羅的に構造化されている | コミュニティ保守データのため、新セット直後や最新エラッタは公式カード DB と照合する。カードテキスト・名前の知的財産権は LSS に帰属する |
| **公式カードデータベース**（`cards.fabtcg.com`） | Web | Legend Story Studios による一次情報。最新エラッタ・禁止制限・Living Legend ポイントの正本 | 機械取得用の安定 JSON 配布は限定的 |
| **公式ルールポータル**（`rules.fabtcg.com`） | Web | Comprehensive Rules・TRP・Release Notes の一次情報 | 規則番号・裁定テストの正本 |

**方針**:
- `the-fab-cube/flesh-and-blood-cards` のリリース版 JSON を主要な構造化データ源としてスナップショット取得し、必要に応じて公式カード DB の最新エラッタ・Release Notes で補正パッチを当てる。

---

## 3. 取り込みのパイプライン

```text
scripts/fetch.py      データ源から日付付きスナップショット JSON を取得
scripts/normalize.py  正規化: Name + Pitch 論理カードの確定、両面・分割カードのリンク、
                      型・Supertype・Subtype の分類、エラッタ補正の適用
scripts/gen_lean.py   FabCards/<Set>.lean の生成ブロックを更新し、新カードの雛形を追記
                      （--check で差分検査。scripts/verify.sh から呼ぶ）
scripts/coverage.py   セット別実装状況表（docs/coverage.md）を生成
```

- Python は `uv` で管理し、`uv run` で実行する。
- Lean ビルド時に JSON を直接読まない（ビルド再現性・キャッシュ・型検査の明確さのため）。スナップショット JSON と生成ブロックを含む `FabCards/<Set>.lean` をコミットし、`gen_lean.py --check` で一致を保証する。
- **論理カードの同一性と `CardId`**:
  - キーは **`(name, pitch)`**（両面カードは表面基準＋裏面参照、分割カードは両面名基準）。
  - `CardId` は初出セットの印刷コード＋色接尾辞（例: `WTR_118_R` / `WTR_118_Y` / `WTR_118_B`、または `unique_id` ベースの安定 ID）とし、**一度決めた `CardId` はエラッタや再録があっても変更しない**。
  - 再録は初出セットのファイルの生成ブロック内 `Printings:` に追記する。
  - テキストハッシュはキーに含めず、エラッタによる文面変更の検出のみに使う。

---

## 4. Lean 側の表現

```lean
/-- カードの 1 面（表面・裏面・Meld の右半面）。 -/
structure CardFace where
  name       : String
  supertypes : List Supertype     -- Class / Talent / Generic（CR 2.11）
  types      : List CardType      -- Action / AttackReaction / Equipment / Hero ...（CR 2.10）
  subtypes   : List Subtype       -- Attack / Aura / Head / 1H / 2H / Young ...（CR 2.12）
  color      : Option ColorStrip  -- Red / Yellow / Blue
  pitch      : Option Nat         -- 1 / 2 / 3（CR 2.8）
  cost       : Option AssetCost   -- Resource / Chi / Life（CR 2.2）
  power      : Option Int         -- {p}（CR 2.7）
  defense    : Option Int         -- {d}（CR 2.3）
  intellect  : Option Nat         -- Hero 用 {i}（CR 2.4）
  life       : Option Int         -- Hero / Ally 用 {h}（CR 2.5）
  keywords   : List KeywordInst   -- 印刷キーワード（CR 8）
  abilities  : List Ability       -- Passive / Replacement / Activated / Triggered
  playEffect : Option EffectDef   -- 解決時の離散効果（非パーマネント・攻撃等）

/-- 論理カード 1 種（Name + Pitch 単位）の定義。 -/
structure CardDef where
  id         : CardId
  front      : CardFace
  back       : Option CardFace    -- 両面カード（Transcend / Transform / Demi-Hero）
  splitRight : Option CardFace    -- 分割カード（Meld: CR 8.3.38）
  sets       : List SetCode       -- 収録セット一覧
  status     : ImplStatus         -- todo / drafted / partial / full
```

### 4.1 ファイル構成: 1 弾 1 ファイル

- `FabCards/WTR.lean`、`FabCards/ARC.lean`、`FabCards/CRU.lean` … のように **1 弾 1 ファイル** とし、`FabCards/Tokens.lean` に全トークン定義、`FabCards/Registry.lean` に全 `CardDB` を集約する。
- 各論理カードは **生成ブロック**（`-- BEGIN GENERATED <CardId>` 〜 `-- END GENERATED`）と **手書き部分** を並べて記述する。
- 公式英語テキスト（最新エラッタ後）は生成ブロックの docstring に入れ、`linter.missingDocs` とホバー表示と陳腐化チェックを兼ねる。
- 1 弾 1 ファイルにする理由は `riftbound-lean4` の実測（200 枚を 200 ファイルに分けると 52 秒、1 ファイルなら 1.9 秒）に基づく。ファイルが大きくなりすぎた弾のみ `FabCards/<Set>/Part1.lean` のように分割する。
- `FabCards/*` は `Fab.Card` のみを import し、`GameState` やエンジン本体には依存しない。

### 4.2 赤・黄・青（Pitch 1/2/3）の重複削減パターン

FaB 特有の 3 色展開を簡潔に保つため、同名の 3 色カードで効果構造が同一のものは、`FabCards/<Set>.lean` 内にパラメータ化したローカルヘルパを書く：

```lean
-- 例: 効果構造が共通でダメージ量だけ色別に違うカード
private def sinkBelowEffect : List Ability := [...] -- 共通ロジック

def WTR_215_R : CardDef := { WTR_215_R.meta with front := { WTR_215_R.meta.front with ... }, status := .full }
def WTR_216_Y : CardDef := { WTR_216_Y.meta with front := { WTR_216_Y.meta.front with ... }, status := .full }
def WTR_217_B : CardDef := { WTR_217_B.meta with front := { WTR_217_B.meta.front with ... }, status := .full }
```

これにより論理カード単位の独立性（`CardId` ごとの定義）と、手書き IR の保守性を両立できる。

---

## 5. 文面パターンと IR への写像（FaB 代表パターン）

| 文面パターン（FaB） | IR / Hook 表現 |
|---|---|
| `Go again` | キーワード `Keyword.goAgain`（非攻撃は解決時、攻撃は 7.6 Resolution Step で +1 AP） |
| `Dominate` / `Overpower` | キーワード → Defend Step / Defense Reaction の防御制約 Hook |
| `Battleworn` / `Blade Break` / `Temper` / `Guardwell` | キーワード → Close Step（7.7）の装備摩耗処理 |
| `Arcane Barrier X` / `Spellvoid X` / `Quell X` / `Ward X` | キーワード → Prevention 置換効果（6.4.10d） |
| `Combo — If [Card Name] was the last attack this combat chain, ...` | `Condition.prevChainLinkNamed name`＋`ifThen` |
| `Crush — If this deals 4 or more damage to a hero, ...` | `Trigger.onDealDamage (min := 4) (to := .hero)` |
| `Reprise — If the defending hero has defended with a card from their hand this chain link, ...` | `Condition.defendedFromHandThisLink` |
| `When this hits, ...` | `Trigger.onHit` |
| `Opt X` | `Prim.opt x`（山札上 X 枚を見て上・下へ分ける決定フレーム） |
| `Intimidate` | `Prim.intimidate`（相手手札からランダム 1 枚を裏向き追放＋End Phase 返還の遅延誘発） |
| `Deal X arcane damage to target hero.` | `EffectDef`（対象枠 `.hero`）＋ `Prim.dealDamage .arcane (.slot 0) x` |
| `Next attack action card you play this turn gains +X{p}.` | 期間付き継続効果 `grantNext`（`Duration.thisTurn`、1 回消費） |
| `Once per Turn Action — {r}: Attack`（武器起動） | `Ability.activated`（`oncePerTurn := true`, `speed := .action`, 攻撃プロキシ生成） |

---

## 6. 実装状況の管理

- `ImplStatus`（`todo` / `drafted` / `partial` / `full`）と完了条件は [roadmap.md](roadmap.md) 末尾に従う。
- `scripts/coverage.py` がセットごとの件数・IR 転記率・`full` 率・`custom` 使用数・テスト有無を `docs/coverage.md` に出力する。

### 初出順と WTR 発売前の収録範囲

公式カードデータベースと製品・配布記録を参照し、初回発売・配布日が古い製品から実装する。WTR 発売前の範囲は2019年10月11日より前とする。同じ製品ではカード番号順に進める。別印刷は既存の論理カード ID に紐付ける。配布日が不明な場合は、確認できた印刷日と配布記録を別々に記録する。 [公式 Card Vault](https://cardvault.fabtcg.com/) · [進捗チェックシート #246](https://github.com/japan4415/flesh-and-blood-lean4/issues/246)

| 製品・配布物 | 初出の根拠 | 実装 |
|---|---|---|
| Slingshot Underground | 2018年12月の発売前配布 | `OXO001-P`〜`OXO004-P` を対応する WTR の Ironrot 装備に紐付ける。`OXO002-P` の旧名称と `OXO002-P`〜`OXO004-P` の参照先誤記は、公式の印刷記録を参照。 [公式記録](https://legacy.fabtcg.com/en/collectors-centre/promos-and-extras/) |
| Ira Welcome Deck | 2019年8月31日発売 | 12種すべてに対応。新規の論理カードは10種で、Head Jab と Scar for a Scar は WTR の既存カードを参照する。 [公式製品ページ](https://legacy.fabtcg.com/en/products/welcome-deck-2019/) · [公式収録表](https://legacy.fabtcg.com/en/collectors-centre/ira-welcome-deck/) |
| Local Game Store 初期プロモ | 2019年8月印刷、カード個別の初回配布日は未確認 | `LGS001-P`〜`LGS008-P` の8種を対応する WTR カードに紐付ける。 [公式プロモ一覧](https://legacy.fabtcg.com/en/collectors-centre/promos-and-extras/) |
| Special Use Promos | `LSS001-P` と `LSS002-P` は2019年8月印刷。確認できた配布は WTR 発売後 | `LSS001-P` は2021年の Alpha Investments 配布、`LSS002-P` は2019年10月25〜28日の Mighty Ape 配布。 [公式プロモ一覧](https://legacy.fabtcg.com/en/collectors-centre/promos-and-extras/) · [2021年当時の配布記録](https://www.rathetimes.com/articles/state-of-the-market-end-of-november-2021) · [Mighty Ape 配布記録](https://legacy.fabtcg.com/en/articles/my-first-fabled/) · [イベント日程](https://www.armageddonexpo.co.nz/armageddon-updates/auckgeddon-2019-is-here/) |

`throughWtrDB` は WTR の226種と IRA 初出の10種、合計236論理カードを提供する。印刷番号は `earlyPrintingCardId?` で解決する。 [登録の回帰テスト](../FabTest/EarlyCards.lean)

---

## 7. モデルにとって難しいカード（先に設計で考慮しておくもの）

M3b の先行検証と M5〜M8 の設計で必ず検証対象に含める代表的な難関カード群：

| 分類 | 代表例 | 必要な仕組み |
|---|---|---|
| **Chain Link 永続と LKI** | *Endless Arrow*（ヒット時に手札へ戻るが Go Again は機能する） | Chain Link の永続＋`LkiSnapshot`（CR 1.2.3, 3.5.4b） |
| **Attack-Proxy 連続攻撃** | *Dawnblade*（同一チェイン内で複数回攻撃し、ヒット数でカウンター付与） | `ObjectKind.attackProxy` と旧 Proxy の LKI 化（CR 1.4.3） |
| **強制クローズ誘発** | *Phantasm* 攻撃（6{p} 非 Illusionist 攻撃アクション防御で即破壊＆クローズ）、*Spectra* オーラ（攻撃対象指定で即破壊＆クローズ） | 状態・条件誘発＋`Prim.closeCombatChain`（7.7 へジャンプ） |
| **Prevention 競合と強制性** | *Ward X*（強制破壊して軽減）vs *Arcane Barrier X*（任意コスト支払い）vs *Shielding Prevention*（ターン中プール軽減） | 4 区分置換の Prevention 段（6.4.10d）と当事者順序選択（6.5.1） |
| **同時誘発の順選択** | 攻撃側・防御側双方の `On Hit` / `End Phase` 同時誘発 | ターンプレイヤーによる開始プレイヤー選択＋時計回り順序（CR 6.6.6b） |
| **両面カードと Chi** | *Transcend* カード（裏面反転して手札へ入り、ピッチで Chi `{c}` を生む） | `CardFace` 表裏、`FaceState`、Chi 資産支払い・充当規則（1.14.2b） |
| **分割カード（Meld）** | *Meld* を持つ分割カード（片面プレイまたは代替コストで両面合成プレイ） | `splitRight`、`Declare Costs` での代替コスト選択、両面合成特性（8.3.38） |
| **装備の重ね置き・裏向き** | *Evo*（Base 装備の上に重ねて装備）、*Cloaked*（裏向きでアリーナ開始し後から表向き化） | 装備スロットの `List ObjId`、`faceDown` 状態と非機能化 |
| **Outcome-replacement** | *Clash* 敗北時の結果置換（例: Gold 破壊で再 Clash） | イベント実行後の Outcome-replacement 段（CR 6.4.10e） |
| **追放領域プレイと負債** | *Blood Debt*（表向き追放から End Phase に 1 ライフ喪失）、*Chane* / *Levia*（追放領域からのプレイ） | 表向き・裏向き Banished、プレイ元ゾーン許可 Hook、End Phase 誘発 |
| **非公開のデッキ底積み** | End Phase の Pitch→Deck 底、*Opt*、*Sink Below*（手札からデッキ底へ置き 1 ドロー） | `choosePitchOrder`、非公開情報射影 `view`（I10） |
| **8 ステージ依存関係** | 基本値設定（Stage 7）と現在値参照（Stage 8: 例 *Minnowism*、型追加とクラス参照） | 8 ステージ連続効果と同一ステージ内依存関係（CR 6.3.2-6.3.3） |
| **手札外・Inventory 参照** | 試合前 Loadout 選択、ゲーム中に Inventory から装備を出すカード | `Zone.inventory` をゲーム状態に保持し、物理カード保存 I1 に含める |

---

## 8. 新しいキーワードを追加する手順

1. 公式 CR（`rules.fabtcg.com`）の Chapter 8 を確認し、[rules-model.md §10](rules-model.md#10-主要キーワードchapter-8) に追記する。
2. `Fab/Core/Keyword.lean` にコンストラクタ（必要ならパラメータ付き）を追加する。
3. 意味を与える：誘発・起動型は能力列への展開（`KeywordInst.abilities`）、静的能力・置換型は対応する Hook または 4 区分置換へ接続する。
4. キーワードの性質補題を 1 つ以上証明する。
5. `scripts/normalize.py` / `scripts/gen_lean.py` のキーワード抽出器を更新する。
6. 該当キーワードを持つテストカードでシナリオテストを追加する。

---

## 9. 新しいセットを追加する手順

1. 公式の最新 CR・Release Notes・TRP を確認し、ルール変更があれば先に [design.md §9](design.md#9-ルールとカードの版管理) に沿って反映する。
2. `scripts/fetch.py` → `scripts/normalize.py` → `scripts/gen_lean.py` で `FabCards/<Set>.lean` を生成する。
3. まず構文転記（`drafted`）で IR の過不足を確認し、不足があれば `docs/ir-gaps.md` に記録して新キーワード（§8）やプリミティブ・Hook を追加する。
4. 解釈器とシナリオテスト（Release Notes 裁定を含む）を整備して `full` にする。
5. `scripts/verify.sh` を通し、カバレッジ表を更新する。

---

## 10. 権利面の注意（法的助言ではない）

- Flesh and Blood のカード名・カード文面・ロゴ・アート・ルール文書は **Legend Story Studios（LSS）** の知的財産である。
- LSS の **Terms of Use for Game and Studio Assets and IP**（`https://fabtcg.com/resources/terms-of-use-for-game-and-studio-assets-and-ip/`）は、非商用・無料で公式と誤認されないコミュニティ向けツール／サービス・ファンプロジェクトへの取り消し可能な利用許諾を定めている。
- 本リポジトリでは以下を遵守する：
  - **免責文の表示**: リポジトリ直下の `README.md` に、公式非提携・非承認であることおよび `© Legend Story Studios` の帰属表記を明記する。
  - **`NOTICE` の設置**: コードライセンス（Apache-2.0 等）はソースコードにのみ適用され、カード名・カードテキスト・ルール文書は LSS の著作物でありライセンス対象外であることを明記する。
  - **非商用・無料** として運用し、直接課金・有料提供は行わない。
  - **カードアート画像およびフレーバーテキストは取り扱わない**（形式化に必要なルール上の特性・テキストのみを扱う）。

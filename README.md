# lean-tractatus-logico-philosophicus

ウィトゲンシュタイン『論理哲学論考』(1921)を Lean 4 で形式化する試み。

論考の命題を Lean の定義と定理として書き、証明を Lean に機械的に確かめさせる。論考は全部を形式化できる本ではないので、**全 526 命題について「どう形式化したか」「なぜ形式化しなかったか」を一つ残らず記録する**ことを完全さの基準にしている。形式化は論考そのものの再現ではなく一つの読み方(モデル化)なので、論考とのずれも命題ごとに日本語で記録している。

## 対応状況(2026-11-06)

| 状態 | 数 | 中身 |
|---|---|---|
| 形式化済み | 218 | Lean で定義・定理として書き、証明が通っている |
| この読みでは不成立 | 2 | 5.152(確率)、6.3751(色)。ここで置いた読み方のもとでは成り立たないことを証明した |
| 未着手(保留) | 9 | 量化つきの同一性の消去(段階 4c)と、対象が無限個の場合(4d)。重いので後回し |
| 対象外 | 297 | 形式化しない命題(倫理・神秘・解明など)と、設計の根拠として使った命題 |

段階ごとの範囲:

| 段階 | 範囲 | 命題数 |
|---|---|---|
| 1 | 世界と事実、対象と事態、論理空間、像の意味と真偽、真理可能性と真理関数、帰結 | 80 |
| 2 | 操作と形式列、N 演算子、命題の一般形式、論理の命題、数 | 63 |
| 3 | 名前と像の構造、命題記号と思考、内的性質、確率、色の排除 | 66 |
| 4a | 対象が有限個の場合の量化と N 演算子 | 5 |
| 4b | 同一性の記号(量化なし) | 6 |

### 主な結果

- **N 演算子の表現力**(5.5、4.5):要素命題が有限個なら、どの真理関数も N の繰り返しで作れ、N で作った命題はみな真理関数である
- **量化の N への翻訳**(5.52):対象が有限個で全てに名前があれば、量化を含む命題は N と要素命題だけの命題に意味を変えずに書き換えられる
- **同一性の記号の消去**(5.53):量化のない範囲で、同じ対象を指す名前を一つに揃えれば、同一性の記号は要らない
- **独立性の役割**:多くの結論は事態の独立性(2.061)に依存し、独立性を外すと成り立たないことを反例のモデルで示した(2.062、2.225、6.37、6.375)
- **不成立の 2 命題**:真理項を共有しない命題どうしの確率は一般には 1/2 にならない(5.152)。色の命題を要素命題とみなすと、色の排除は論理的不可能性にならない(6.3751)

詳しくは成果のまとめ `correspondence/README.md` を参照。

## どこから読むか

| 読みたいもの | 場所 |
|---|---|
| 全体の結果と限界 | `correspondence/README.md` |
| 命題ごとの記録(Lean で何を言ったか、論考とのずれ) | `correspondence/stage1.md` 〜 `stage4b.md` |
| Lean のコード | `Tractatus/`(下の「構成」) |
| 全命題の分類と、形式化しなかった理由 | `analysis/reading/classification.tsv`、`analysis/reading/README.md` |
| 解釈が分かれる論点と、ここでの扱い | `analysis/interpretation.md` |
| 形式化の方針、進め方 | `docs/policy.md`、`docs/roadmap.md` |

記録は日本語、Lean のコード・docstring は英語で書いている。記録には原文を載せていない(下の「本文について」)。

## 構成

| ファイル | 中身 |
|---|---|
| `Tractatus/LogicalSpace.lean`、`Facts.lean` | 世界・現実・論理空間、事実 |
| `Tractatus/Objects.lean` | 対象と事態、対象の形式 |
| `Tractatus/TruthPossibility.lean`、`Picture.lean`、`Consequence.lean` | 真理可能性と真理関数、像の意味と真偽、帰結 |
| `Tractatus/Operation.lean`、`GeneralForm.lean`、`Logic.lean` | 操作と数、N 演算子と命題の一般形式、論理の命題 |
| `Tractatus/Names.lean`、`Internal.lean`、`Probability.lean`、`Colour.lean` | 名前と像の構造、内的性質、確率、色の排除 |
| `Tractatus/Generality.lean`、`Identity.lean` | 量化、同一性の記号 |
| `Tractatus/Models/` | 主張が矛盾しないことのモデルと、反例 |
| `Tractatus/Meta.lean` | 命題番号の札 `@[tlp "2.062"]` |
| `tools/` | 検査(`lake test`)、本文データの生成、読む用の版の生成 |

宣言に付いた札 `@[tlp "番号"]` が、その宣言がどの命題を形式化したものかを示す。`@[tlp_refutes "番号"]` は「この読みでは不成立」の証明。

## 動かし方

必要なもの:[mise](https://mise.jdx.dev/)(Lean のツールチェーン管理 elan を入れるのに使う)。Lean と Mathlib の版は `lean-toolchain` と `lakefile.toml` で固定している(Lean v4.35.0)。

```bash
mise trust && mise install   # elan と lean / lake のプロキシを入れる
lake exe cache get           # Mathlib のビルド済みキャッシュを取る(初回だけ。省くとビルドに時間がかかる)
lake build                   # 全体をビルドする(= 全ての証明を検査する)
```

`lake build` が通れば、全ての証明が Lean に確かめられたことになる。

### 検査と、原文と並べて読む版

`lake test`(分類表・札・記録の形式などの検査と、全命題の状態の一覧)と、原文を差し込んだ記録の生成には、本文データが要る。本文データは git に入れていないので、手元で作る(手順は `source/README.md`)。

```bash
# source/README.md の手順で .cache/gutenberg/5740-t.tex を置いてから
lake exe extract-source .cache/gutenberg/5740-t.tex source
lake test                          # 検査と、全命題の状態の一覧(out/coverage.md)
lake exe render-correspondence 4a  # 原文入りの記録を out/correspondence/stage4a.md に作る(段階は 1、2、3、4a、4b)
```

## 本文について

本文の出典は、ドイツ語原文(1921)と C. K. Ogden 英訳(1922)だけを使う。どちらも public domain。日本語訳や Pears/McGuinness 訳など著作権のある訳は使っていない。本文データそのものはリポジトリに入れず、Project Gutenberg #5740 から手元で再生成する。記録や docstring の中の引用は、短い命題や一句に限っている(`lake test` が 15 語以上の一致を検査する)。

## ライセンス

- Lean のコード、ツール、設定ファイル:MIT License(`LICENSE`)
- 日本語の対応記録、分析、方針などの文書:CC BY 4.0(`LICENSE-docs.md`)
- 引用している『論理哲学論考』の本文(ドイツ語原文、Ogden 英訳)は public domain

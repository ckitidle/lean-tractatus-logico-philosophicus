# source/ — 論考の本文データ

フェーズ A(本文の整備)の成果物。以後の作業(読解ノート、整合性チェック、対応記録)はすべてここを参照元にする。

**本文データは git で管理しない**。public domain だが、本文そのものを GitHub に上げない方針(2026-11-06 にユーザーが決定)。git に入っているのはこの README だけで、`tractatus.json` などは手元で再生成する(`.gitignore` 済み)。過去のコミットからも取り除いてある。

```bash
# 1. Gutenberg の LaTeX ソースを、git 管理外の .cache/ に置く(初回だけ)
mkdir -p .cache/gutenberg
curl -fsSL -o .cache/gutenberg/5740-t.tex https://www.gutenberg.org/files/5740/5740-t/5740-t.tex
shasum -a 256 .cache/gutenberg/5740-t.tex   # 下の SHA-256 と一致すること

# 2. 本文データを生成して検査する
lake exe extract-source .cache/gutenberg/5740-t.tex source
lake test
```

本文の扱いの線引き:

- 本文の全体や長い引用は commit しない(本文データを git 管理外にしているのはこのため)。Lean の docstring や対応記録に、短い命題や一句を引用するのはよい
- 私たちが書く解説の中の短い断片(`~~p=p` のような式や、一語・一句の引用)は残してよい
- `lake test` が機械的に検査する:commit するファイル(`Tractatus/`、`tools/`、`correspondence/`、`analysis/`、`docs/`、README・CLAUDE.md)に、本文と15語以上連続して一致する箇所があればエラー(1文字の語=式の記号は数えない)。短い命題や一句の引用はよい

## ファイル

| ファイル | 中身 |
|---|---|
| `tractatus.json` | 正本。前付け(献辞・モットー)、序文、命題 526 個の英独対訳 |
| `tractatus-en.md` / `tractatus-de.md` | `tractatus.json` から生成した読む用の Markdown。手で編集しない |

`tractatus.json` の命題1つ分の形:

```json
{
  "number": "2.0121",
  "en": { "text": "...", "latex": "...", "page": "037", "footnotes": [...], "figures": [...], "typos": [...] },
  "de": { ... }
}
```

- `text`:LaTeX をプレーンテキスト(Markdown)に変換したもの。比較や引用にはこれを使う
- `latex`:Gutenberg の LaTeX をそのまま切り出したもの。元のファイルと突き合わせるための正本
- `page`:その命題が始まるページの、元のスキャン画像の番号(Gutenberg の校正用の印 `% -----File: 037.png---` から取ったもの)
- `typos`:Gutenberg の校正者が直した誤植。`original`(1922 年版の表記)と `corrected`(訂正後)の対。`text` は訂正後で作っている
- `footnotes` / `figures`:脚注と図版(図版は名前だけ。画像は入れていない)

## 出典

- Project Gutenberg eBook #5740 の LaTeX ソース `5740-t.tex`
  - URL:<https://www.gutenberg.org/files/5740/5740-t/5740-t.tex>
  - 取得日:2026-11-06
  - SHA-256:`52158eed80f03552c257e22dca26e1684588814554481242be94063ce9c6061f`
- 底本:C. K. Ogden 訳の英独対訳版(London: Kegan Paul, Trench, Trubner, 1922)
- ドイツ語原文と Ogden 訳はどちらも public domain。Gutenberg のライセンス文と商標表記は含めていない(public domain の本文だけを使う場合は不要)
- **含めていないもの**:Russell の序文(Russell は 1970 年没で日本では保護期間内)、Gutenberg の定型文
- 元の `.tex` は Russell の序文を含むので、リポジトリには入れていない

## 検査

`lake test`(`tools/TlpTest.lean`)が最初に行う、本文データの検査の内容(`tools/CheckSource.lean`):

- すべての命題に、正しい書式の番号と、空でない英語・ドイツ語の本文がある
- 番号に重複がなく、Wittgenstein の順序(`2 < 2.01 < 2.011 < 2.02 < 2.1`)で並んでいる
- 番号の親子関係が成り立つ:番号の最後の桁を落とし、末尾の 0 も落としたもの(`2.0121` → `2.012`、`2.01` → `2`)が実在する。成り立たない番号は `numbering-exceptions.txt` に列挙する決まりだが、1922 年版では**例外はゼロ**だった

## 変換の決まり

- 強調(`\emph`、ドイツ語側の隔字体 `\Emph`)は `*...*`
- 引用符は “…”(英語)と „…“(ドイツ語)
- 論理記号は 1922 年版の Russell 式の記法のまま Unicode にする:`~`(否定)、`.`(連言)、`∨`、`⊃`、`≡`、`|`。`p̄` のような上線は結合文字(U+0304)
  - 原本では論理和が小文字の `v` だったのを、Gutenberg 版が `∨` に置き換えている
- 真理表など(`tabular`、`array`、`gather*`、`\[ \]`)と、`\sum`・`\binom`・`\frac` を含む数式は、LaTeX のまま残す(` ```latex ` のブロックと `$...$`)
- 図版は `[Figure: cube]` のように名前だけ残す(5.5423、5.6331、6.1203、6.36111)
- 脚注は `[^1]` で参照する(1 と 6.32 付近)

## 版についての注意

本文が正しいかを独立した版と突き合わせた記録は `analysis/source-check.md`。

- これは **1922 年の初刷**の本文。1933 年の第2刷では、Wittgenstein による訂正がドイツ語原文と英訳の両方に入っている。第2刷との違いは調べていない。形式化の対象になる命題で違いが問題になりそうなときに、個別に調べる
- 1922 年版の中でも誤植がある。Gutenberg の校正者が直した箇所は `typos` に記録されている

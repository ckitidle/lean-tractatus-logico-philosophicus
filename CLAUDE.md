# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project concept

ウィトゲンシュタイン『論理哲学論考』を Lean 4 で形式化する。
進め方は `docs/roadmap.md`(フェーズ A〜F と整合性チェック)。
形式化の方針(範囲・表現・命名・検査)は `docs/policy.md`。
その根拠は `analysis/reading/`(全命題の分類)と `analysis/interpretation.md`(解釈の分かれ目)。
フェーズ・段階の区切りでは、`docs/roadmap.md` の「区切りの手順」(機械的検証、自己レビュー、ユーザーのレビュー、記録)を必ず行う。

- 本文の出典はドイツ語原文と C. K. Ogden 英訳(1922)だけ。日本語訳・Pears/McGuinness 訳・Russell の序文は著作権があるので使わない
- 本文は public domain だが GitHub に上げない。`source/tractatus.json` などの本文データは git 管理外で、`.cache/gutenberg/5740-t.tex` から手元で再生成する(`source/README.md`)。commit するファイル(Lean の docstring、対応記録など)にも本文の全体や長い引用(15語以上)を入れない。短い命題や一句の引用はよい
- Lean の実装(コード・docstring・識別子)は英語。ドキュメントと会話は日本語

## Toolchain

- **mise** が固定するのは elan(Lean のツールチェーン管理)だけ。`.mise.toml` を参照
  - mise のレジストリに lean / elan は無いので `github:leanprover/elan` バックエンドで入れ、
    postinstall の `elan-init` で `~/.elan/bin` に `lean` / `lake` のプロキシを置いている
- **Lean 本体の版は `lean-toolchain`** が決める。elan がこのファイルを読んで自動で取得する。
  版を上げるときはこのファイルだけを書き換える(Mathlib を入れたら Mathlib の版に揃える)
- Mathlib は `lakefile.toml` の `[[require]]` で、`lean-toolchain` に対応するリリース版のタグ(今は `v4.35.0`)に固定している
  (master は Lean の開発版前提なので使わない)。版を上げるときは `lean-toolchain` と `rev` を揃えて変え、
  `lake update mathlib` のあと `lake exe cache get` でビルド済みキャッシュを取る

clone 直後:

```bash
mise trust && mise install   # elan と ~/.elan/bin のプロキシ
lake build                   # lean-toolchain の版を elan が自動で入れてからビルド
```

## Commands

```bash
lake build                          # ライブラリ全体をビルド(型検査 = 証明の検査)
lake env lean Tractatus/LogicalSpace.lean  # 1ファイルだけ検査
lake test                           # 本文データ・分類表・形式化の検査と、全命題の状態の一覧(先に lake build が要る)
lake test -- --strict               # 上に加えて未完成(sorry)をエラーにする。段階の締めくくりで使う
lake exe extract-source .cache/gutenberg/5740-t.tex source  # 本文データの再生成(git 管理外。source/README.md)
lake exe render-review 1             # 段階 1 の分類のレビュー一覧を out/review/stage1.md に生成(原文入り、git 管理外)
lake exe render-correspondence 1     # correspondence/stage1.md に原文を差し込んだ版を out/correspondence/ に生成
```

作成中に必要な検査は、ローカルの `lake build` と `lake test` だけで行う(CI は置いていない)。
`lake test` は全命題の状態を `out/coverage.md` に書き出す(`docs/policy.md` §6.1)。

- Lake でハイフンを含む実行ファイル名を `testDriver` などから参照するときは `«tlp-test»` と書く
- 命題番号の札は `@[tlp "2.062"]` / `@[tlp_refutes "6.3751"]`(`Tractatus/Meta.lean`)。札は `Tractatus.Meta.tags.*` という補助の定義として記録され、`tools/TlpTest.lean` がそれを読む。`Tractatus/Meta.lean` には Mathlib を import しない
- `tools/` の共通部分(`CheckSource`)は lean_lib `TractatusTools` に入れてある。どのライブラリにも属さないモジュールを実行ファイルから import すると、lake が作り直さず古いビルド成果物を読むことがある
- Mathlib は Lean のモジュール方式で書かれていて、こちらのファイルは旧来の書き方なので、import すると警告が出る。動作には影響しないので、今は旧来の書き方のままにしている

## Layout

- `lakefile.toml` — Lake の設定。ライブラリ名は `Tractatus`
- `Tractatus.lean` — ライブラリのルート。新しいモジュールはここで import する
- `Tractatus/` — 本体。`Meta.lean`(命題番号の札)、`LogicalSpace.lean`(世界・現実・論理空間)、`Facts.lean`(事実)、`Objects.lean`(対象と事態)、`TruthPossibility.lean`(真理可能性・真理関数)、`Picture.lean`(像の意味と真偽)、`Consequence.lean`(帰結)、`Models/`(モデルと反例)
- Mathlib の `Set.sUnion`(記法 `⋃₀`)などは、`Mathlib.Order.SetNotation` を直接 import しないと見えないことがある(モジュール方式の影響)
- `tools/` — 補助ツール(`extract-source`、`tlp-test`(= lake test)、`render-review`、`render-correspondence`)。ライブラリとは別の実行ファイル
- `source/` — 論考の本文データ(英独対訳)。出典と変換の決まりは `source/README.md`
- `docs/` — 方針だけ(`roadmap.md` 進め方、`policy.md` 形式化の方針)
- `analysis/` — 読んで調べた結果。手書きで作り直せないので git で管理する(分類表、解釈の記録、本文の突き合わせ)
- `correspondence/` — 日本語の対応記録(成果物)。段階ごとに `stage<N>.md`。原文は書かない
- `out/` — スクリプトで作り直せる生成物(git 管理外)

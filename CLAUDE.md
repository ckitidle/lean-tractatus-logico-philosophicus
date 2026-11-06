# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project concept

ウィトゲンシュタイン『論理哲学論考』を Lean 4 で形式化する。
進め方は `docs/roadmap.md`(フェーズ A〜F と整合性チェック)。
形式化の方針(範囲・表現・命名・検査)は `docs/policy.md`。
その根拠は `analysis/reading/`(全命題の分類)と `analysis/interpretation.md`(解釈の分かれ目)。
フェーズ・段階の区切りでは、`docs/roadmap.md` の「区切りの手順」(機械的検証、自己レビュー、ユーザーのレビュー、記録)を必ず行う。

- 本文の出典はドイツ語原文と C. K. Ogden 英訳(1922)だけ。日本語訳・Pears/McGuinness 訳・Russell の序文は著作権があるので使わない
- 本文は public domain だが GitHub に上げない。`source/tractatus.json` などの本文データは git 管理外で、`.cache/gutenberg/5740-t.tex` から手元で再生成する(`source/README.md`)。commit するファイル(Lean の docstring、対応記録など)にも本文を丸ごと・長く引用しない
- Lean の実装(コード・docstring・識別子)は英語。ドキュメントと会話は日本語

## Toolchain

- **mise** が固定するのは elan(Lean のツールチェーン管理)だけ。`.mise.toml` を参照
  - mise のレジストリに lean / elan は無いので `github:leanprover/elan` バックエンドで入れ、
    postinstall の `elan-init` で `~/.elan/bin` に `lean` / `lake` のプロキシを置いている
- **Lean 本体の版は `lean-toolchain`** が決める。elan がこのファイルを読んで自動で取得する。
  版を上げるときはこのファイルだけを書き換える(Mathlib を入れたら Mathlib の版に揃える)
- Mathlib はまだ入れていない(パイロットで入れる)。`lakefile.toml` に `[[require]]` を足し、
  `rev` には `lean-toolchain` に対応するリリース版のタグを指定する(master は Lean の開発版前提なので使わない)。
  `lake exe cache get` でビルド済みキャッシュを取る

clone 直後:

```bash
mise trust && mise install   # elan と ~/.elan/bin のプロキシ
lake build                   # lean-toolchain の版を elan が自動で入れてからビルド
```

## Commands

```bash
lake build                          # ライブラリ全体をビルド(型検査 = 証明の検査)
lake env lean Tractatus/Basic.lean  # 1ファイルだけ検査
lake test                           # 本文データ source/tractatus.json の検査(check-source)
lake exe extract-source .cache/gutenberg/5740-t.tex source  # 本文データの再生成(git 管理外。source/README.md)
lake exe render-review 1             # 段階 1 の分類のレビュー一覧を out/review/stage1.md に生成(原文入り、git 管理外)
```

作成中に必要な検査は、ローカルの `lake build` と `lake test` だけで行う(CI は置いていない)。

Lake でハイフンを含む実行ファイル名を `testDriver` などから参照するときは `«check-source»` と書く。

## Layout

- `lakefile.toml` — Lake の設定。ライブラリ名は `Tractatus`
- `Tractatus.lean` — ライブラリのルート。新しいモジュールはここで import する
- `Tractatus/` — 本体
- `tools/` — 補助ツール(`extract-source`、`check-source`、`render-review`)。ライブラリとは別の実行ファイル
- `source/` — 論考の本文データ(英独対訳)。出典と変換の決まりは `source/README.md`
- `docs/` — 方針だけ(`roadmap.md` 進め方、`policy.md` 形式化の方針)
- `analysis/` — 読んで調べた結果。手書きで作り直せないので git で管理する(分類表、解釈の記録、本文の突き合わせ)
- `correspondence/` — 日本語の対応記録(成果物。パイロット以降に作る)
- `out/` — スクリプトで作り直せる生成物(git 管理外)

# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project concept

ウィトゲンシュタイン『論理哲学論考』を Lean 4 で形式化する。
進め方は `docs/roadmap.md`(フェーズ A〜F と整合性チェック)。
何をどこまで形式化するかは、フェーズ D で `docs/policy.md` に決める。

- 本文の出典はドイツ語原文と C. K. Ogden 英訳(1922)だけ。日本語訳・Pears/McGuinness 訳・Russell の序文は著作権があるので使わない
- Lean の実装(コード・docstring・識別子)は英語。ドキュメントと会話は日本語

## Toolchain

- **mise** が固定するのは elan(Lean のツールチェーン管理)だけ。`.mise.toml` を参照
  - mise のレジストリに lean / elan は無いので `github:leanprover/elan` バックエンドで入れ、
    postinstall の `elan-init` で `~/.elan/bin` に `lean` / `lake` のプロキシを置いている
- **Lean 本体の版は `lean-toolchain`** が決める。elan がこのファイルを読んで自動で取得する。
  版を上げるときはこのファイルだけを書き換える(Mathlib を入れたら Mathlib の版に揃える)
- Mathlib はまだ入れていない。必要になったら `lakefile.toml` に `[[require]]` を足し、
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
```

`.github/workflows/lean_action_ci.yml` が push と PR で `leanprover/lean-action` を走らせる。

## Layout

- `lakefile.toml` — Lake の設定。ライブラリ名は `Tractatus`
- `Tractatus.lean` — ライブラリのルート。新しいモジュールはここで import する
- `Tractatus/` — 本体

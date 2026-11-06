# lean-tractatus-logico-philosophicus

ウィトゲンシュタイン『論理哲学論考』を Lean 4 で形式化する試み。

- 成果のまとめ:`correspondence/README.md`(全 526 命題の扱い、主な結果、限界)
- 命題ごとの日本語の対応記録:`correspondence/stage*.md`
- 方針と進め方:`docs/policy.md`、`docs/roadmap.md`
- 本文(ドイツ語原文と Ogden 英訳、public domain)はリポジトリに入れていない。手元での再生成は `source/README.md`

## Setup

```bash
mise trust && mise install
lake build
```

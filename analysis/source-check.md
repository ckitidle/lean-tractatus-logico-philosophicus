# 本文の突き合わせの記録

`source/tractatus.json`(Project Gutenberg #5740 から生成。出典と再生成の手順は `source/README.md`)の本文が正しいかを確かめた記録。

## 独立した版との突き合わせ(2026-11-06)

Gutenberg 版とは別に作られた、1922 年版のスキャンの OCR テキストと突き合わせた。

- 比較に使った版:archive.org `in.ernet.dli.2015.221720`(Digital Library of India による 1922 年版のスキャン)の `2015.221720.Tractatus-Logico_djvu.txt`
- 方法:OCR を段落に分けて言語別に振り分け、`tractatus.json` の `text` と単語の並びを `difflib` で揃えて差分を出し、全件を目で確認した。使い捨ての分析なので、スクリプトはリポジトリに入れていない
- 一致率:英語 96.9%、ドイツ語 86.7%(ドイツ語はウムラウトの誤認識が多い)
- 結果:**未記録の違いはなかった**
  - 小さな差分(英語 374 箇所、ドイツ語 1540 箇所)は、OCR の誤認識(`feet`←fact、`fiir`←für など)か、`typos` に記録済みの誤植訂正だった
  - 誤植訂正の箇所(4.2211 atomatic→atomic、5.234 proposition→propositions、5.541 epistomology→epistemology、5.513 nichtssagt→nichts sagt など)では、OCR 側に 1922 年版の元の表記が出ていて、記録と一致した
  - 大きな差分(5語以上の欠落)は、OCR を言語別に振り分けるときに短い段落が漏れたことによるもので、該当する文はすべて OCR テキストの中に実在した
- この方法の限界:数式や真理表は比較から外している(OCR がほとんど読めていないため)。数式の正しさは Gutenberg の校正に頼っている

## 数式を含む命題で見つかった食い違い

- 4.1252:英訳(1922)の式はドイツ語原文と食い違う。詳しくは `analysis/reading/README.md` の「読んでいて見つかったこと」

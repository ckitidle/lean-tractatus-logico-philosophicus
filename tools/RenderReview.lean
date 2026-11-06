import Lean.Data.Json

/-!
# render-review

Renders a review sheet (in Japanese) for one stage of docs/policy.md §2: every proposition
whose `stage` in `analysis/reading/classification.tsv` is the given stage, with the Ogden
text from `source/tractatus.json`, its kind, confidence, contested topic and rationale.

The sheet contains the source text, so it is written to `out/` (not tracked by git).

Usage: `lake exe render-review <stage> [out-file]` (default `out/review/stage<stage>.md`)
-/

open Lean

namespace RenderReview

structure Row where
  number : String
  kind : String
  stage : String
  scopeNote : String
  confidence : String
  contested : String
  related : String
  rationale : String
  deriving Inhabited

def readRows (path : String) : IO (Array Row) := do
  let lines := ((← IO.FS.readFile path).splitOn "\n").drop 1 |>.filter (· ≠ "")
  let mut rows := #[]
  for l in lines do
    match l.splitOn "\t" with
    | [n, k, s, sn, c, ct, _concepts, rel, r] =>
      rows := rows.push ⟨n, k, s, sn, c, ct, rel, r⟩
    | _ => throw <| IO.userError s!"{path}: malformed row: {l}"
  return rows

def kindLabel : String → String
  | "def" => "定義"
  | "claim" => "主張(公理の候補)"
  | "conseq" => "帰結(定理の候補)"
  | "notation" => "記法"
  | "elucid" => "解明・比喩"
  | "out" => "対象外"
  | k => k

def confLabel : String → String
  | "high" => "高"
  | "mid" => "中"
  | "low" => "低"
  | c => c

/-- Quote a (possibly multi-line) text as a Markdown block quote. -/
def blockquote (t : String) : String :=
  "\n".intercalate ((t.splitOn "\n").map fun l => if l.isEmpty then ">" else "> " ++ l)

def isFlagged (r : Row) : Bool := r.contested != "-" || r.confidence == "low"

def entry (texts : Std.HashMap String String) (topics : Std.HashMap String String) (r : Row) :
    String :=
  let flags := (if r.contested != "-" then [s!"論点: {topics.getD r.contested r.contested}"] else []) ++
    (if r.confidence == "low" then ["確信度が低い"] else [])
  let flagStr := if flags.isEmpty then "" else s!"  ★ {", ".intercalate flags}"
  s!"### {r.number}{flagStr}\n\n" ++
  blockquote (texts.getD r.number "(本文なし)") ++ "\n\n" ++
  s!"- **種別**:{kindLabel r.kind}(確信度 {confLabel r.confidence})\n" ++
  s!"- **理由**:{r.rationale}\n" ++
  (if r.scopeNote != "-" then s!"- **扱い**:{r.scopeNote}\n" else "") ++
  s!"- **関連**:{r.related}\n"

def run (stage outPath : String) : IO UInt32 := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "source/tractatus.json"))
  let props ← IO.ofExcept (json.getObjValAs? (Array Json) "propositions")
  let mut texts : Std.HashMap String String := {}
  for p in props do
    let n ← IO.ofExcept (p.getObjValAs? String "number")
    let en := p.getObjValD "en"
    let t ← IO.ofExcept (en.getObjValAs? String "text")
    -- append footnotes so that `[^1]` markers resolve
    let notes := (en.getObjValAs? (Array String) "footnotes").toOption.getD #[]
    let mut full := t
    let mut i := 0
    for f in notes do
      i := i + 1
      full := full ++ s!"\n\n[^{i}]: {f}"
    texts := texts.insert n full
  -- Japanese titles of the contested topics
  let mut topics : Std.HashMap String String := {}
  for l in ((← IO.FS.readFile "analysis/reading/contested.tsv").splitOn "\n").drop 1 do
    match l.splitOn "\t" with
    | id :: title :: _ => topics := topics.insert id title
    | _ => pure ()
  let rows ← readRows "analysis/reading/classification.tsv"
  let inStage := rows.filter (·.stage == stage)
  if inStage.isEmpty then
    IO.eprintln s!"error: no propositions with stage '{stage}'"
    return 1
  -- propositions marked `out` that sit between two propositions of this stage:
  -- metaphors, examples etc. inside the stage's text, to skim for hidden content
  let mut skim : Array Row := #[]
  for i in [0:rows.size] do
    let r := rows[i]!
    if r.stage != "out" then continue
    let prev := (rows.extract 0 i).reverse.find? (·.stage != "out")
    let next := (rows.extract (i + 1) rows.size).find? (·.stage != "out")
    if prev.map (·.stage) == some stage && next.map (·.stage) == some stage then
      skim := skim.push r
  let flagged := inStage.filter isFlagged
  let mut out := s!"# 段階 {stage} の分類のレビュー\n\n"
  out := out ++ "<!-- lake exe render-review で生成。原文を含むので git 管理外(out/)。手で編集しない -->\n\n"
  out := out ++ s!"段階 {stage} で形式化する命題 {inStage.size} 個について、Claude が付けた分類を並べた。" ++
    "原文は Ogden 訳(1922)。見てほしいのは次の3点:\n\n" ++
    "1. **種別**は合っているか(定義/主張/帰結/記法)。主張は「Wittgenstein の仮定」として、帰結は「そこから証明する定理」として扱う\n" ++
    "2. **理由**に書いた読み方でよいか。形式化はこの読み方に沿って行う\n" ++
    "3. **抜け**はないか。末尾の「流し見」の命題(比喩・例示として形式化しないもの)に、形式化すべき内容が隠れていないか\n\n" ++
    "気づいたことは、命題番号と一緒に会話で伝えてもらえれば、分類表(analysis/reading/classification.tsv)に反映する。\n\n"
  out := out ++ s!"## 特に見てほしい命題({flagged.size} 個)\n\n" ++
    "解釈が分かれる論点が付いているか、Claude の確信度が低いもの:" ++
    " " ++ ", ".intercalate (flagged.toList.map (·.number)) ++ "\n\n"
  out := out ++ s!"## 命題(番号順)\n\n"
  for r in inStage do
    out := out ++ entry texts topics r ++ "\n"
  out := out ++ s!"## 流し見:段階 {stage} の範囲にある、形式化しない命題({skim.size} 個)\n\n"
  for r in skim do
    let t := texts.getD r.number ""
    let short := if t.length > 160 then (t.take 160).toString ++ "…" else t
    out := out ++ s!"- **{r.number}**({kindLabel r.kind}){short.replace "\n" " "}\n  - 理由:{r.rationale}\n"
    if r.scopeNote != "-" then
      out := out ++ s!"  - 形式化しない理由:{r.scopeNote}\n"
  let dir := (System.FilePath.mk outPath).parent.getD "."
  IO.FS.createDirAll dir
  IO.FS.writeFile outPath out
  IO.println s!"wrote {outPath} ({inStage.size} propositions, {flagged.size} flagged, {skim.size} to skim)"
  return 0

end RenderReview

def main (args : List String) : IO UInt32 := do
  match args with
  | [stage] => RenderReview.run stage s!"out/review/stage{stage}.md"
  | [stage, path] => RenderReview.run stage path
  | _ =>
    IO.eprintln "usage: lake exe render-review <stage> [out-file]"
    return 2

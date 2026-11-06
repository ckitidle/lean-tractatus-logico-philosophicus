import Lean.Data.Json

/-!
# render-correspondence

Renders a reader's version of `correspondence/stage<N>.md`: after every heading
`### <number>`, the English (Ogden) and German texts of that proposition are inserted from
`source/tractatus.json`. The output contains the source text, so it is written to `out/`
(not tracked by git).

Usage: `lake exe render-correspondence <stage>`
-/

open Lean

namespace RenderCorrespondence

def blockquote (t : String) : String :=
  "\n".intercalate ((t.splitOn "\n").map fun l => if l.isEmpty then ">" else "> " ++ l)

def run (stage : String) : IO UInt32 := do
  let inPath := s!"correspondence/stage{stage}.md"
  let outPath := s!"out/correspondence/stage{stage}.md"
  unless ← System.FilePath.pathExists inPath do
    IO.eprintln s!"error: {inPath} not found"
    return 1
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "source/tractatus.json"))
  let props ← IO.ofExcept (json.getObjValAs? (Array Json) "propositions")
  let mut texts : Std.HashMap String (String × String) := {}
  for p in props do
    let n ← IO.ofExcept (p.getObjValAs? String "number")
    let en ← IO.ofExcept ((p.getObjValD "en").getObjValAs? String "text")
    let de ← IO.ofExcept ((p.getObjValD "de").getObjValAs? String "text")
    texts := texts.insert n (en, de)
  let mut out := "<!-- lake exe render-correspondence で生成。原文を含むので git 管理外(out/)。手で編集しない -->\n\n"
  let mut count := 0
  for line in (← IO.FS.readFile inPath).splitOn "\n" do
    out := out ++ line ++ "\n"
    if line.startsWith "### " then
      let n := (line.drop 4).trimAscii.toString
      match texts.get? n with
      | some (en, de) =>
        count := count + 1
        out := out ++ "\n**原文(Ogden 訳、1922)**\n\n" ++ blockquote en ++
          "\n\n**原文(ドイツ語)**\n\n" ++ blockquote de ++ "\n"
      | none =>
        IO.eprintln s!"error: {inPath}: unknown proposition number in heading '{line}'"
        return 1
  IO.FS.createDirAll "out/correspondence"
  IO.FS.writeFile outPath out
  IO.println s!"wrote {outPath} ({count} propositions)"
  return 0

end RenderCorrespondence

def main (args : List String) : IO UInt32 := do
  match args with
  | [stage] => RenderCorrespondence.run stage
  | _ =>
    IO.eprintln "usage: lake exe render-correspondence <stage>"
    return 2

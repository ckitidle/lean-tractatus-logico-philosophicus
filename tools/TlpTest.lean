import Lean
import CheckSource

/-!
# tlp-test (`lake test`)

1. Checks the source text and the classification table (tools/CheckSource.lean).
2. Loads the compiled `Tractatus` library, collects the links made by `@[tlp ...]` and
   `@[tlp_refutes ...]` (auxiliary definitions of type `Tractatus.Meta.Tag`), and checks
   them against analysis/reading/classification.tsv (docs/policy.md §4, §6):
   * the proposition number exists and the proposition is scheduled for formalization,
   * the declarations have the kind required by the classification,
   * no axioms beyond `propext`, `Classical.choice`, `Quot.sound` (and `sorryAx`, which
     marks an incomplete proof).
3. Reports the status of every proposition (formalized / incomplete / fails under our
   reading / not started / out of scope): a summary on the terminal and the full list in
   `out/coverage.md` (not tracked by git).

The test fails only on mistakes in how the formalization is put together. Incomplete
proofs fail it only with `--strict` (used when closing a stage).

Usage: `lake build && lake test [-- --strict]`
-/

open Lean

namespace TlpTest

structure Tag where
  decl : Name
  number : String
  refutes : Bool

/-- Decode the value of an auxiliary `Tractatus.Meta.Tag` definition. -/
def decodeTag (v : Expr) : Option Tag :=
  match v.getAppArgs with
  | #[.lit (.strVal d), .lit (.strVal n), b] =>
    let refutes := b.isConstOf ``Bool.true
    some ⟨d.toName, n, refutes⟩
  | _ => none

/-- Axioms that a declaration depends on, transitively. -/
def axiomsOf (env : Environment) (n : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[n]
  let mut axs : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    match env.find? c with
    | some (.axiomInfo _) => axs := axs.push c
    | some ci =>
      for d in ci.type.getUsedConstants do stack := stack.push d
      if let some v := ci.value? (allowOpaque := true) then
        for d in v.getUsedConstants do stack := stack.push d
      if let .inductInfo i := ci then
        for d in i.ctors do stack := stack.push d
    | none => pure ()
  return axs

/-- The body of a type after all its `∀`/`→` binders. -/
partial def forallBody : Expr → Expr
  | .forallE _ _ b _ => forallBody b
  | e => e

inductive DeclKind where
  | theorem | propDef | dataDef | other
  deriving BEq

def DeclKind.label : DeclKind → String
  | .theorem => "theorem"
  | .propDef => "Prop を値とする定義"
  | .dataDef => "定義"
  | .other => "その他"

def declKind (ci : ConstantInfo) : DeclKind :=
  match ci with
  | .thmInfo _ => .theorem
  | .defnInfo _ | .opaqueInfo _ =>
    if forallBody ci.type == .sort .zero then .propDef else .dataDef
  | .inductInfo _ => .dataDef
  | _ => .other

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure Row where
  number : String
  kind : String
  stage : String
  scopeNote : String

def formalStages : List String := ["1", "2", "3", "4a", "4b", "4c", "4d"]
def deferredStages : List String := ["4c", "4d"]

inductive Status where
  | formalized | incomplete | refuted | notStarted | deferred | outOfScope
  deriving BEq

def Status.label : Status → String
  | .formalized => "形式化済み"
  | .incomplete => "未完成"
  | .refuted => "この読みでは不成立"
  | .notStarted => "未着手"
  | .deferred => "未着手(保留)"
  | .outOfScope => "対象外"

def kindLabel : String → String
  | "def" => "定義"
  | "claim" => "主張"
  | "conseq" => "帰結"
  | "notation" => "記法"
  | "elucid" => "解明・比喩"
  | "out" => "対象外"
  | k => k

def run (strict : Bool) : IO UInt32 := do
  -- 1. source text and classification
  let sourceCode ← CheckSource.run "source"
  -- 2. the compiled library
  let olean : System.FilePath := ".lake/build/lib/lean/Tractatus.olean"
  unless ← olean.pathExists do
    IO.eprintln "error: the library is not built. Run `lake build` before `lake test`."
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Tractatus }] {} (trustLevel := 1024)
  let mut tags : Array Tag := #[]
  for (_, ci) in env.constants.toList do
    if ci.type.isConstOf `Tractatus.Meta.Tag then
      if let some v := ci.value? then
        if let some t := decodeTag v then tags := tags.push t
  let rows : Array Row := ((← CheckSource.readTsv "analysis/reading/classification.tsv").toArray.filterMap
    fun | [n, k, s, sn, _, _, _, _, _] => some ⟨n, k, s, sn⟩ | _ => none)
  let mut errors : Array String := #[]
  -- per tagged declaration: kind and axioms
  let mut declInfo : Std.HashMap Name (DeclKind × Bool) := {}  -- kind, uses sorry
  for t in tags do
    if declInfo.contains t.decl then continue
    match env.find? t.decl with
    | none => errors := errors.push s!"{t.decl}: tagged declaration not found"
    | some ci =>
      let axs := axiomsOf env t.decl
      let usesSorry := axs.contains ``sorryAx
      for a in axs do
        if a != ``sorryAx && !allowedAxioms.contains a then
          errors := errors.push s!"{t.decl}: depends on a non-standard axiom {a}"
      declInfo := declInfo.insert t.decl (declKind ci, usesSorry)
  -- per proposition
  let mut statuses : Array (Row × Status × String) := #[]
  for r in rows do
    let ts := tags.filter (·.number == r.number)
    let note : String := ", ".intercalate (ts.toList.map fun t =>
      (if t.refutes then "反証: " else "") ++ t.decl.toString)
    if !ts.isEmpty then
      if !formalStages.contains r.stage then
        errors := errors.push s!"{r.number}: tagged ({note}) but its stage is '{r.stage}' (not scheduled for formalization)"
      let kinds := ts.filterMap fun t => if t.refutes then none else (declInfo.get? t.decl).map (·.1)
      let ok := match r.kind with
        | "def" | "notation" => kinds.any (· == .dataDef) || kinds.any (· == .propDef)
        | "claim" => kinds.any (· == .propDef)
        | "conseq" => kinds.any (· == .theorem)
        | _ => false
      let onlyRefutes := ts.all (·.refutes)
      if !ok && !onlyRefutes then
        errors := errors.push s!"{r.number}: classified as {kindLabel r.kind}, but no tagged declaration has the required kind ({note})"
      for t in ts do
        if t.refutes && (declInfo.get? t.decl).map (·.1) != some .theorem then
          errors := errors.push s!"{r.number}: {t.decl} is tagged tlp_refutes but is not a theorem"
      let incomplete := ts.any fun t => (declInfo.get? t.decl).map (·.2) == some true
      let refuted := ts.any fun t => t.refutes && (declInfo.get? t.decl).map (·.2) == some false
      let st := if refuted then Status.refuted else if incomplete then .incomplete else .formalized
      statuses := statuses.push (r, st, note)
    else if deferredStages.contains r.stage then
      statuses := statuses.push (r, .deferred, r.scopeNote)
    else if formalStages.contains r.stage then
      statuses := statuses.push (r, .notStarted, "")
    else
      let reason := if r.scopeNote != "-" then r.scopeNote else s!"種別が{kindLabel r.kind}"
      statuses := statuses.push (r, .outOfScope, reason)
  for t in tags do
    unless rows.any (·.number == t.number) do
      errors := errors.push s!"{t.decl}: tagged with unknown proposition number {t.number}"
  -- correspondence records (docs/policy.md §6 level 3): every formalized proposition has a
  -- record `### <number>` in some correspondence/stage*.md, and every record is formalized
  let mut recorded : Array String := #[]
  -- the text of each record, from its heading to the next heading
  let mut recordText : Std.HashMap String String := {}
  if ← System.FilePath.pathExists "correspondence" then
    for entry in ← System.FilePath.readDir "correspondence" do
      if entry.fileName.startsWith "stage" && entry.fileName.endsWith ".md" then
        let mut current : Option String := none
        for line in (← IO.FS.readFile entry.path).splitOn "\n" do
          if line.startsWith "### " then
            let n := (line.drop 4).trimAscii.toString
            recorded := recorded.push n
            current := some n
          else if line.startsWith "## " || line == "---" then
            current := none
          else if let some n := current then
            recordText := recordText.insert n ((recordText.getD n "") ++ line ++ "\n")
  -- every declaration named in a record (as `Tractatus.…`) exists, and every tagged
  -- declaration is named in the record of its proposition
  for (n, text) in recordText.toList do
    let pieces := (text.splitOn "`").toArray
    for i in [0:pieces.size] do
      let w := pieces[i]!
      if i % 2 == 1 && w.startsWith "Tractatus." && !w.contains '/' then
        unless env.contains w.toName do
          errors := errors.push s!"correspondence: record '{n}' names `{w}`, which does not exist"
  for t in tags do
    if let some text := recordText.get? t.number then
      unless (text.splitOn s!"`{t.decl}`").length > 1 do
        errors := errors.push s!"correspondence: record '{t.number}' does not name its tagged declaration `{t.decl}`"
  let tagged := statuses.filter (fun (_, s, _) => s == .formalized || s == .incomplete || s == .refuted)
  for (r, _, _) in tagged do
    unless recorded.contains r.number do
      errors := errors.push s!"{r.number}: formalized but has no record in correspondence/stage*.md"
  for n in recorded do
    unless tagged.any (·.1.number == n) do
      errors := errors.push s!"correspondence: record '{n}' but the proposition is not formalized"
  -- 3. report
  let count (s : Status) := (statuses.filter (·.2.1 == s)).size
  let numbersOf (s : Status) := " ".intercalate ((statuses.filter (·.2.1 == s)).toList.map (·.1.number))
  IO.println "形式化の状態:"
  for s in [Status.formalized, .incomplete, .refuted] do
    let n := count s
    IO.println s!"  {s.label}: {n}{if n > 0 then s!"  ({numbersOf s})" else ""}"
  IO.println s!"  未着手: {count .notStarted + count .deferred}  (うち保留 {count .deferred})"
  IO.println s!"  対象外: {count .outOfScope}"
  let mut md := "# 形式化の状態\n\n<!-- lake test で生成。git 管理外(out/)。手で編集しない -->\n\n"
  md := md ++ "| 状態 | 数 |\n|---|---|\n"
  for s in [Status.formalized, .incomplete, .refuted, .notStarted, .deferred, .outOfScope] do
    md := md ++ s!"| {s.label} | {count s} |\n"
  md := md ++ "\n| 番号 | 状態 | 種別 | 段階 | 対応する宣言 / 理由 |\n|---|---|---|---|---|\n"
  for (r, s, note) in statuses do
    md := md ++ s!"| {r.number} | {s.label} | {kindLabel r.kind} | {r.stage} | {note.replace "|" "\\|"} |\n"
  IO.FS.createDirAll "out"
  IO.FS.writeFile "out/coverage.md" md
  IO.println "詳細: out/coverage.md"
  for e in errors do IO.eprintln s!"error: {e}"
  let incompleteFail := strict && count .incomplete > 0
  if incompleteFail then
    IO.eprintln s!"error: --strict: {count .incomplete} propositions are incomplete"
  if sourceCode == 0 && errors.isEmpty && !incompleteFail then
    IO.println "整合性: ok"
    return 0
  else
    return 1

end TlpTest

def main (args : List String) : IO UInt32 :=
  TlpTest.run (args.contains "--strict")

import Lean.Data.Json

/-!
# check-source

Validates `source/tractatus.json`:

* every proposition has a well-formed number and non-empty English and German text;
* numbers are unique and appear in Wittgenstein's order;
* the numbering forms a tree: the *nominal parent* of a number (drop the last digit,
  then trailing zeros) exists. Numbers whose nominal parent is missing must be listed
  in `source/numbering-exceptions.txt`, and nothing else may be listed there.

Usage: `lake exe check-source [source-dir]` (default `source`). Run by `lake test`.
-/

open Lean

namespace CheckSource

/-- A proposition number split into its integer part and its decimal digits. -/
structure Num where
  whole : Nat
  digits : List Char
  deriving BEq, Inhabited

def Num.parse (s : String) : Option Num :=
  match s.splitOn "." with
  | [w] => w.toNat?.map ({ whole := ·, digits := [] })
  | [w, d] =>
    if d.isEmpty || !d.toList.all Char.isDigit then none
    else w.toNat?.map ({ whole := ·, digits := d.toList })
  | _ => none

def Num.toString (n : Num) : String :=
  if n.digits.isEmpty then s!"{n.whole}" else s!"{n.whole}.{String.ofList n.digits}"

instance : ToString Num := ⟨Num.toString⟩

/-- Wittgenstein's order: by integer part, then lexicographically by decimal digits,
so that `2 < 2.01 < 2.011 < 2.012 < 2.02 < 2.1`. -/
def Num.lt (a b : Num) : Bool :=
  a.whole < b.whole || (a.whole == b.whole && listLt a.digits b.digits)
where
  listLt : List Char → List Char → Bool
    | [], _ :: _ => true
    | x :: xs, y :: ys => x < y || (x == y && listLt xs ys)
    | _, _ => false

/-- Drop the last digit, then trailing zeros: the parent of `2.01` is `2`,
of `2.0121` is `2.012`, of `5.101` is `5.1`, of `1` is none. -/
def Num.parent (n : Num) : Option Num :=
  if n.digits.isEmpty then none
  else
    let ds := (n.digits.dropLast.reverse.dropWhile (· == '0')).reverse
    some { n with digits := ds }

/-- Rows of a TSV file without its header line (empty lines dropped). -/
def readTsv (path : String) : IO (List (List String)) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  return (lines.drop 1).filter (· ≠ "") |>.map (·.splitOn "\t")

def kinds : List String := ["def", "claim", "conseq", "notation", "elucid", "out"]
def confidences : List String := ["high", "mid", "low"]

/-- Validates `docs/reading/classification.tsv` against the proposition numbers:
one row per proposition in the same order, 7 columns, known kind and confidence,
and every contested topic listed in `docs/reading/contested.tsv`. -/
def checkClassification (numbers : List String) : IO (Array String) := do
  let path := "docs/reading/classification.tsv"
  if !(← System.FilePath.pathExists path) then return #[]
  let rows ← readTsv path
  let topicsPath := "docs/reading/contested.tsv"
  let topics : List String ←
    if ← System.FilePath.pathExists topicsPath then
      pure <| (← readTsv topicsPath).map (·.headD "")
    else pure []
  let mut errors : Array String := #[]
  if rows.map (·.headD "") != numbers then
    errors := errors.push s!"{path}: numbers differ from source/tractatus.json (must be one row per proposition, in order)"
  for row in rows do
    match row with
    | [num, kind, conf, contested, _concepts, _related, rationale] =>
      if !kinds.contains kind then errors := errors.push s!"{path}: {num}: unknown kind '{kind}'"
      if !confidences.contains conf then errors := errors.push s!"{path}: {num}: unknown confidence '{conf}'"
      if contested != "-" && !topics.contains contested then
        errors := errors.push s!"{path}: {num}: contested topic '{contested}' is not listed in {topicsPath}"
      if rationale.trimAscii.isEmpty then errors := errors.push s!"{path}: {num}: empty rationale"
    | _ => errors := errors.push s!"{path}: {row.headD "?"}: expected 7 columns, got {row.length}"
  return errors

def run (dir : String) : IO UInt32 := do
  let raw ← IO.FS.readFile (dir ++ "/tractatus.json")
  let json ← IO.ofExcept (Json.parse raw)
  let props ← IO.ofExcept (json.getObjValAs? (Array Json) "propositions")
  let mut errors : Array String := #[]
  let mut nums : Array Num := #[]
  for p in props do
    let numStr ← IO.ofExcept (p.getObjValAs? String "number")
    match Num.parse numStr with
    | none => errors := errors.push s!"malformed number: {numStr}"
    | some n =>
      if n.whole < 1 || n.whole > 7 then errors := errors.push s!"number out of range: {numStr}"
      nums := nums.push n
    for lang in ["en", "de"] do
      let text := (p.getObjValD lang).getObjValD "text"
      match text.getStr? with
      | .ok t => if t.trimAscii.isEmpty then errors := errors.push s!"{numStr}: empty {lang} text"
      | .error _ => errors := errors.push s!"{numStr}: missing {lang} text"
  -- order and uniqueness
  for (a, b) in nums.zip (nums.extract 1 nums.size) do
    if !Num.lt a b then errors := errors.push s!"out of order or duplicate: {a} before {b}"
  -- top-level propositions 1..7
  for w in [1, 2, 3, 4, 5, 6, 7] do
    if !nums.contains { whole := w, digits := [] } then
      errors := errors.push s!"missing top-level proposition {w}"
  -- tree structure
  let orphans := nums.filter fun n =>
    match n.parent with
    | some p => !nums.contains p
    | none => false
  let exceptionsPath := dir ++ "/numbering-exceptions.txt"
  let listed : List String ←
    if ← System.FilePath.pathExists exceptionsPath then
      let lines := (← IO.FS.readFile exceptionsPath).splitOn "\n"
      pure <| (lines.map fun l => ((l.splitOn "#").headD "").trimAscii.toString).filter (· ≠ "")
    else pure []
  let orphanStrs := orphans.toList.map toString
  for o in orphans do
    if !listed.contains (toString o) then
      errors := errors.push s!"{o}: nominal parent {o.parent.get!} does not exist (not listed in numbering-exceptions.txt)"
  for l in listed do
    if !orphanStrs.contains l then
      errors := errors.push s!"{l} is listed in numbering-exceptions.txt but is not an exception"
  -- the reading classification (phase B), if present
  let classErrors ← checkClassification (nums.toList.map toString)
  errors := errors ++ classErrors
  for e in errors do IO.eprintln s!"error: {e}"
  if errors.isEmpty then
    IO.println s!"ok: {nums.size} propositions, {orphans.size} numbering exceptions"
    return 0
  else
    IO.eprintln s!"{errors.size} errors"
    return 1

end CheckSource

def main (args : List String) : IO UInt32 :=
  CheckSource.run (args.headD "source")

import Lean.Data.Json

/-!
# extract-source

Extracts the text of the *Tractatus Logico-Philosophicus* from the LaTeX source
of Project Gutenberg eBook #5740 (C. K. Ogden's 1922 parallel edition) into
`source/tractatus.json` and Markdown views.

Usage: `lake exe extract-source <path/to/5740-t.tex> <outdir>`

Only the work itself is extracted (front matter, preface, propositions).
Russell's introduction and the Project Gutenberg boilerplate are skipped.
-/

open Lean

namespace ExtractSource

abbrev Src := Array Char

def ch (s : Src) (i : Nat) : Char := s.getD i '\x00'

def sub (s : Src) (a b : Nat) : String := String.ofList (s.extract a b).toList

def startsAt (s : Src) (i : Nat) (p : String) : Bool := Id.run do
  let mut j := i
  for c in p.toList do
    if ch s j != c then return false
    j := j + 1
  return true

/-- First index `≥ i` where `p` occurs, or `s.size`. -/
def findFrom (s : Src) (i : Nat) (p : String) : Nat := Id.run do
  let mut j := i
  while j < s.size do
    if startsAt s j p then return j
    j := j + 1
  return s.size

/-- `i` points at `%`; returns the index just after the end of the line. -/
def skipComment (s : Src) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < s.size && ch s j != '\n' do
    j := j + 1
  return j + 1

def skipSpaces (s : Src) (i : Nat) : Nat := Id.run do
  let mut j := i
  while ch s j == ' ' || ch s j == '\t' do
    j := j + 1
  return j

/-- Skip whitespace (including newlines) and comments. -/
partial def skipWs (s : Src) (i : Nat) : Nat :=
  let c := ch s i
  if c == ' ' || c == '\t' || c == '\n' then skipWs s (i + 1)
  else if c == '%' then skipWs s (skipComment s i)
  else i

/-- `i` points at `{`; returns the index just after the matching `}`. -/
partial def skipGroup (s : Src) (i : Nat) : Nat :=
  go (i + 1) 1
where
  go (j depth : Nat) : Nat :=
    if j ≥ s.size then j
    else match ch s j with
      | '\\' => go (j + 2) depth
      | '%' => go (skipComment s j) depth
      | '{' => go (j + 1) (depth + 1)
      | '}' => if depth == 1 then j + 1 else go (j + 1) (depth - 1)
      | _ => go (j + 1) depth

/-- If an optional argument `[...]` follows (after spaces), skip it. -/
def skipOpt (s : Src) (i : Nat) : Nat :=
  let j := skipSpaces s i
  if ch s j == '[' then
    (findFrom s j "]") + 1
  else i

/-- The next mandatory argument starting at or after `i`:
`(contentStart, contentEnd, next)`. A non-group argument is a single token. -/
def nextArg (s : Src) (i : Nat) : Nat × Nat × Nat :=
  let j := skipWs s i
  if ch s j == '{' then
    let e := skipGroup s j
    (j + 1, e - 1, e)
  else if ch s j == '\\' then
    -- a control sequence as argument
    let k := Id.run do
      let mut k := j + 1
      if (ch s k).isAlpha then
        while (ch s k).isAlpha do k := k + 1
      else k := k + 1
      return k
    (j, k, k)
  else (j, j + 1, j + 1)

/-- Read a control sequence name starting just after a backslash at `i`.
Returns `(name, next)`. -/
def readName (s : Src) (i : Nat) : String × Nat := Id.run do
  if (ch s i).isAlpha then
    let mut j := i
    while (ch s j).isAlpha do j := j + 1
    return (sub s i j, j)
  else
    return (String.singleton (ch s i), i + 1)

/-- Page-image markers `% -----File: 097.png---` with their positions. -/
def pageMarkers (s : Src) : Array (Nat × String) := Id.run do
  let mut out := #[]
  let mut j := 0
  let pat := "-----File: "
  while j < s.size do
    let k := findFrom s j pat
    if k ≥ s.size then break
    let a := k + pat.length
    let b := findFrom s a ".png"
    out := out.push (k, sub s a b)
    j := b
  return out

def pageAt (marks : Array (Nat × String)) (i : Nat) : String := Id.run do
  let mut p := ""
  for (k, name) in marks do
    if k < i then p := name else break
  return p

/-! ## LaTeX → plain text (Markdown) conversion -/

structure Typo where
  original : String
  corrected : String

structure ConvState where
  out : String := ""
  footnotes : Array String := #[]
  typos : Array Typo := #[]
  figures : Array String := #[]
  warnings : Array String := #[]

abbrev ConvM := StateM ConvState

def emit (t : String) : ConvM Unit := modify fun st => { st with out := st.out ++ t }

def warn (t : String) : ConvM Unit := modify fun st => { st with warnings := st.warnings.push t }

/-- Environments kept verbatim as fenced LaTeX blocks. -/
def rawEnvs : List String := ["tabular", "array", "table*", "gather*", "split", "alltt"]

/-- Inline math containing these is kept verbatim as `$...$`. -/
def complexMath : List String := ["\\frac", "\\binom", "\\sum", "\\limits"]

def mathSymbol : String → Option String
  | "DotOp" => some " . "
  | "BarOp" => some " | "
  | "Implies" => some " ⊃ "
  | "lor" => some " ∨ "
  | "equiv" => some " ≡ "
  | "times" => some " × "
  | "vdash" => some "⊢"
  | "exists" => some "∃"
  | "aleph" => some "ℵ"
  | "sharp" => some "♯"
  | "flat" => some "♭"
  | "xi" => some "ξ"
  | "eta" => some "η"
  | "Omega" => some "Ω"
  | "phi" => some "φ"
  | "psi" => some "ψ"
  | "nu" => some "ν"
  | "mu" => some "μ"
  | "kappa" => some "κ"
  | _ => none

def textSymbol : String → Option String
  | "idEst" => some "i.e."
  | "IdEst" => some "I.e."
  | "exempliGratia" => some "e.g."
  | "ExempliGratia" => some "E.g."
  | "dasHeiszt" => some "d. h."
  | "zumBeispiel" => some "z. B."
  | "ZumBeispiel" => some "Z. B."
  | "undAndere" => some "u. a."
  | "UndSoWeiter" => some "U. s. w."
  | "undSoFort" => some "u. s. f."
  | "glqq" => some "„"
  | "grqq" => some "“"
  | "glq" => some "‚"
  | "grq" => some "‘"
  | "quotedblbase" => some "„"
  | "DittoInWords" => some "„ „"
  | "DittoInWorten" => some "„ „"
  | "ldots" => some "..."
  | "fourdots" => some "...."
  | "fivedots" => some "....."
  | "Wahr" => some "W"
  | "False" => some "F"
  | "\\" => some "\n"
  | " " => some " "
  | "," => some " "
  | ";" => some " "
  | "-" => some ""
  | "&" => some "&"
  | "%" => some "%"
  | "{" => some "{"
  | "}" => some "}"
  | _ => none

/-- Commands that take no argument and produce nothing. -/
def ignored : List String :=
  ["Strut", "stretchyspace", "verystretchyspace", "AllowBreak", "noindent", "centering",
   "footnotesize", "small", "null", "vfill", "newpage", "hline", "limits"]

/-- Commands whose single argument is dropped. -/
def ignoredWithArg : List String :=
  ["enlargethispage", "hspace", "vspace", "phantom", "selectlanguage", "pagestyle",
   "SkipToNewPage", "end"]

/-- Commands whose single argument is rendered as-is. -/
def transparent : List String := ["text", "mbox", "textsc", "Title"]

def emphasis : List String := ["emph", "textit", "Emph", "EmphPart", "BookTitle"]

def combiningMacron (t : String) : String :=
  String.ofList (t.toList.foldr (fun c acc => c :: '̄' :: acc) [])

mutual

/-- Convert `s[i:stop]`. -/
partial def conv (s : Src) (i stop : Nat) (math : Bool) : ConvM Unit := do
  if i ≥ stop then return
  let c := ch s i
  match c with
  | '%' =>
    let j := skipSpaces s (skipComment s i)
    conv s j stop math
  | '\\' =>
    let j ← command s (i + 1) stop math
    conv s j stop math
  | '{' =>
    let e := skipGroup s i
    conv s (i + 1) (e - 1) math
    conv s e stop math
  | '}' => conv s (i + 1) stop math
  | '$' =>
    if math then conv s (i + 1) stop math
    else
      let e := findFrom s (i + 1) "$"
      let inner := sub s (i + 1) e
      if complexMath.any (fun m => (inner.splitOn m).length > 1) then
        emit ("$" ++ inner ++ "$")
      else
        conv s (i + 1) e true
      conv s (e + 1) stop math
  | '~' => emit " "; conv s (i + 1) stop math
  | '`' =>
    if ch s (i + 1) == '`' then emit "“"; conv s (i + 2) stop math
    else emit "‘"; conv s (i + 1) stop math
  | '\'' =>
    if ch s (i + 1) == '\'' then emit "”"; conv s (i + 2) stop math
    else emit "’"; conv s (i + 1) stop math
  | '-' =>
    if !math && startsAt s i "---" then emit "—"; conv s (i + 3) stop math
    else if !math && startsAt s i "--" then emit "–"; conv s (i + 2) stop math
    else emit "-"; conv s (i + 1) stop math
  | '\n' =>
    if math then emit " "; conv s (i + 1) stop math
    else
      -- a blank line (possibly with spaces) is a paragraph break
      let j := skipSpaces s (i + 1)
      if ch s j == '\n' then
        let k := skipWs s j
        emit "\n\n"; conv s k stop math
      else emit " "; conv s j stop math
  | '&' => emit " & "; conv s (i + 1) stop math
  -- LaTeX typesets a comma in math mode as punctuation followed by a thin space
  | ',' => emit (if math then ", " else ","); conv s (i + 1) stop math
  | c =>
    if math && (c == ' ' || c == '\t') then conv s (i + 1) stop math
    else emit (String.singleton c); conv s (i + 1) stop math

/-- Capture the conversion of `s[a:b]` into a separate string. -/
partial def capture (s : Src) (a b : Nat) (math : Bool) : ConvM String := do
  let saved := (← get).out
  modify fun st => { st with out := "" }
  conv s a b math
  let r := (← get).out
  modify fun st => { st with out := saved }
  return r

/-- Handle a control sequence whose name starts at `i` (just after `\`).
Returns the index to continue from. -/
partial def command (s : Src) (i _stop : Nat) (math : Bool) : ConvM Nat := do
  let (name, j0) := readName s i
  -- LaTeX skips spaces after a control word
  let j := if (ch s i).isAlpha then skipSpaces s j0 else j0
  if name == "begin" then
    let (a, b, k) := nextArg s j
    let env := sub s a b
    if rawEnvs.contains env then
      let endTok := "\\end{" ++ env ++ "}"
      let e := findFrom s k endTok
      let raw := sub s (i - 1) (e + endTok.length)
      emit ("\n\n```latex\n" ++ raw ++ "\n```\n\n")
      return e + endTok.length
    else
      let k := skipOpt s k
      let k := if env == "minipage" then (nextArg s k).2.2 else k
      emit "\n\n"
      return k
  else if name == "[" then
    let e := findFrom s j "\\]"
    let raw := sub s (i - 1) (e + 2)
    emit ("\n\n```latex\n" ++ raw ++ "\n```\n\n")
    return e + 2
  else if name == "DPtypo" then
    -- a typesetting error corrected by the transcribers: `\DPtypo{original}{corrected}`
    let (a1, b1, k1) := nextArg s j
    let (a2, b2, k2) := nextArg s k1
    modify fun st => { st with typos := st.typos.push ⟨sub s a1 b1, sub s a2 b2⟩ }
    conv s a2 b2 math; return k2
  else if name == "\n" then
    -- a backslash at the end of a line is a control space
    emit " "; return j
  else if math then
    match mathSymbol name with
    | some t => emit t; return j
    | none =>
      if name == "Not" then
        let (a, b, k) := nextArg s j
        emit "~"; conv s a b true; return k
      else if name == "overline" then
        let (a, b, k) := nextArg s j
        let t ← capture s a b true
        emit (combiningMacron t); return k
      else if name == "text" || name == "mbox" then
        let (a, b, k) := nextArg s j
        conv s a b false; return k
      else
        match textSymbol name with
        | some t => emit t; return j
        | none =>
          if ignored.contains name then return skipOpt s j
          warn s!"unknown math command \\{name}"
          emit ("\\" ++ name); return j
  else
    match textSymbol name with
    | some t =>
      let j := if name == "\\" then skipOpt s j else j
      emit t; return j
    | none =>
    if ignored.contains name then return skipOpt s j
    else if ignoredWithArg.contains name then return (nextArg s j).2.2
    else if transparent.contains name then
      let (a, b, k) := nextArg s j
      conv s a b false; return k
    else if emphasis.contains name then
      let (a, b, k) := nextArg s j
      let t ← capture s a b false
      if t.trimAscii.isEmpty then return k
      emit ("*" ++ t ++ "*"); return k
    else if name == "PropERef" || name == "PropGRef" then
      let (a, b, k) := nextArg s j
      emit (sub s a b); return k
    else if name == "footnote" then
      let (a, b, k) := nextArg s j
      let t ← capture s a b false
      modify fun st => { st with footnotes := st.footnotes.push t }
      let n := (← get).footnotes.size
      emit s!"[^{n}]"; return k
    else if name == "Illustration" then
      let k := skipOpt s j
      let (a, b, k) := nextArg s k
      let fig := sub s a b
      modify fun st => { st with figures := st.figures.push fig }
      emit s!"\n\n[Figure: {fig}]\n\n"; return k
    else if name == "raisebox" then
      let (_, _, k) := nextArg s j
      let (a, b, k) := nextArg s k
      conv s a b false; return k
    else if name == "smash" then
      let k := skipOpt s j
      let (a, b, k) := nextArg s k
      conv s a b false; return k
    else if name == "discretionary" then
      let k := (nextArg s j).2.2
      let k := (nextArg s k).2.2
      return (nextArg s k).2.2
    else
      match mathSymbol name with
      | some t => emit t.trimAscii.toString; return j
      | none =>
        warn s!"unknown command \\{name}"
        emit ("\\" ++ name); return j

end

/-- Normalise whitespace: collapse runs of spaces, trim around newlines,
at most one blank line in a row; fenced blocks are left untouched. -/
def normalize (t : String) : String := Id.run do
  let lines := t.splitOn "\n"
  let mut out : Array String := #[]
  let mut inFence := false
  for line in lines do
    if line.startsWith "```" then
      inFence := !inFence
      out := out.push line
    else if inFence then
      out := out.push line
    else
      let words := (line.splitOn " ").filter (· ≠ "")
      out := out.push (" ".intercalate words)
  -- collapse multiple blank lines
  let mut res : Array String := #[]
  let mut blank := false
  for l in out do
    if l.isEmpty then
      if !blank && !res.isEmpty then res := res.push l
      blank := true
    else
      res := res.push l
      blank := false
  while !res.isEmpty && res.back!.isEmpty do res := res.pop
  return "\n".intercalate res.toList

structure Converted where
  latex : String
  text : String
  footnotes : Array String
  typos : Array Typo
  figures : Array String
  warnings : Array String

def convert (s : Src) (a b : Nat) : Converted :=
  let ((), st) := (conv s a b false).run {}
  { latex := sub s a b
    text := normalize st.out
    footnotes := st.footnotes.map normalize
    typos := st.typos
    figures := st.figures
    warnings := st.warnings }

/-! ## Extraction -/

structure Prop' where
  number : String
  page : String
  body : Converted

/-- All `\PropositionE{n}{...}` (or `G`) occurrences in order. -/
def propositions (s : Src) (marks : Array (Nat × String)) (macroName : String) :
    Array Prop' := Id.run do
  let mut out := #[]
  let mut j := 0
  let pat := "\\" ++ macroName
  while j < s.size do
    let k := findFrom s j pat
    if k ≥ s.size then break
    let after := k + pat.length
    let n := skipWs s after
    -- skip the macro definition itself (`\newcommand{\PropositionE}[2]`)
    if ch s n != '{' then
      j := after
      continue
    let (na, nb, k1) := nextArg s after
    let (ta, tb, k2) := nextArg s k1
    out := out.push { number := sub s na nb, page := pageAt marks k, body := convert s ta tb }
    j := k2
  return out

def typoJson (t : Typo) : Json :=
  Json.mkObj [("original", t.original), ("corrected", t.corrected)]

def convJson (c : Converted) (page : Option String := none) : Json :=
  Json.mkObj <|
    [("text", Json.str c.text), ("latex", Json.str c.latex)] ++
    (match page with | some p => [("page", Json.str p)] | none => []) ++
    (if c.footnotes.isEmpty then [] else [("footnotes", toJson c.footnotes)]) ++
    (if c.figures.isEmpty then [] else [("figures", toJson c.figures)]) ++
    (if c.typos.isEmpty then [] else [("typos", Json.arr (c.typos.map typoJson))])

def markdown (title : String) (front preface : Converted) (props : Array Prop') : String := Id.run do
  let mut out := s!"# {title}\n\n"
  out := out ++ "<!-- Generated by `lake exe extract-source`. Do not edit. -->\n\n"
  out := out ++ front.text ++ "\n\n## Preface\n\n" ++ preface.text ++ "\n\n## Propositions\n"
  for p in props do
    out := out ++ s!"\n### {p.number}\n\n" ++ p.body.text ++ "\n"
    let mut n := 0
    for f in p.body.footnotes do
      n := n + 1
      out := out ++ s!"\n[^{n}]: {f}\n"
  return out

def run (texPath outDir : String) : IO UInt32 := do
  let tex ← IO.FS.readFile texPath
  -- the Gutenberg file uses CRLF line endings
  let s : Src := (tex.toList.filter (· != '\r')).toArray
  let marks := pageMarkers s
  -- front matter: dedication and motto, between Russell's introduction and the preface
  let prefE := findFrom s 0 "\\Preface{Tractatus Logico-Philosophicus}"
  let mainE := findFrom s 0 "\\MainMatter{Tractatus logico-philosophicus}"
  let prefG := findFrom s 0 "\\Preface{Logisch-Philosophische Abhandlung}"
  let mainG := findFrom s 0 "\\MainMatter{Logisch-philosophische Abhandlung}"
  let russellEnd := findFrom s 0 "\\textsc{Bertrand Russell.}"
  let frontA := findFrom s russellEnd "\\SkipToNewPage{empty}"
  if [prefE, mainE, prefG, mainG, russellEnd, frontA].any (· ≥ s.size) then
    IO.eprintln "error: expected section markers not found; is this 5740-t.tex?"
    return 1
  let front := convert s frontA prefE
  let afterPrefaceHeader (k : Nat) : Nat := (nextArg s (nextArg s (k + "\\Preface".length)).2.2).2.2
  let prefaceE := convert s (afterPrefaceHeader prefE) mainE
  let prefaceG := convert s (afterPrefaceHeader prefG) mainG
  let en := propositions s marks "PropositionE"
  let de := propositions s marks "PropositionG"
  -- report
  let mut warnings : Array String := front.warnings ++ prefaceE.warnings ++ prefaceG.warnings
  for p in en ++ de do
    for w in p.body.warnings do warnings := warnings.push s!"{p.number}: {w}"
  for w in warnings do IO.eprintln s!"warning: {w}"
  if en.size != de.size then
    IO.eprintln s!"error: {en.size} English vs {de.size} German propositions"
    return 1
  let mut props : Array Json := #[]
  for (e, g) in en.zip de do
    if e.number != g.number then
      IO.eprintln s!"error: proposition order differs: {e.number} vs {g.number}"
      return 1
    props := props.push <| Json.mkObj [
      ("number", Json.str e.number),
      ("en", convJson e.body (some e.page)),
      ("de", convJson g.body (some g.page))]
  let doc := Json.mkObj [
    ("source", Json.mkObj [
      ("title", "Tractatus Logico-Philosophicus / Logisch-philosophische Abhandlung"),
      ("author", "Ludwig Wittgenstein"),
      ("translation", "C. K. Ogden (London: Kegan Paul, 1922)"),
      ("transcription", "Project Gutenberg eBook #5740, LaTeX source 5740-t.tex"),
      ("url", "https://www.gutenberg.org/files/5740/5740-t/5740-t.tex"),
      ("note", "Russell's introduction and the Project Gutenberg boilerplate are omitted. `page` is the page-image number of the original scan in which a proposition begins.")]),
    ("front_matter", convJson front),
    ("preface", Json.mkObj [("en", convJson prefaceE), ("de", convJson prefaceG)]),
    ("propositions", Json.arr props)]
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir ++ "/tractatus.json") (doc.pretty 100 ++ "\n")
  IO.FS.writeFile (outDir ++ "/tractatus-en.md")
    (markdown "Tractatus Logico-Philosophicus (Ogden 1922)" front prefaceE en)
  IO.FS.writeFile (outDir ++ "/tractatus-de.md")
    (markdown "Logisch-philosophische Abhandlung" front prefaceG de)
  IO.println s!"extracted {en.size} propositions ({warnings.size} warnings) into {outDir}"
  return 0

end ExtractSource

def main (args : List String) : IO UInt32 := do
  match args with
  | [tex, out] => ExtractSource.run tex out
  | _ =>
    IO.eprintln "usage: lake exe extract-source <5740-t.tex> <outdir>"
    return 2

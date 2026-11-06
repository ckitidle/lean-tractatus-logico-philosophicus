import Lean

/-!
# Links from declarations to propositions of the *Tractatus*

`@[tlp "2.062"]` marks a declaration as formalizing proposition 2.062.
`@[tlp_refutes "6.3751"]` marks a theorem showing that proposition 6.3751 does *not* hold
under the reading adopted here (see docs/policy.md §4).

Each attribute application records the link as a small auxiliary definition of type
`Tractatus.Meta.Tag` under the namespace `Tractatus.Meta.tags`. The checker run by
`lake test` (tools/TlpTest.lean) reads these definitions from the compiled library, so it
does not need to run this file's initialization code.

This module must not import Mathlib: the checker links against nothing but Lean core.
-/

namespace Tractatus.Meta

open Lean

/-- A link from a declaration to a proposition of the *Tractatus*. -/
structure Tag where
  /-- the linked declaration, as a string (`Name.toString`) -/
  decl : String
  /-- the proposition number, e.g. `"2.062"` -/
  number : String
  /-- `true` if the declaration shows that the proposition fails under our reading -/
  refutes : Bool

/-- Valid proposition numbers look like `2` or `2.0121`. -/
def isWellFormedNumber (s : String) : Bool :=
  match s.splitOn "." with
  | [w] => !w.isEmpty && w.all Char.isDigit
  | [w, d] => !w.isEmpty && w.all Char.isDigit && !d.isEmpty && d.all Char.isDigit
  | _ => false

/-- Record that `decl` is linked to proposition `number`. -/
def addTag (decl : Name) (number : String) (refutes : Bool) : AttrM Unit := do
  unless isWellFormedNumber number do
    throwError "malformed proposition number '{number}'"
  let suffix := Name.mkSimple ((if refutes then "refutes_" else "") ++ number.replace "." "_")
  let tagName := (`Tractatus.Meta.tags ++ decl) ++ suffix
  let value := mkApp3 (mkConst ``Tag.mk) (toExpr decl.toString) (toExpr number) (toExpr refutes)
  addDecl <| .defnDecl {
    name := tagName, levelParams := [], type := mkConst ``Tag, value,
    hints := .abbrev, safety := .safe }

end Tractatus.Meta

open Lean in
/-- `@[tlp "2.062"]`: this declaration formalizes proposition 2.062 of the *Tractatus*. -/
syntax (name := tlp) "tlp " str : attr

open Lean in
/-- `@[tlp_refutes "6.3751"]`: this theorem shows that proposition 6.3751 of the
*Tractatus* does not hold under the reading adopted here. -/
syntax (name := tlp_refutes) "tlp_refutes " str : attr

open Lean in
initialize
  registerBuiltinAttribute {
    name := `tlp
    descr := "links a declaration to a proposition of the Tractatus"
    applicationTime := .afterTypeChecking
    add := fun decl stx kind => do
      unless kind == .global do throwError "tlp: only global attributes are supported"
      match stx with
      | `(attr| tlp $s:str) => Tractatus.Meta.addTag decl s.getString false
      | _ => throwError "tlp: unexpected syntax" }
  registerBuiltinAttribute {
    name := `tlp_refutes
    descr := "links a theorem refuting (under our reading) a proposition of the Tractatus"
    applicationTime := .afterTypeChecking
    add := fun decl stx kind => do
      unless kind == .global do throwError "tlp_refutes: only global attributes are supported"
      match stx with
      | `(attr| tlp_refutes $s:str) => Tractatus.Meta.addTag decl s.getString true
      | _ => throwError "tlp: unexpected syntax" }

-- Do not modify this file.
import Lean

/-!
Support code for the knights-and-knaves puzzles.

Every islander is a knight, who says only true things, or a knave, who says
only false things. `role x` is which of the two `x` is, and `Says x s` records
that `x` said `s`: it holds exactly when `x` is a knight if and only if `s`
holds, which is the same as saying a knight said something true or a knave
said something false.

A puzzle takes the islanders it talks about as arguments and each thing they
said as a `Says` hypothesis. The answer is either `impossible` or a
`verdict (...)` naming a role for each islander, and the goal is whatever that
answer claims about their roles.
-/

/-- What an islander is. -/
inductive Role where
  | knight
  | knave
  deriving DecidableEq, Repr, Inhabited

/-- The islanders. Nothing is known about them beyond what a puzzle assumes. -/
opaque Islander : Type

/-- Each islander's role. Nothing is known about it beyond what a puzzle
assumes; the hypotheses are all the information there is. -/
opaque role : Islander → Role

/-- `Says x s`: islander `x` said `s`. A knight's words are true and a knave's
are false, so `x` is a knight exactly when `s` holds. -/
def Says (x : Islander) (s : Prop) : Prop := role x = .knight ↔ s

/-- An answer about the islanders `ns`: a role for each of them, in the
order the puzzle names them, or `impossible` — the claim that nobody could
have said what was said.

The islanders appear as names rather than as the islanders themselves because
an answer is written before any of them is in scope. That is what makes a
puzzle a puzzle: one answer has to fit every reading of it, so it cannot be
assembled by looking at who happens to be a knight. Carrying the names is
also what lets `verdict (...)` check that you answered for the right ones. -/
inductive Answer : List String → Type where
  | impossible : Answer ns
  | last (n : String) (r : Role) : Answer [n]
  | cons (n : String) (r : Role) (rest : Answer ns) : Answer (n :: ns)

/-- What an answer claims about the islanders `xs`, as something to prove.
`impossible` claims `False`, so answering it commits you to deriving a
contradiction. -/
def Answer.holds : {ns : List String} → Answer ns → List Islander → Prop
  | _, impossible, _ => False
  | _, last _ r, [x] => role x = r
  | _, cons _ r rest, x :: xs => role x = r ∧ rest.holds xs
  | _, _, _ => False

/-- The answer that no assignment of knights and knaves fits. -/
abbrev impossible {ns : List String} : Answer ns := .impossible

declare_syntax_cat islanderClaim
syntax ident " is-a " &"knight" : islanderClaim
syntax ident " is-a " &"knave" : islanderClaim

/-- `verdict (A is-a knave, B is-a knight)` is the answer that A is a knave
and B is a knight. Name every islander the puzzle asks about, in the order it
names them: the answer's type lists those names, so answering for the wrong
islanders, or in the wrong order, or for too few of them, is a type error. -/
syntax "verdict" "(" islanderClaim,+ ")" : term

open Lean in
macro_rules
  | `(verdict ($cs,*)) => do
    let mut acc : Option (TSyntax `term) := none
    for c in cs.getElems.reverse do
      let (x, r) ← match c with
        | `(islanderClaim| $x:ident is-a knight) => pure (x, ← `(Role.knight))
        | `(islanderClaim| $x:ident is-a knave)  => pure (x, ← `(Role.knave))
        | _ => Macro.throwUnsupported
      let n := Syntax.mkStrLit x.getId.toString
      acc := some (← match acc with
        | none => `(Answer.last $n $r)
        | some rest => `(Answer.cons $n $r $rest))
    match acc with
    | some t => return t
    | none => Macro.throwUnsupported

open Lean Meta in
/-- `Answer.holds` carried out wherever it is applied to a concrete answer, and
nothing else touched. -/
private partial def reduceClaim (e : Expr) : MetaM Expr :=
  transform e (pre := step)
where
  step (e : Expr) : MetaM TransformStep := do
    let e ← whnfCore e
    if let .const n _ := e.getAppFn then
      if n == ``Answer.holds then
        if let some e' ← unfoldDefinition? e then
          return ← step e'
    return .continue (some e)

/-- `claim% ans xs` is what the answer `ans` claims about the islanders `xs`.
It means the same as `ans.holds xs` — the two are definitionally equal — but the
definition is already unfolded, so a puzzle's goal reads
`role A = Role.knave ∧ role B = Role.knight` instead of `ans.holds [A, B]` and
you can get straight to proving it.

While `ans` is still `sorry` there is nothing to unfold, and the goal shows
`ans.holds xs`; fill the answer in and it becomes the claim you have to prove. -/
syntax "claim% " term:max term:max : term

open Lean Elab Term in
elab_rules : term
  | `(claim% $a $l) => do
    let t ← elabTerm (← `(Answer.holds $a $l)) (some (.sort .zero))
    synthesizeSyntheticMVars
    let t ← instantiateMVars t
    let t' ← reduceClaim t
    -- An unanswered puzzle leaves `sorry`, or a `match` on it, in the way; the
    -- auxiliary matches are named under the definition they came from.
    let stuck := t'.find? fun e =>
      match e with
      | .const n _ => (``Answer.holds).isPrefixOf n || n == ``sorryAx
      | _ => false
    return if stuck.isSome then t else t'

-- Do not modify this file.
import Lean

/-!
Support code for HW01's knights-and-knaves puzzles.

An islander is either a knight, who says only true things, or a knave, who
says only false things. Each islander gets a proposition — `A` reads "A is a
knight", so `¬A` reads "A is a knave" — and each thing an islander says
becomes a hypothesis: `X` says `s` gives `X ↔ s`, true exactly when a knight
said it or a knave said its negation.
-/

/-- What one islander turns out to be. -/
inductive Verdict where
  | knight
  | knave
  deriving DecidableEq, Repr

/-- What verdict `v` claims about the islander whose "is a knight"
proposition is `X`. -/
def Verdict.holds : Verdict → Prop → Prop
  | knight, X => X
  | knave, X => ¬X

/-- An answer about the islanders `ns`: a verdict for each of them, in the
order the puzzle names them, or `impossible` — the claim that nobody could
have said what was said.

The islanders appear as names rather than as their propositions because an
answer is written before any of them is in scope. That is what makes a puzzle
a puzzle: one answer has to fit every reading of it, so it cannot be assembled
by looking at which islander happens to be a knight. Carrying the names is
also what lets `verdict (...)` check that you answered for the right ones. -/
inductive Answer : List String → Type where
  | impossible : Answer ns
  | last (n : String) (v : Verdict) : Answer [n]
  | cons (n : String) (v : Verdict) (rest : Answer ns) : Answer (n :: ns)

/-- What an answer claims about the propositions `Xs`, as something to prove.
`impossible` claims `False`, so answering it commits you to deriving a
contradiction. -/
def Answer.holds : {ns : List String} → Answer ns → List Prop → Prop
  | _, impossible, _ => False
  | _, last _ v, [X] => v.holds X
  | _, cons _ v rest, X :: Xs => v.holds X ∧ rest.holds Xs
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
      let (x, v) ← match c with
        | `(islanderClaim| $x:ident is-a knight) => pure (x, ← `(Verdict.knight))
        | `(islanderClaim| $x:ident is-a knave)  => pure (x, ← `(Verdict.knave))
        | _ => Macro.throwUnsupported
      let n := Syntax.mkStrLit x.getId.toString
      acc := some (← match acc with
        | none => `(Answer.last $n $v)
        | some rest => `(Answer.cons $n $v $rest))
    match acc with
    | some t => return t
    | none => Macro.throwUnsupported

open Lean Meta in
/-- `Answer.holds` and `Verdict.holds` carried out wherever they are applied to
a concrete answer, and nothing else touched: `¬` and `∧` are left as they are. -/
private partial def reduceClaim (e : Expr) : MetaM Expr :=
  transform e (pre := step)
where
  step (e : Expr) : MetaM TransformStep := do
    let e ← whnfCore e
    if let .const n _ := e.getAppFn then
      if n == ``Answer.holds || n == ``Verdict.holds then
        if let some e' ← unfoldDefinition? e then
          return ← step e'
    return .continue (some e)

/-- `claim% ans Xs` is what the answer `ans` claims about the propositions `Xs`.
It means the same as `ans.holds Xs` — the two are definitionally equal — but the
definition is already unfolded, so a puzzle's goal reads `¬A ∧ B` instead of
`ans.holds [A, B]` and you can get straight to proving it.

While `ans` is still `sorry` there is nothing to unfold, and the goal shows
`ans.holds Xs`; fill the answer in and it becomes the claim you have to prove. -/
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
      | .const n _ =>
        (``Answer.holds).isPrefixOf n || (``Verdict.holds).isPrefixOf n
          || n == ``sorryAx
      | _ => false
    return if stuck.isSome then t else t'

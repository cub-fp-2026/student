/-
# Lecture 1

- Lean as a language for logic
- Propositional logic connectives
- Logic puzzles

-/

import Course.KnightsAndKnaves
namespace Lecture01
set_option linter.defProp false

-- ## Truth and Implication

theorem selfImpl {A : Prop} : A → A := sorry

theorem implConst {A B : Prop} : A → B → A := sorry

theorem implSelectSecond {A B C : Prop} : A → B → C → B := sorry

theorem implModusPonens {A B : Prop} : A → (A → B) → B := sorry

theorem implTrans {A B C : Prop} : (A → B) → (B → C) → (A → C) := sorry

-- ## Conjunction

theorem andIntro {A B : Prop} : A → B → A ∧ B := sorry

theorem andLeft {A B : Prop} : A ∧ B → A := sorry

theorem andRight {A B : Prop} : A ∧ B → B := sorry

theorem andSymm {A B : Prop} : A ∧ B → B ∧ A := sorry

theorem andAssoc {A B C : Prop} : (A ∧ B) ∧ C → A ∧ (B ∧ C) := sorry

-- ## Disjunction

theorem orIntroLeft {A B : Prop} : A → A ∨ B := sorry

theorem orIntroRight {A B : Prop} : B → A ∨ B := sorry

theorem orElim {A B C : Prop} : (A → C) → (B → C) → A ∨ B → C := sorry

theorem orSymm {A B : Prop} : A ∨ B → B ∨ A := sorry

theorem orAssoc {A B C : Prop} : (A ∨ B) ∨ C → A ∨ (B ∨ C) := sorry

theorem andDistribOr {A B C : Prop} : A ∧ (B ∨ C) → A ∧ B ∨ A ∧ C := sorry

-- ## False and negation

theorem exFalso {A : Prop} : False → A := sorry

theorem notFalse : ¬False := sorry

theorem absurdLive {A C : Prop} : A → ¬A → C := fun a na => sorry

theorem notNotIntro {A : Prop} : A → ¬¬A := fun a na => sorry

theorem notNotElim {A : Prop} : ¬¬A → A := fun nna => sorry

-- ## Iff

theorem iffRefl {A : Prop} : A ↔ A := sorry

theorem iffAsPair {A B : Prop} : (A ↔ B) → (A → B) ∧ (B → A) := sorry

theorem notIsArrow {A : Prop} : ¬A ↔ (A → False) := sorry


-- ## Knights and Knaves

/-
Knights always tell the truth.
Knaves always lie.

Possible answers:
- impossible
- verdict (A is-a knight, B is-a knave, ...)
-/

/-- You meet A.  A says: "False is true" -/
def answerFalseIsTrue : Answer ["A"] := sorry

theorem puzzleFalseIsTrue (A : Prop) (hA : A ↔ False) :
    claim% answerFalseIsTrue [A] := sorry

/-- You meet A and B.  A says: "I am a knave or B is a knight." -/
def answerKnaveOrKnight : Answer ["A", "B"] := sorry

theorem puzzleKnaveOrKnight (A B : Prop) (hA : A ↔ (¬A ∨ B)) :
    claim% answerKnaveOrKnight [A, B] := sorry

/-- You meet A and B.
A says: "B and I are not the same type."
B says: "A and I are the same type." -/
def answerDisagreement : Answer ["A", "B"] := sorry

theorem puzzleDisagreement (A B : Prop) (hA : A ↔ (A ↔ ¬B)) (hB : B ↔ (A ↔ B)) :
    claim% answerDisagreement [A, B] := sorry

end Lecture01

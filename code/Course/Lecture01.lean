/-
# Lecture 1

- Lean as a language for logic
- Propositional logic connectives
- Logic puzzles

-/

import Course.KnightsAndKnaves
namespace Lecture01
set_option linter.defProp false

#eval 2 + 2
#check 2 + 2
#check fun (x: Nat) => x + x
#print Nat

-- ## Truth and Implication

theorem trueIsTrue : True := True.intro

theorem selfImpl {A : Prop} : A → A := fun a => a

theorem implConst {A B : Prop} : A → B → A :=
    fun a _ => a

theorem implSelectSecond {A B C : Prop} : A → B → C → B :=
    fun _ b _ => b

theorem implModusPonens {A B : Prop} : A → (A → B) → B :=
    fun a ab => ab a

theorem implTrans {A B C : Prop} : (A → B) → (B → C) → (A → C) :=
    fun ab bc a => bc (ab a)

-- ## Conjunction

theorem andIntro {A B : Prop} (a : A) (b : B) : A ∧ B := ⟨a, b⟩
#print andIntro

#print And.left
theorem andLeft {A B : Prop} : A ∧ B → A := fun ab => ab.left

theorem andRight {A B : Prop} : A ∧ B → B := fun ⟨_, b⟩ => b

theorem andSymm {A B : Prop} : A ∧ B → B ∧ A := fun ⟨a, b⟩ => ⟨b, a⟩

theorem andAssoc {A B C : Prop} : (A ∧ B) ∧ C → A ∧ (B ∧ C) :=
    fun ⟨⟨a, b⟩, c⟩ => ⟨a, ⟨b, c⟩⟩

-- ## Disjunction

#print Or
theorem orIntroLeft {A B : Prop} : A → A ∨ B :=
    fun a => Or.inl a

theorem orIntroRight {A B : Prop} : B → A ∨ B :=
    fun b => .inr b

theorem orElim {A B C : Prop} (f : A → C) (g : B → C) : A ∨ B → C :=
    fun a_or_b =>
        match a_or_b with
        | .inl a => f a
        | .inr b => g b

theorem orSymm {A B : Prop} : A ∨ B → B ∨ A
--    fun aorb => aorb.elim (fun a => .inr a) (fun b => .inl b)
--    fun aorb => match aorb with (part below)
    | .inl a => .inr a
    | .inr b => .inl b

theorem orAssoc {A B C : Prop} : (A ∨ B) ∨ C → A ∨ (B ∨ C) := sorry

theorem andDistribOr {A B C : Prop} : A ∧ (B ∨ C) → A ∧ B ∨ A ∧ C := sorry

-- ## False and negation

#print False
#check False.elim
theorem exFalso {A : Prop} : False → A := nofun

#print Not
theorem notFalse : ¬False := fun fls => fls

theorem absurdLive {A C : Prop} : A → ¬A → C :=
    fun a na => False.elim (na a)

theorem notNotIntro {A : Prop} : A → ¬¬A := fun a na => sorry

theorem notNotElim {A : Prop} : ¬¬A → A := fun nna => sorry

-- ## Iff

theorem iffRefl {A : Prop} : A ↔ A := ⟨fun x => x, fun x => x⟩

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
def answerFalseIsTrue : Answer ["A"] := verdict (A is-a knave)

theorem puzzleFalseIsTrue (A : Prop) (hA : A ↔ False) :
    claim% answerFalseIsTrue [A] :=
        fun a => hA.mp a

/-- You meet A and B.  A says: "I am a knave or B is a knight." -/
def answerKnaveOrKnight : Answer ["A", "B"] :=
    verdict (A is-a knave, B is-a knight)

theorem puzzleKnaveOrKnight (A B : Prop) (hA : A ↔ (¬A ∨ B)) :
    claim% answerKnaveOrKnight [A, B] :=
        match Classical.em A with
        | .inl a => sorry
        | .inr na => sorry

/-- You meet A and B.
A says: "B and I are not the same type."
B says: "A and I are the same type." -/
def answerDisagreement : Answer ["A", "B"] := sorry

theorem puzzleDisagreement (A B : Prop) (hA : A ↔ (A ↔ ¬B)) (hB : B ↔ (A ↔ B)) :
    claim% answerDisagreement [A, B] := sorry

end Lecture01

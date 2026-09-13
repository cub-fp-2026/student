/-
# Lecture 2

- Tactics
- Inductive types
- Equality
- Quantifiers
-/

import Course.Islanders
import Batteries.Tactic.Init
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Hint
namespace Lecture02
set_option linter.defProp false

-- ## Tactics

theorem selfImpl {A : Prop} : A → A := by
  intro
  assumption

theorem implTrans {A B C : Prop} : (A → B) → (B → C) → (A → C) := by
  intros
  repeat apply_assumption

#print implTrans

theorem andSymm {A B : Prop} : A ∧ B → B ∧ A := by
  rintro ⟨_, _⟩
  constructor <;> assumption

theorem orSymm {A B : Prop} : A ∨ B → B ∨ A := by
  rintro (_ | _)
  · right
    assumption
  · left
    assumption

theorem orElim {A B C : Prop} (f : A → C) (g : B → C) : A ∨ B → C := by
  rintro (_ | _) <;> solve_by_elim

theorem andDistribOr {A B C : Prop} : A ∧ (B ∨ C) → A ∧ B ∨ A ∧ C
  | ⟨a, .inl b⟩ => .inl ⟨a, b⟩
  | ⟨a, .inr c⟩ => .inr ⟨a, c⟩

/-
 := by
  rintro ⟨a, b | c⟩
  · left
    exact ⟨a, b⟩
  · right
    exact ⟨a, c⟩
-/

#print andDistribOr

theorem exFalso {A : Prop} : False → A := by
  intros
  contradiction

theorem notNotIntro {A : Prop} : A → ¬¬A := by
  intro _ _
  contradiction

theorem notIsArrow {A : Prop} : ¬A ↔ (A → False) := by
  -- variation
  constructor <;> (intro _ _; contradiction)

theorem absurdLive {A C : Prop} : A → ¬A → C := by
  intro a not_a
  exfalso
  exact not_a a

theorem deMorganOr {A B : Prop} : ¬(A ∨ B) ↔ ¬A ∧ ¬B := by
  -- variation
  constructor
  · intro not_a_or_b
    constructor
    · intro
      apply not_a_or_b
      left
      assumption
    · intro b
      have a_or_b : A ∨ B := Or.inr b
      exact not_a_or_b a_or_b
  · rintro ⟨na, nb⟩ (a | b) <;> contradiction

-- two approaches:
-- `by_cases a : A`
-- `by_contra h`
theorem notNotElim {A : Prop} : ¬¬A → A := by
  by_cases a : A
  · intro h
    exact a
  · intro h
    exfalso
    apply h
    exact a

theorem notNotElim' {A : Prop} : ¬¬A → A := by
  intro h
  by_contra h2
  contradiction

-- ## Inductive types

/-
class Pair {
  val x: Int
  val y: Int
}
-/

inductive Pair where
| pair (x y : Nat)

#print Pair

#print Role

def Role.flip : Role → Role
  | .knight => .knave
  | .knave => .knight

#eval Role.flip Role.knight

theorem flipKnight : Role.flip .knight = .knave := by
  rewrite [Role.flip]
  rfl

theorem flipFlipKnight : Role.flip (Role.flip .knight) = Role.flip .knave := by
  conv => rhs; rewrite [Role.flip]
  rewrite [Role.flip]
  rewrite [Role.flip]
  rfl

theorem flipFlip (r : Role) : Role.flip (Role.flip r) = r := by
  cases r <;> rfl

theorem knightNeKnave : Role.knight ≠ Role.knave := by
  intro h
  cases h

theorem flipNeSelf (r : Role) : Role.flip r ≠ r := by
  intro h
  cases r
  · cases h
  · cases h

-- ## Equality

-- note: equalities
#print Eq

example (r1 r2 : Role) (h : Role.flip .knight = Role.flip .knave) :
    r1 = .knight ∧ r2 = .knave := by
  repeat rw [Role.flip] at h
  cases h

theorem eqSymm {α : Type} (a b : α) (h : a = b) : b = a := by
  rw [h]

theorem eqTrans {α : Type} (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by
  cases h₁
  cases h₂
  rfl

theorem congrRole (A B : Islander) (h : A = B) : role A = role B := by
  rw [h]

theorem roleChain (A B : Islander) (h : role A = role B) (hB : role B = .knight) :
    role A = .knight := by
  rw [← h] at hB
  exact hB

-- ## Quantifiers

theorem forallAnd {α : Type} (P Q : α → Prop) :
    (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    constructor
    · intro x
      have p := h x
      exact p.left
    · intro x
      have q := h x
      exact q.right
  · intro h
    intro x
    constructor
    · apply h.left
    · apply h.right

theorem existsOr {α : Type} (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · intro h
    obtain ⟨x, p | q⟩ := h
    · left
      exact ⟨x, p⟩
    · right
      exact ⟨x, q⟩
  · intro h
    obtain ⟨x, hl⟩ | ⟨x, hr⟩ := h
    · exact ⟨x, Or.inl hl⟩
    · exact ⟨x, Or.inr hr⟩

theorem existsAndImp {α : Type} (P Q : α → Prop) :
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  intro h
  obtain ⟨x, ⟨p, q⟩⟩ := h
  constructor
  · exact ⟨x, p⟩
  · exact ⟨x, q⟩

theorem existsNotOfNotForall {α : Type} (P : α → Prop) :
    (∃ x, ¬P x) → ¬(∀ x, P x) := by
  intro h
  obtain ⟨x, not_px⟩ := h
  intro h
  apply not_px
  exact h x

-- ## Injective and surjective functions

def Injective {α β : Type} (f : α → β) : Prop := ∀ x y, f x = f y → x = y

def Surjective {α β : Type} (f : α → β) : Prop := ∀ y, ∃ x, f x = y

theorem injectiveId {α : Type} : Injective (fun x : α => x) := by
  unfold Injective
  intro x y
  intro h
  exact h

theorem flipInjective : Injective Role.flip := by
  unfold Injective
  intro x y h
  -- variation
  cases x <;> cases y <;> try rfl
  · cases h
  · cases h

theorem flipSurjective : Surjective Role.flip := by
  unfold Surjective
  intro y
  cases y
  · have h : Role.flip Role.knave = Role.knight := by rfl
    exact ⟨_, h⟩
  · have h : Role.flip Role.knight = Role.knave := by rfl
    exact ⟨_, h⟩

theorem injectiveComp {α β γ : Type} (f : α → β) (g : β → γ)
    (hf : Injective f) (hg : Injective g) : Injective (fun x => g (f x)) := by
  unfold Injective
  intro x y h
  apply hf
  apply hg
  exact h

theorem surjectiveComp {α β γ : Type} (f : α → β) (g : β → γ)
    (hf : Surjective f) (hg : Surjective g) : Surjective (fun x => g (f x)) := by
  unfold Surjective
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  have h : g (f x) = z := by
    rw [hx, hy]
  exact ⟨x, h⟩

-- ## Knights and knaves, with the islanders as values

/-
Last week an islander was a proposition, "A is a knight".
Now an islander is a value of type `Islander`, `role A` is a `Role`,
and "A said s" is `Says A s`.
A puzzle quantifies over the islanders it talks about.
-/

/-- A says: "I am a knave." -/
def answerSelfAccusation : Answer ["A"] := impossible

-- `unfold Says at hA`, `cases hr : role A`, `rw [hr] at h`, `cases h`.
theorem puzzleSelfAccusation (A : Islander) (hA : Says A (role A = .knave)) :
    claim% answerSelfAccusation [A] := by
  unfold Says at hA
  cases hr : role A
  · have h := hA.mp hr
    rw [hr] at h
    cases h
  · have h := hA.mpr hr
    rw [hr] at h
    cases h

#print axioms puzzleSelfAccusation

/-- A says: "B is a knight."  B says: "A and I are not the same." -/
def answerDifferent : Answer ["A", "B"] := verdict (A is-a knave, B is-a knave)

theorem puzzleDifferent (A B : Islander)
    (hA : Says A (role B = .knight))
    (hB : Says B (role A ≠ role B)) :
    claim% answerDifferent [A, B] := by
  unfold Says at hA hB
  cases hrA : role A
  · -- A is a knight, so B is a knight too, so what B said is false.
    exfalso
    have hrB := hA.mp hrA
    have hne := hB.mp hrB
    apply hne
    rw [hrA, hrB]
  · cases hrB : role B
    · -- B is a knight, so A is one as well.
      have h := hA.mpr hrB
      rw [hrA] at h
      cases h
    · exact ⟨rfl, rfl⟩

/-- A says: "Everyone on this island is a knave." -/
def answerAllKnaves : Answer ["A"] := verdict (A is-a knave)

theorem puzzleAllKnaves (A : Islander) (hA : Says A (∀ x, role x = .knave)) :
    claim% answerAllKnaves [A] := by
  unfold Says at hA
  cases hr : role A
  · -- A would be a knight counting himself among the knaves.
    exfalso
    have h := hA.mp hr A
    rw [hr] at h
    cases h
  · rfl

/-- A says: "Someone on this island is a knight."  B says: "A is a knave." -/
def answerSomeKnight : Answer ["A", "B"] := verdict (A is-a knight, B is-a knave)

theorem puzzleSomeKnight (A B : Islander)
    (hA : Says A (∃ x, role x = .knight)) (hB : Says B (role A = .knave)) :
    claim% answerSomeKnight [A, B] := by
  unfold Says at hA hB
  cases hrA : role A
  · constructor
    · rfl
    · cases hrB : role B
      · -- B is a knight calling the knight A a knave.
        exfalso
        have h := hB.mp hrB
        rw [hrA] at h
        cases h
      · rfl
  · exfalso
    cases hrB : role B
    · -- B is the knight A said existed, so A is a knight after all.
      have h := hA.mpr ⟨B, hrB⟩
      rw [hrA] at h
      cases h
    · -- B is a knave, so what B said about A is false.
      have h := hB.mpr hrA
      rw [hrB] at h
      cases h

-- # Bonus lecture material

-- ## Inductive Types

inductive MyBool : Type where
  | t : MyBool
  | f : MyBool

#print MyBool

def or : MyBool → MyBool → MyBool
  | .t, .t => .t
  | .f, .t => .t
  | .t, .f => .t
  | .f, .f => .f

def and : MyBool → MyBool → MyBool
  | .t, .t => .t
  | _, _ => .f

def not : MyBool → MyBool
  | .t => .f
  | .f => .t

def PropDeMorgan (P Q : Prop) :
    Not (And P Q) ↔ Or (Not P) (Not Q) := by
  constructor
  · sorry
  · rintro (np | nq) ⟨p, q⟩ <;> contradiction

def myBoolDeMorgan (x y : MyBool) :
    not (and x y) = or (not x) (not y) := by
  cases x <;> cases y <;> rfl
  /-
  · conv => rhs; repeat rewrite [not]
    rewrite [and]
    rewrite [or]
    rewrite [not]
    rfl
  -/

-- ## Bool vs Prop vs Type

#check Bool.true
#print Bool
#check True
example (tt : True) : True := tt

inductive MyPropBool : Prop where
  | tProp : MyPropBool
  | fProp : MyPropBool

example : ∀ x y: MyPropBool, x = y := fun _ _ => rfl
example : ∃ x y: MyBool, x ≠ y := by
  exists .t
  exists .f
  intro h
  contradiction

example : MyPropBool → MyBool := sorry
/-
| .tProp => .t
| .fProp => .f
-/


-- ## The Curry-Howard Isomorphism

-- a proposition: a type of type Prop
-- a proof: a term of a proposition type
  -- (i.e. a term of a type of type Prop t : P : Prop)

example {A : Prop} : A → A → A := by
  intro x y
  assumption


-- a value type: a type of type Type
-- a program: a term of a value type
  -- (i.e. a term of a type of type Type, t : T : Type)

def myFirst {A : Type} : A → A → A := fun x _ => x
def mySecond {A : Type} : A → A → A := fun _ y => y

end Lecture02

/-
# Lecture 2

- Tactics
- Inductive types
- Equality
- Quantifiers
-/

import Course.Islanders
import Batteries.Tactic.Init
namespace Lecture02
set_option linter.defProp false

-- ## Tactics

theorem selfImpl {A : Prop} : A → A := by
  intro a
  exact a

theorem implTrans {A B C : Prop} : (A → B) → (B → C) → (A → C) := by
  intro ab bc a
  apply bc
  apply ab
  exact a

theorem andSymm {A B : Prop} : A ∧ B → B ∧ A := by
  intro h
  obtain ⟨a, b⟩ := h
  exact ⟨b, a⟩

theorem orSymm {A B : Prop} : A ∨ B → B ∨ A := by
  intro h
  obtain a | b := h
  · right
    exact a
  · left
    exact b

-- rcases
theorem orElim {A B C : Prop} (f : A → C) (g : B → C) : A ∨ B → C := by
  intro h
  rcases h with a | b
  · exact f a
  · exact g b

theorem andDistribOr {A B C : Prop} : A ∧ (B ∨ C) → A ∧ B ∨ A ∧ C := by
  intro h
  rcases h with ⟨a, b | c⟩
  · left
    exact ⟨a, b⟩
  · right
    exact ⟨a, c⟩

theorem exFalso {A : Prop} : False → A := by
  intro h
  exfalso
  exact h

theorem notNotIntro {A : Prop} : A → ¬¬A := by
  intro a not_a
  apply not_a
  exact a

theorem notIsArrow {A : Prop} : ¬A ↔ (A → False) := by
  constructor
  · intro not_a a
    exact not_a a
  · intro not_a
    exact not_a

theorem absurdLive {A C : Prop} : A → ¬A → C := by
  intro a not_a
  exfalso
  exact not_a a

theorem deMorganOr {A B : Prop} : ¬(A ∨ B) ↔ ¬A ∧ ¬B := by
  constructor
  · intro not_a_or_b
    constructor
    · intro a
      have a_or_b : A ∨ B := Or.inl a
      exact not_a_or_b a_or_b
    · intro b
      have a_or_b : A ∨ B := Or.inr b
      exact not_a_or_b a_or_b
  · intro not_a_or_not_b
    intro a_or_b
    obtain a | b := a_or_b
    · exact not_a_or_not_b.left a
    · exact not_a_or_not_b.right b

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
  exfalso
  exact h h2

-- ## Inductive types

#print Role

def Role.flip : Role → Role
  | .knight => .knave
  | .knave => .knight

#eval Role.flip .knight

theorem flipKnight : Role.flip .knight = .knave := by
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

theorem eqSymm {α : Type} (a b : α) (h : a = b) : b = a := by
  rw [h]

theorem eqTrans {α : Type} (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁, h₂]

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
  cases x <;> cases y
  · rfl
  · cases h
  · cases h
  · rfl

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

end Lecture02

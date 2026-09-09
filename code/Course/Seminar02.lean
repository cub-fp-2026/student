/-
# Seminar 2
-/

import Course.Islanders
import Batteries.Tactic.Init
namespace Seminar02

-- ## Round 1 — translate

/-
Each of these is one of last week's exercises, with the term proof you handed
in written above it. Write the same proof with tactics.
-/

-- term: ⟨⟨h.left, h.right.left⟩, h.right.right⟩
theorem andAssocBack {A B C : Prop} (h : A ∧ (B ∧ C)) : (A ∧ B) ∧ C := by
  sorry

-- term: ⟨fun na b => na (hab.mpr b), fun nb a => nb (hab.mp a)⟩
theorem iffNotCongr {A B : Prop} (hab : A ↔ B) : ¬A ↔ ¬B := by
  sorry

-- term: fun ⟨a, na⟩ => na a
theorem noContradiction {A : Prop} : ¬(A ∧ ¬A) := by
  sorry

/-- The one where the term is a puzzle and the tactic proof is not: every step
is forced by the goal. When it is done, `#print` it — you will get your own
term back, character for character. -/
-- term: fun h => h (Or.inr (fun a => h (Or.inl a)))
theorem notNotEm {A : Prop} : ¬¬(A ∨ ¬A) := by
  sorry

#print notNotEm

-- ## Round 2 — back-translate

/-
Now the other direction. The two tactic proofs below are given. Predict what
`#print` shows, write the term yourself underneath, and see whether they agree.
-/

theorem implModusPonens {A B : Prop} : (A → B) ∧ A → B := by
  intro h
  exact h.left h.right

#print implModusPonens

theorem implModusPonensTerm {A B : Prop} : (A → B) ∧ A → B :=
  sorry

theorem andOrDistrib {A B C : Prop} (h : A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) := by
  obtain ⟨a, hbc⟩ := h
  cases hbc with
  | inl b => left;  exact ⟨a, b⟩
  | inr c => right; exact ⟨a, c⟩

-- Predict this one before you run it.
#print andOrDistrib

theorem andOrDistribTerm {A B C : Prop} (h : A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) :=
  sorry

-- ## Round 3 — the proofs whose term you would not want to write

def Role.flip : Role → Role
  | .knight => .knave
  | .knave => .knight

/-- Two constructors, and both sides compute in each of them. One `cases`, then
`rfl` twice — `<;>` runs the tactic after it on every goal the one before it
opened. -/
theorem flipFlipFlip (r : Role) :
    Role.flip (Role.flip (Role.flip r)) = Role.flip r := by
  sorry

/-- Rewriting forwards. The last rewrite leaves `role C = role C`, which `rw`
closes by itself. -/
theorem roleChain3 (A B C : Islander) (h₁ : role A = role B) (h₂ : role B = role C) :
    role A = role C := by
  sorry

/-- The same fact, rewriting backwards and at a hypothesis instead: turn `h₂`
into the goal rather than the goal into `h₂`. -/
theorem roleChain3' (A B C : Islander) (h₁ : role A = role B) (h₂ : role B = role C) :
    role A = role C := by
  sorry

/-- `∀` is `→` with a name on the argument, so it needs no new tactic. -/
theorem forallImpForall {α : Type} (P Q : α → Prop) :
    (∀ x, P x → Q x) → (∀ x, P x) → ∀ x, Q x := by
  sorry

/-- `∃` is a pair, so it is `obtain` to use and `⟨_, _⟩` to build. -/
theorem existsSwap {α β : Type} (P : α → β → Prop) :
    (∃ x, ∃ y, P x y) → ∃ y, ∃ x, P x y := by
  sorry

/-!
### The same puzzle in the new encoding

Last week this was islanders-as-propositions and the case split came from
`Classical.em A`. Now an islander is a value, and the split comes from the two
constructors of `Role` — so the proof is constructive. Compare it with what you
handed in for `puzzleMutualAccusation` last week.

The answer is given here, so the goal reads `False` from the start; the tactics
are the exercise.
-/

/-- You meet A and B.  A says: "B is a knight."  B says: "A is a knave." -/
def answerMutualAccusation : Answer ["A", "B"] := impossible

-- `unfold Says at hA hB`, `cases hr : role A`, `rw [hr] at h`, `cases h`.
theorem puzzleMutualAccusation (A B : Islander)
    (hA : Says A (role B = .knight)) (hB : Says B (role A = .knave)) :
    claim% answerMutualAccusation [A, B] := by
  sorry

#print axioms puzzleMutualAccusation

end Seminar02

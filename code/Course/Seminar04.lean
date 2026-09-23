/-
# Seminar 4
-/

import Mathlib.Tactic

namespace Seminar04

-- ## Round 1 — `≤` is a rule set

#check @Nat.le.refl
#check @Nat.le.step

/-- Build the derivation by hand: each `step` climbs one, `refl` is the one way to stop. -/
theorem two_le_five_term : 2 ≤ 5 := by
  sorry

/-- Homework ex01. The same claim, letting `constructor` choose the rule every time. -/
theorem two_le_five : 2 ≤ 5 := by
  sorry

/-- Induct on the number, not on a derivation — `0 ≤ n` hands you no derivation to take
apart, so the derivation is what you have to build. -/
theorem zero_le' (n : Nat) : 0 ≤ n := by
  sorry

/-- Homework ex03. Induct on `m`, then take the hypothesis apart with `cases h with`.
One of the cases closes on its own, because no rule can conclude `n + 1 ≤ 0`. -/
theorem le_of_succ_le_succ (n m : Nat) : n + 1 ≤ m + 1 → n ≤ m := by
  sorry

/-- The homework's `myMax`, with `≤` where the homework has `isLe`. -/
def myMax (n m : Nat) : Nat :=
  if n ≤ m then m else n

/-- Homework ex07. `unfold myMax` first. `split` then gives one goal per branch of the
`if`, each carrying the hypothesis that put it there — `‹n ≤ m›` names it back.
`Nat.le_of_not_le` closes the other branch. -/
theorem le_myMax (n m : Nat) : n ≤ myMax n m ∧ m ≤ myMax n m := by
  sorry

-- ## Round 2 — a new rule set: stamps

/-- What postage you can make from 3¢ and 5¢ stamps: 0¢ needs no stamps, and any
amount you can make stays makeable after one more stamp of either kind. -/
inductive Buyable : Nat → Prop where
  | zero : Buyable 0
  | add3 {n : Nat} : Buyable n → Buyable (n + 3)
  | add5 {n : Nat} : Buyable n → Buyable (n + 5)

/-- One stamp. Write the term. -/
theorem buyable_three : Buyable 3 :=
  sorry

/-- Three stamps. Write the term. -/
theorem buyable_nine : Buyable 9 :=
  sorry

-- The lecture's search — `MyOdd 5`, `CollatzFinite 6` — closes this one.
example : Buyable 9 := by
  repeat first | exact Buyable.zero | apply Buyable.add3 | apply Buyable.add5

/-- The same search on 13 fails. Run it, read the goal it gives up on, and say why.
Then prove this: as a term, or with a tactic that backtracks (`solve_by_elim` takes the
rules as a list). -/
theorem buyable_thirteen : Buyable 13 :=
  sorry

-- ## Round 3 — take a derivation apart

/-- `intro`, then `cases`: which of the three rules could have concluded `Buyable 1`? -/
theorem not_buyable_one : ¬ Buyable 1 := by
  sorry

/-- The same, one level deeper. -/
theorem not_buyable_four : ¬ Buyable 4 := by
  sorry

/-- The same again, except the first `cases` leaves two branches this time, because two
rules can conclude `Buyable 7`. Draw the tree before you write it. -/
theorem not_buyable_seven : ¬ Buyable 7 := by
  sorry

-- ## Round 4 — induct over a derivation, and compare with a formula

/-- `induction hm` — on the derivation, not on `m`. The shape of the lecture's `even_add`. -/
theorem buyable_add (n m : Nat) (hn : Buyable n) (hm : Buyable m) : Buyable (n + m) := by
  sorry

theorem buyable_three_mul (a : Nat) : Buyable (3 * a) := by
  sorry

theorem buyable_five_mul (b : Nat) : Buyable (5 * b) := by
  sorry

/-- The rules on the left, a formula on the right. Left to right is an induction over the
derivation. Right to left needs no induction at all — the three lemmas above already did
it. -/
theorem buyable_iff_exists (n : Nat) : Buyable n ↔ ∃ a b, n = 3 * a + 5 * b := by
  sorry

-- ## Round 5 — strengthen the hypothesis, then compute

/-- Everything from 8¢ up is buyable. `∀ n, Buyable (n + 8)` on its own cannot be proved
by induction on `n`: no rule steps by 1, so knowing `n + 8` is buyable says nothing about
`n + 9`. Carry three consecutive amounts and the step goes through. -/
theorem buyable_eight_nine_ten (n : Nat) :
    Buyable (n + 8) ∧ Buyable (n + 9) ∧ Buyable (n + 10) := by
  sorry

/-- `Nat.exists_eq_add_of_le` turns `h` into an equation: the lecture's
`le_iff_exists_add_eq` under its library name. -/
theorem buyable_of_le (n : Nat) (h : 8 ≤ n) : Buyable n := by
  sorry

/-- The whole answer: four exceptional amounts, then everything. Left to right, go
through `buyable_iff_exists` — but `omega` will not finish alone, it cannot rule out
`3 * a + 5 * b ∈ {1, 2}`. Split the small cases off first with
`rcases a with _ | _ | _ | a` (and similarly for `b`) and leave the rest to `omega`. -/
theorem buyable_iff (n : Nat) :
    Buyable n ↔ n = 0 ∨ n = 3 ∨ n = 5 ∨ n = 6 ∨ 8 ≤ n := by
  sorry

/-- The lecture's bridge: the claim, decided, as data. `decidable_of_iff` builds one
from a claim that is already decidable and an `Iff`. -/
instance (n : Nat) : Decidable (Buyable n) :=
  sorry

-- Once that instance is real, uncomment these. The rules are gone; a computation decides.
-- `¬ Buyable 7` cost a tree of `cases` in round 3.
-- example : Buyable 100 := by decide
-- example : ¬ Buyable 7 := by decide
-- #eval decide (Buyable 7)

end Seminar04

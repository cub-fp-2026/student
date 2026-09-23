/-
# Lecture 4

- Inductive predicates: claims defined by rules
- Less-or-equal, even and odd: each compared with a formula and a computation
- Parity: Type vs Prop, and Decidable as the bridge
- Collatz
-/

import Batteries.Tactic.Init
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Hint
import Mathlib.Tactic.Ring
namespace Lecture04

-- ## Recap: inductive types build data

#print Nat

-- ## Inductive predicates: claims defined by rules

inductive MyLe : Nat → Nat → Prop where
  | refl (n : Nat) : MyLe n n
  | step {n m : Nat} : MyLe n m → MyLe n (m + 1)

example : MyLe 2 4 := MyLe.step (MyLe.step (MyLe.refl 2))

-- ### Using a derivation: cases

theorem not_succ_le_zero (n : Nat) : ¬ MyLe (n + 1) 0 := by
  intro h
  cases h

-- ### Nat's own ≤ is an inductive predicate

#print Nat.le
#check @Nat.le.refl
#check @Nat.le.step

-- Nat.le is MyLe with notation: same constructors, real ≤.
example : 2 ≤ 4 := Nat.le.step (Nat.le.step (Nat.le.refl))
example : 2 ≤ 4 := by decide
example : 2 ≤ 4 := by omega

theorem le_of_le_succ (n m : Nat) (h : n ≤ m + 1) (hne : n ≠ m + 1) : n ≤ m := by
  cases h with
  | refl => exact absurd rfl hne
  | step h' => exact h'

-- ### Using a derivation: induction

theorem my_le_trans (n m k : Nat) (h₁ : n ≤ m) (h₂ : m ≤ k) : n ≤ k := by
  induction h₂ with
  | refl => exact h₁
  | step _ ih => exact Nat.le.step ih

theorem succ_le_succ (n m : Nat) (h : n ≤ m) : n + 1 ≤ m + 1 := by
  induction h with
  | refl => exact Nat.le.refl
  | step _ ih => exact Nat.le.step ih

theorem le_of_succ_le (n m : Nat) (h : n + 1 ≤ m) : n ≤ m := by
  induction h with
  | refl => exact Nat.le.step Nat.le.refl
  | step _ ih => exact Nat.le.step ih

-- ### Compared with a formula

theorem exists_add_eq_of_le (n m : Nat) (h : n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by omega⟩

theorem le_of_exists_add_eq (n m : Nat) (h : ∃ k, n + k = m) : n ≤ m := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => exact Nat.le.refl
  | succ k ih => exact Nat.le.step ih

theorem le_iff_exists_add_eq (n m : Nat) : n ≤ m ↔ ∃ k, n + k = m :=
  ⟨exists_add_eq_of_le n m, le_of_exists_add_eq n m⟩

-- ### Compared with a computation

-- From homework 3.
/-- `isLe n m = true` exactly when `n ≤ m`. -/
def isLe : Nat → Nat → Bool :=
  fun
  | 0, _ => true
  | _ + 1, 0 => false
  | n + 1, m + 1 => isLe n m

theorem my_zero_le (m : Nat) : 0 ≤ m := by
  induction m with
  | zero => exact Nat.le.refl
  | succ m ih => exact Nat.le.step ih

theorem le_of_isLe (n m : Nat) : isLe n m = true → n ≤ m := by
  induction n generalizing m with
  | zero => intro _; exact my_zero_le m
  | succ n ih =>
    cases m with
    | zero =>
      intro h
      rw [isLe] at h
      contradiction
    | succ m =>
      intro h
      rw [isLe] at h
      exact succ_le_succ n m (ih m h)

theorem isLe_refl (n : Nat) : isLe n n = true := by
  induction n with
  | zero => rw [isLe]
  | succ n ih => rw [isLe, ih]

theorem isLe_succ_right (n m : Nat) : isLe n m = true → isLe n (m + 1) = true := by
  induction n generalizing m with
  | zero => intro _; rw [isLe]
  | succ n ih =>
    cases m with
    | zero =>
      intro h
      rw [isLe] at h
      contradiction
    | succ m =>
      intro h
      rw [isLe] at h
      rw [isLe]
      exact ih m h

theorem isLe_of_le (n m : Nat) : n ≤ m → isLe n m = true := by
  intro h
  induction h with
  | refl => exact isLe_refl n
  | step _ ih => exact isLe_succ_right n _ ih

theorem isLe_iff_le (n m : Nat) : isLe n m = true ↔ n ≤ m :=
  ⟨le_of_isLe n m, isLe_of_le n m⟩

-- A computation that agrees with a predicate is what `Decidable` packages (see below).

-- ## Even and odd

inductive MyEven : Nat → Prop where
  | zero : MyEven 0
  | add_two {n : Nat} : MyEven n → MyEven (n + 2)

inductive MyOdd : Nat → Prop where
  | one : MyOdd 1
  | add_two {n : Nat} : MyOdd n → MyOdd (n + 2)

example : MyEven 4 := MyEven.add_two (MyEven.add_two MyEven.zero)

example : MyOdd 5 := by
  repeat first | exact MyOdd.one | apply MyOdd.add_two

theorem not_even_one : ¬ MyEven 1 := by
  intro h
  cases h

theorem not_even_three : ¬ MyEven 3 := by
  intro h
  cases h with
  | add_two h' => cases h'

theorem even_add (n m : Nat) (hn : MyEven n) (hm : MyEven m) : MyEven (n + m) := by
  induction hn with
  | zero => simpa using hm
  | add_two _ ih =>
    rw [Nat.add_right_comm]
    exact MyEven.add_two ih

theorem odd_succ_of_even (n : Nat) (h : MyEven n) : MyOdd (n + 1) := by
  induction h with
  | zero => exact MyOdd.one
  | add_two _ ih => exact MyOdd.add_two ih

theorem even_succ_of_odd (n : Nat) (h : MyOdd n) : MyEven (n + 1) := by
  induction h with
  | one => exact MyEven.add_two MyEven.zero
  | add_two _ ih => exact MyEven.add_two ih

-- ### Compared with a formula

theorem even_two_mul (n : Nat) : MyEven (2 * n) := by
  induction n with
  | zero => exact MyEven.zero
  | succ n ih =>
    rw [Nat.mul_succ]
    exact MyEven.add_two ih

theorem exists_two_mul_eq_of_even (n : Nat) (h : MyEven n) : ∃ k, n = 2 * k := by
  induction h with
  | zero => exact ⟨0, rfl⟩
  | add_two _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by omega⟩

theorem even_iff_exists (n : Nat) : MyEven n ↔ ∃ k, n = 2 * k :=
  ⟨exists_two_mul_eq_of_even n, fun ⟨k, hk⟩ => hk ▸ even_two_mul k⟩

-- ### Compared with a computation: Parity

/-- `n` is twice `k`, or twice `k` plus one. The value `k` is stored. -/
inductive Parity (n : Nat) : Type where
  | even (k : Nat) (h : n = 2 * k)
  | odd (k : Nat) (h : n = 2 * k + 1)

def parity : (n : Nat) → Parity n
  | 0 => .even 0 rfl
  | n + 1 =>
    match parity n with
    | .even k h => .odd k (by omega)
    | .odd k h => .even (k + 1) (by omega)

def half (n : Nat) : Nat :=
  match parity n with
  | .even k _ => k
  | .odd k _ => k

#eval half 7

theorem exists_two_mul_or (n : Nat) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 :=
  match parity n with
  | .even k h => ⟨k, Or.inl h⟩
  | .odd k h => ⟨k, Or.inr h⟩

-- A def cannot pattern-match on a proof of `∃ k, ...` to pull `k` out: erased
-- Prop content leaves nothing to branch on at runtime.
--   def half' (n : Nat) : Nat :=
--     match exists_two_mul_or n with
--     | ⟨k, _⟩ => k
--   error: recursor `Exists.casesOn` can only eliminate into `Prop`

-- ## Decidable: the bridge

#print Decidable

-- Same shape as Parity: each constructor stores a proof. An instance is an algorithm.

instance (n : Nat) : Decidable (MyEven n) :=
  match parity n with
  | .even k h => isTrue (h ▸ even_two_mul k)
  -- The rules give no way in, so switch to the formula and let `omega` finish.
  | .odd k h => isFalse fun he => by
      obtain ⟨k', hk'⟩ := exists_two_mul_eq_of_even n he
      omega

example : MyEven 10 := by decide
#eval decide (MyEven 10)

-- ## Collatz

def collatzStep (n : Nat) : Nat :=
  match parity n with
  | .even k _ => k
  | .odd _ _ => 3 * n + 1

theorem collatzStep_two_mul (n : Nat) : collatzStep (2 * n) = n := by
  unfold collatzStep
  split <;> omega

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => iterate f k (f a)

#eval iterate collatzStep 8 6
#eval iterate collatzStep 111 27

/-- `0` and `1` are Collatz-finite, and so is any `n` whose step is. -/
inductive CollatzFinite : Nat → Prop where
  | zero : CollatzFinite 0
  | one : CollatzFinite 1
  | step {n : Nat} : CollatzFinite (collatzStep n) → CollatzFinite n

example : CollatzFinite 6 :=
  CollatzFinite.step (CollatzFinite.step (CollatzFinite.step (CollatzFinite.step
    (CollatzFinite.step (CollatzFinite.step (CollatzFinite.step
      (CollatzFinite.step CollatzFinite.one)))))))

example : CollatzFinite 6 := by
  repeat first | exact CollatzFinite.one | apply CollatzFinite.step

example : CollatzFinite 7 := by
  repeat first | exact CollatzFinite.one | apply CollatzFinite.step

-- The conjecture is a Prop; nobody has a proof of it.
def CollatzConjecture : Prop := ∀ n, CollatzFinite n

-- `CollatzFinite` is the core; the formula is `∃ k, iterate collatzStep k n = 1`
-- (homework); no computation that decides it is known.

end Lecture04

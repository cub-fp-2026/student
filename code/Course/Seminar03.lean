/-
# Seminar 3
-/

import Mathlib.Tactic

namespace Seminar03

-- ## Round 1 — rfl or induction

inductive MyNat where
  | zero
  | succ (n : MyNat)
  deriving Repr

namespace MyNat

def add : MyNat → MyNat → MyNat
  | n, .zero => n
  | n, .succ m => .succ (add n m)

theorem add_zero (n : MyNat) : add n .zero = n := rfl

theorem add_succ (n m : MyNat) :
    add n (.succ m) = .succ (add n m) := rfl

/-- Can this be proved by computation? -/
theorem add_one (n : MyNat) :
    add n (.succ .zero) = .succ n := by
  sorry

/-- Try cases n, inspect the stuck goal, then restart with induction n. -/
theorem zero_add (n : MyNat) :
    add .zero n = n := by
  sorry

/-- Choose the induction variable from the definition of add. -/
theorem succ_add (n m : MyNat) :
    add (.succ n) m = .succ (add n m) := by
  sorry

-- ## Round 2 — induction as a recursor

#check @MyNat.rec
#check @congrArg

/-- Write the proof of zero_add using MyNat.rec. -/
theorem zero_add_term (n : MyNat) :
    add .zero n = n :=
  MyNat.rec
    (motive := fun k => add .zero k = k)
    (by sorry)
    (fun k ih => by sorry)
    n

#print zero_add
#print zero_add_term

/-- Equal successors have equal predecessors. No induction needed. -/
theorem succ_injective (n m : MyNat) (h : succ n = succ m) :
    n = m := by
  sorry

end MyNat

-- ## Round 3 — recursive functions and specifications

/-
Define multiplication by recursion on the second argument.
-/
def mulRec : Nat → Nat → Nat :=
  sorry

theorem mulRec_eq (n m : Nat) :
    mulRec n m = n * m := by
  sorry

/-- First prove by induction on k; then prove again using mulRec_eq. -/
theorem mulRec_add (n m k : Nat) :
    mulRec n (m + k) = mulRec n m + mulRec n k := by
  sorry

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

theorem double_succ (n : Nat) :
    double (n + 1) = double n + 2 := rfl

-- Homework ex13. Prove by induction on m.
theorem double_add (n m : Nat) :
    double (n + m) = double n + double m := by
  sorry

-- Given from the lecture.
theorem double_eq_two_mul (n : Nat) :
    double n = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [double_succ, ih, Nat.mul_succ]

/-- Use double_eq_two_mul and calc, not induction. -/
theorem double_double (n : Nat) :
    double (double n) = 4 * n := by
  sorry

def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

-- Homework ex15.
theorem half_double (n : Nat) :
    half (double n) = n := by
  sorry

-- ## Round 4 — generalizing the induction hypothesis

def doubleAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => doubleAcc n (acc + 2)

/--
Prove correctness for every initial accumulator.
Compare induction n with induction n generalizing acc.
-/
theorem doubleAcc_correct (n acc : Nat) :
    doubleAcc n acc = double n + acc := by
  sorry

end Seminar03

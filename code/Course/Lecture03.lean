/-
# Lecture 3

- Inductive types: Nat from nothing
- Induction
- Recursive functions on Nat, proved correct
- calc and simp
-/

import Course.Islanders
import Batteries.Tactic.Init
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Hint
namespace Lecture03

-- ## MyBool

inductive MyBool : Type where
  | t
  | f
  deriving Repr

#print MyBool

def myNot : MyBool → MyBool := fun b =>
  match b with
  | .t => .f
  | .f => .t

theorem myNot_myNot_eq_id (b : MyBool) : myNot (myNot b) = b := by
  cases b
  · conv => lhs; arg 1; rewrite [myNot]
    conv => lhs; rewrite [myNot]
  · rfl

-- ## MySum

inductive MySum (A B : Type) where
  | inl (a : A)
  | inr (b : B)
  deriving Repr

#print MySum

def swapSum {A B : Type} : MySum A B → MySum B A
| .inl a => .inr a
| .inr b => .inl b

-- ## MyProd

/-
struct Prod {
  int x;
  int y;
};
-/

inductive MyProd (A B : Type) where
  | prod (a : A) (b : B)
  deriving Repr

#print MyProd

def swapProd {A B : Type} : MyProd A B → MyProd B A
| .prod a b => .prod b a

-- ## MyNat

inductive MyNat where
  | zero
  | succ (n : MyNat)
  deriving Repr

#print MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | n, .zero => n -- n + 0 = n
  | n, .succ m => .succ (add n m) -- n + (m + 1) = (n + m) + 1

-- 0 = 0
-- 1 = (0)
-- 2 = ((0))
-- 3 = (((0)))
-- 1 + 2 i.e. add (.succ .zero) (.succ (.succ .zero))

-- (0) + ((0)) ~> ((0) + (0)) ~> (((0) + 0)) ~> (((0)))

theorem add_zero (n : MyNat) : add n .zero = n := by rfl

-- rfl : a = a
-- here we have goal: 0 + n = n
-- if we do cases, we get
-- 0 + 0 = 0  (easy)
-- 0 + (m + 1) = m + 1 i.e. (0 + m) + 1 = m + 1, cancelling the + 1 gives 0 + m = m

theorem zero_add (n : MyNat) : add .zero n = n := by
  induction n
  case zero => sorry
  case succ m ih => sorry

theorem add_succ (n m : MyNat) : add n (.succ m) = .succ (add n m) := by sorry

theorem succ_add (n m : MyNat) : add (.succ n) m = .succ (add n m) := by sorry

end MyNat

-- ## Nat is MyNat with notation

#print Nat

example (n : Nat) : n + 0 = n := rfl

theorem zero_add' (n : Nat) : 0 + n = n := by sorry

theorem succ_ne_zero' (n : Nat) : n + 1 ≠ 0 := by
  intro h
  cases h

theorem succ_inj' (n m : Nat) (h : n + 1 = m + 1) : n = m := by
  cases h
  rfl

#check @Nat.zero_add
#check @Nat.succ_add
#check @Nat.add_comm
#check @Nat.add_assoc
#check @Nat.mul_succ
#check @Nat.succ_mul
#check @Nat.mul_add
#check @Nat.add_mul
#check @Nat.mul_comm

-- Great place to practice: https://adam.math.hhu.de/#/g/leanprover-community/nng4

-- ## Recursive functions on Nat, proved correct

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

example : double 3 = 6 := sorry

example : double 3 = 6 := sorry

theorem double_eq_mul_two (n : Nat) : double n = 2 * n := sorry

theorem double_eq_add_self (n : Nat) : double n = n + n := by sorry

-- ## calc and simp

theorem double_eq_add_self_calc (n : Nat) : double n = n + n := by sorry

theorem zero_chain (a b : Nat) : 0 + (a + 0) + (0 + b) = a + b := by sorry

theorem zero_chain' (a b : Nat) : 0 + (a + 0) + (0 + b) = a + b := by sorry

theorem double_eq_two_mul' (n : Nat) : double n = 2 * n := by sorry

example (n : Nat) : 0 + n = n := by sorry


-- ## Equality

def isEq : Nat → Nat → Bool
| 0, 0 => true
| n + 1, m + 1 => isEq n m
| _ + 1, 0 => false
| 0, _ + 1 => false

theorem isEq_implies_eq (n m : Nat) : isEq n m = true → n = m := by
  intro h
  induction n generalizing m
  case zero =>
    cases m
    · rfl
    · conv at h => lhs; rw [isEq]
      contradiction
  case succ n' ihn =>
    cases m
    case zero =>
      conv at h => lhs; rw [isEq]
      contradiction
    case succ m' =>
      conv at h => lhs; rw [isEq]
      congr
      apply ihn
      assumption

theorem eq_implies_isEq (n m : Nat) : n = m → isEq n m = true := by
  rintro rfl
  induction n
  · rfl
  · rw [isEq] at *
    assumption


end Lecture03

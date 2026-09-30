/-
# Seminar 5
- Products, sums, and optional results
- Recursive programs on lists
- Small list algorithms
- Membership as a specification
-/

import Mathlib

namespace Seminar05

-- ## Round 1 — data shapes

/-- Change how three values are grouped. -/
def reassociate {α β γ : Type} :
    (α × β) × γ → α × (β × γ) := by
  sorry

/-- Both alternatives contain the same type, so either one can be returned. -/
def mergeSame {α : Type} : Sum α α → α := by
  sorry

/-- Return the first two elements together,
or `none` if there are fewer than two. -/
def firstTwo? {α : Type} : List α → Option (α × α)
  | [] => sorry
  | [_] => sorry
  | x :: y :: _ => sorry

-- ## Round 2 — programs that follow the shape of a list

/-- Replace every element by two adjacent copies. -/
def duplicateEach {α : Type} : List α → List α
  | [] => sorry
  | x :: xs => sorry

/-- Homework ex01: keep the first, third, fifth, ... elements. -/
def dropEveryOther {α : Type} : List α → List α
  | [] => sorry
  | [x] => sorry
  | x :: _ :: xs => sorry

/-- These examples should close by computation. -/
example : duplicateEach [1, 2, 3] = [1, 1, 2, 2, 3, 3] := by
  sorry

example : dropEveryOther [1, 2, 3, 4, 5] = [1, 3, 5] := by
  sorry

-- ## Round 3 — algorithms as case distinctions

/-- Remove every zero from a list. -/
def removeZeros : List Nat → List Nat
  | [] => sorry
  | x :: xs =>
      if x = 0 then sorry
      else sorry

/-- Homework ex02: return the second-to-last element, if it exists. -/
def penultimate? {α : Type} : List α → Option α
  | [] => sorry
  | [_] => sorry
  | [x, _] => sorry
  | _ :: y :: z :: ys => sorry

/-- Keep the prefix before the first zero. -/
def takeUntilZero : List Nat → List Nat
  | [] => sorry
  | x :: xs =>
      if x = 0 then sorry
      else sorry

example : removeZeros [0, 3, 0, 2] = [3, 2] := by
  sorry

example : penultimate? [4, 7, 9] = some 7 := by
  sorry

example : takeUntilZero [3, 2, 0, 4] = [3, 2] := by
  sorry

-- ## Round 4 — trees

/-
A tree is either:

- a leaf with no stored value;
- a node containing a value and two smaller trees.
-/

inductive Tree (α : Type) where
  | leaf
  | node (left : Tree α) (value : α) (right : Tree α)
  deriving Repr, DecidableEq

/-
Build this tree:

        2
       / \
      1   3
-/
def exampleTree : Tree Nat := sorry

-- ## Round 5 — membership describes the output

/-- First build one concrete membership proof. -/
example : 2 ∈ duplicateEach [1, 2, 3] := by
  sorry

/-- `duplicateEach` changes multiplicity, but not which values occur. -/
theorem memDuplicateEach {α : Type} (x : α) (xs : List α) :
    x ∈ duplicateEach xs ↔ x ∈ xs := by
  sorry

/-- The output of `removeZeros` never contains zero. -/
theorem zeroNotMemRemoveZeros (xs : List Nat) :
    0 ∉ removeZeros xs := by
  sorry

/-
Discussion: does `memDuplicateEach` say that every value occurs the same
number of times in both lists? Why not?
-/

end Seminar05

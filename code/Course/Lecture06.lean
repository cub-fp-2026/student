/-
# Lecture 6 — Higher order function
-/
import Mathlib

namespace Lecture06

/-! ## `map` -/

def doubleAll : List Nat → List Nat
  | [] => []
  | x :: xs => 2 * x :: doubleAll xs

def isEvenAll : List Nat → List Bool
  | [] => []
  | x :: xs => (x % 2 = 0) :: isEvenAll xs

#eval doubleAll [3, 0, 5]
#eval isEvenAll [3, 0, 5]

def map (f : α → β) : List α → List β := by
  sorry
-- In the library: List.map.

example (xs : List Nat) : doubleAll xs = map (fun n => 2 * n) xs := by
  sorry

-- Nicer syntax:
-- - composition
-- - pipelines

def compose (g : β → γ) (f : α → β) : α → γ := by
  sorry
-- In the library: Function.comp, written `g ∘ f`.

theorem map_compose (g : β → γ) (f : α → β) (xs : List α) :
    map (compose g f) xs = map g (map f xs) := by
  sorry

example (g : β → γ) (f : α → β) : compose g f = g ∘ f := by
  sorry

-- `(· + 1)` is short for `fun x => x + 1`.
example : (· + 1) = fun (x : Nat) => x + 1 := by
  sorry

-- Partial application: `map (· + 1)` is a function that still waits for its list.
def incrementAll : List Nat → List Nat := by
  sorry

example : incrementAll [1, 2] = [2, 3] := by
  sorry

-- `x |> f` is `f x`, so a pipeline reads from left to right.
example (xs : List Nat) :
    (xs |> map (· + 1) |> map (2 * ·)) = map ((2 * ·) ∘ (· + 1)) xs := by
  sorry

/-! ## `filter` -/

def positiveOnly : List Nat → List Nat
  | [] => []
  | x :: xs => if x > 0 then x :: positiveOnly xs else positiveOnly xs

def belowTen : List Nat → List Nat
  | [] => []
  | x :: xs => if x < 10 then x :: belowTen xs else belowTen xs

def filter (p : α → Bool) : List α → List α := by
  sorry
-- In the library: List.filter.

example : filter (· > 0) [0, 8, 0, 4] = [8, 4] := by
  sorry

/-! ## `flatMap` -/

def stutter : List Nat → List Nat
  | [] => []
  | x :: xs => x :: x :: stutter xs

def flatMap (f : α → List β) : List α → List β := by
  sorry
-- In the library: List.flatMap.

example (xs : List Nat) : stutter xs = flatMap (fun x => [x, x]) xs := by
  sorry

/-! ## `foldr` -/

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

def product : List Nat → Nat
  | [] => 1
  | x :: xs => x * product xs

def foldr (step : α → β → β) (empty : β) : List α → β := by
  sorry
-- In the library: List.foldr.

example (xs : List Nat) : sum xs = foldr (· + ·) 0 xs := by
  sorry

def mapViaFold (f : α → β) (xs : List α) : List β := by
  sorry

def filterViaFold (p : α → Bool) (xs : List α) : List α := by
  sorry

#check @List.rec

theorem foldr_eq_rec (step : α → β → β) (empty : β) (xs : List α) :
    foldr step empty xs = List.rec (motive := fun _ => β) empty (fun x _ r => step x r) xs := by
  sorry

/-! ## `foldl` -/

def sumFrom (acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: xs => sumFrom (acc + x) xs

def foldl (step : β → α → β) (acc : β) : List α → β := by
  sorry
-- In the library: List.foldl.

example : foldr (fun x rest => x - rest) 0 [10, 3, 2] = 9 := by
  sorry
example : foldl (fun acc x => acc - x) 0 [10, 3, 2] = 0 := by
  sorry

def decimalValue (digits : List Nat) : Nat := by
  sorry

example : decimalValue [2, 0, 7] = 207 := by
  sorry

-- Use Lean's List.map, List.filter, List.foldr and List.foldl from here on.

/-! ## More library combinators -/

-- List.zipWith f combines corresponding elements with f, up to the shorter length.
#eval List.zipWith (· + ·) [1, 2, 3] [10, 20]
-- List.zip pairs corresponding elements.
#eval List.zip [1, 2, 3] ['a', 'b', 'c']
-- List.any p asks whether some element satisfies p.
#eval [1, 2, 3].any (· > 2)
-- List.all p asks whether every element satisfies p.
#eval [1, 2, 3].all (· > 2)
-- List.range n is [0, 1, ..., n - 1].
#eval List.range 5
-- List.scanl lists every accumulator that foldl passes through.
#eval List.scanl (· + ·) 0 [1, 2, 3]

/-! ## Folding a tree -/

inductive Tree (α : Type) where
  | empty
  | node (left : Tree α) (value : α) (right : Tree α)
  deriving Repr, DecidableEq

def Tree.sizeLoop : Tree α → Nat
  | .empty => 0
  | .node left _ right => left.sizeLoop + 1 + right.sizeLoop

def Tree.fold (empty : β) (node : β → α → β → β) : Tree α → β := by
  sorry

def oak : Tree Nat :=
  .node (.node .empty 4 .empty) 2 (.node .empty 7 (.node .empty 1 .empty))

def Tree.size (t : Tree α) : Nat := by
  sorry

example : oak.size = oak.sizeLoop := by
  sorry

def Tree.toList (t : Tree α) : List α := by
  sorry

example : oak.toList = [4, 2, 7, 1] := by
  sorry

def Tree.map (f : α → β) (t : Tree α) : Tree β := by
  sorry

example : (oak.map (· * 10)).toList = [40, 20, 70, 10] := by
  sorry

/-! ## A loop as a pipeline -/

def sumEvenSquaresLoop : List Nat → Nat
  | [] => 0
  | x :: xs => if x % 2 = 0 then x * x + sumEvenSquaresLoop xs else sumEvenSquaresLoop xs

def sumEvenSquares (xs : List Nat) : Nat := by
  sorry

theorem sumEvenSquaresLoop_eq_sumEvenSquares (xs : List Nat) :
    sumEvenSquaresLoop xs = sumEvenSquares xs := by
  sorry

/-! ## Pythagorean triples -/

-- All `(a, b, c)` with `0 < a < b < c < n` and `a * a + b * b = c * c`, ordered by `c`, then `b`.
def pythagoreanTriples (n : Nat) : List (Nat × Nat × Nat) := by
  sorry

example : pythagoreanTriples 14 = [(3, 4, 5), (6, 8, 10), (5, 12, 13)] := by
  sorry

end Lecture06

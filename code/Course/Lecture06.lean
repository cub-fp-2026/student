/-
# Lecture 6 — Higher order function
-/
import Mathlib

namespace Lecture06

#print List

/-! ## `map` -/

def doubleAll : List Nat → List Nat
  | [] => []
  | x :: xs => 2 * x :: doubleAll xs

def isEvenAll : List Nat → List Bool
  | [] => []
  | x :: xs => (x % 2 = 0) :: isEvenAll xs

#eval doubleAll [3, 0, 5]
#eval isEvenAll [3, 0, 5]

def map (f : α → β) : List α → List β
| [] => []
| x :: xs => f x :: map f xs
-- In the library: List.map.

example (xs : List Nat) : doubleAll xs = map (fun n => 2 * n) xs := by
  induction xs
  case nil =>
    rewrite [doubleAll, map]
    rfl
  case cons x xs ih =>
    rewrite [doubleAll, map, ih]
    rfl
  -- induction xs <;> simp [doubleAll, map, *]

-- Nicer syntax:
-- - composition
-- - pipelines

def compose (g : β → γ) (f : α → β) : α → γ :=
  fun a => g (f a)
-- In the library: Function.comp, written `g ∘ f`.

theorem map_compose (g : β → γ) (f : α → β) (xs : List α) :
    map (compose g f) xs = map g (map f xs) := by
  induction xs
  case nil => rfl
  case cons x xs ih => rw [map, map, map, compose, ih]

example (g : β → γ) (f : α → β) : compose g f = g ∘ f := by rfl

example (g : β → γ) (f : α → β) : map (g ∘ f) = map g ∘ map f := by
  funext
  apply map_compose

-- `(· + 1)` is short for `fun x => x + 1`.
example : (· + 1) = fun (x : Nat) => x + 1 := by rfl

-- Partial application: `map (· + 1)` is a function that still waits for its list.
def incrementAll : List Nat → List Nat := map (· + 1)

example : incrementAll [1, 2] = [2, 3] := by rfl

-- `x |> f` is `f x`, so a pipeline reads from left to right.
example (xs : List Nat) :
    (xs |> map (· + 1) |> map (2 * ·)) = map ((2 * ·) ∘ (· + 1)) xs := by
  symm
  apply map_compose

/-! ## `filter` -/

def positiveOnly : List Nat → List Nat
  | [] => []
  | x :: xs => if x > 0 then x :: positiveOnly xs else positiveOnly xs

def belowTen : List Nat → List Nat
  | [] => []
  | x :: xs => if x < 10 then x :: belowTen xs else belowTen xs

def filter (p : α → Bool) : List α → List α
| [] => []
| x :: xs =>
    let xs' := filter p xs
    if p x
    then x :: xs'
    else xs'
-- In the library: List.filter.

example : filter (· > 0) [0, 8, 0, 4] = [8, 4] := by rfl

/-! ## `flatMap` -/

def stutter : List Nat → List Nat
  | [] => []
  | x :: xs => x :: x :: stutter xs

def flatMap (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ flatMap f xs
-- In the library: List.flatMap.

example (xs : List Nat) : stutter xs = flatMap (fun x => [x, x]) xs := by
  induction xs
  case nil => rfl
  case cons x xs ih =>
    rewrite [stutter, flatMap, ih]
    rfl

/-! ## `foldr` -/

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

-- 1 :: 2 :: 3 :: []
-- 1 +  2 +  3 +  0
-- 1 *  2 *  3 *  1

def product : List Nat → Nat
  | [] => 1
  | x :: xs => x * product xs

def foldr (step : α → β → β) (empty : β) : List α → β
  | [] => empty
  | x :: xs => step x (foldr step empty xs)
-- In the library: List.foldr.

example (xs : List Nat) : sum xs = foldr (· + ·) 0 xs := by
  induction xs
  case nil => rfl
  case cons x xs ih => rw [sum, foldr, ih]

/-
def map (f : α → β) : List α → List β
| [] => []
| x :: xs => f x :: map f xs

def filter (p : α → Bool) : List α → List α
| [] => []
| x :: xs =>
    let xs' := filter p xs
    if p x then x :: xs' else xs'
-/

def mapViaFold (f : α → β) : List α → List β :=
  foldr (fun x ys => f x :: ys) []

def filterViaFold (p : α → Bool) : List α → List α :=
  foldr (fun x ys => if p x then x :: ys else ys) []

#check @List.rec

theorem foldr_eq_rec (step : α → β → β) (empty : β) (xs : List α) :
    foldr step empty xs = List.rec (motive := fun _ => β) empty (fun x _ r => step x r) xs := by
  sorry

/-! ## `foldl` -/

def sumFrom (acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: xs => sumFrom (acc + x) xs

def reverseHelper (acc : List α) : List α → List α
  | [] => acc
  | x :: xs => reverseHelper (x :: acc) xs
def reverse (xs : List α) := reverseHelper [] xs

example : reverseHelper [] [1, 2, 3] = [3, 2, 1] := by rfl

def foldl (step : β → α → β) (acc : β) : List α → β
  | [] => acc
  | x :: xs => foldl step (step acc x) xs
-- In the library: List.foldl.

example {xs: List α} : reverse xs = foldl (fun ys x => x :: ys) [] xs := by
  unfold reverse
  generalize [] = ys
  induction xs generalizing ys
  case nil => rfl
  case cons x xs ih =>
    rewrite [reverseHelper, foldl, ih]
    rfl

def decimalValue : List Nat → Nat := foldl (10 * · + ·) 0
def decimalValue' (digits : List Nat) : Nat := foldl (10 * · + ·) 0 digits

example : decimalValue [2, 0, 7] = 207 := by rfl

-- Use Lean's List.map, List.filter, List.foldr and List.foldl from here on.

/-! ## More library combinators -/

-- List.zip pairs corresponding elements.
#eval List.zip [1, 2, 3] ['a', 'b', 'c']
-- List.zipWith f combines corresponding elements with f, up to the shorter length.
#eval List.zipWith (· + ·) [1, 2, 3] [10, 20]
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

#check Tree.empty
#check Tree.node

def Tree.sizeLoop : Tree α → Nat
  | .empty => 0
  | .node left _ right => left.sizeLoop + 1 + right.sizeLoop

def Tree.fold (empty : β) (node : β → α → β → β) : Tree α → β
  | .empty => empty
  | .node lhs a rhs => node (lhs.fold empty node) a (rhs.fold empty node)

def oak : Tree Nat :=
  .node (.node .empty 4 .empty) 2 (.node .empty 7 (.node .empty 1 .empty))

def Tree.size (t : Tree α) : Nat := t.fold 0 (fun ls _ rs => ls + 1 + rs)

example : oak.size = oak.sizeLoop := by rfl

def Tree.toList (t : Tree α) : List α :=
  t.fold [] (fun ls a rs => ls ++ [a] ++ rs)

def Tree.toListPre (t : Tree α) : List α :=
  t.fold [] (fun ls a rs => [a] ++ ls ++ rs)

example : oak.toList = [4, 2, 7, 1] := by rfl

def Tree.map (f : α → β) (t : Tree α) : Tree β :=
  t.fold Tree.empty (fun ls a rs => Tree.node ls (f a) rs)

-- A map is a function of type (α → β) → F α → F β such that
-- map f ∘ map g = map (f ∘ g)
-- map id = id
-- This uniquely defines map for a large class of F.

example : (oak.map (· * 10)).toList = [40, 20, 70, 10] := by rfl

/-! ## A loop as a pipeline -/

def sumEvenSquaresLoop : List Nat → Nat
  | [] => 0
  | x :: xs => if x % 2 = 0 then x * x + sumEvenSquaresLoop xs else sumEvenSquaresLoop xs

def sumEvenSquares (xs : List Nat) : Nat :=
  xs |> filter (· % 2 = 0) |> map (fun x => x * x) |> sum

theorem sumEvenSquaresLoop_eq_sumEvenSquares (xs : List Nat) :
    sumEvenSquaresLoop xs = sumEvenSquares xs := by
  unfold sumEvenSquares
  induction xs
  case nil => rfl
  case cons x xs ih =>
    rw [sumEvenSquaresLoop, filter]
    by_cases h : x % 2 = 0
    · sorry
    · sorry

/-! ## Pythagorean triples -/

-- All `(a, b, c)` with `0 < a < b < c < n` and `a * a + b * b = c * c`, ordered by `c`, then `b`.
def pythagoreanTriples (n : Nat) : List (Nat × Nat × Nat) := by
  sorry

example : pythagoreanTriples 14 = [(3, 4, 5), (6, 8, 10), (5, 12, 13)] := by
  sorry

end Lecture06

/-
# Seminar 6
- A list against its own tail
- Generating lists from ranges
- Folds that carry state through one pass
- Combinators that return `Option`
-/

import Mathlib

namespace Seminar06

/-
Every `example` below is a required behaviour of the definition above it.
-/

-- ## Round 1 — a list against itself

/-- Each element paired with the element right after it. -/
def adjacentPairs (xs : List α) : List (α × α) := sorry

example : adjacentPairs [1, 2, 3] = [(1, 2), (2, 3)] := by
  sorry

example : adjacentPairs [7] = [] := by
  sorry

/-- The number of positions whose next element is strictly larger. -/
def countRises (xs : List Int) : Nat := sorry

example : countRises [1, 3, 2, 5, 5, 6] = 3 := by
  sorry

example : countRises [4, 3, 2] = 0 := by
  sorry

/-- Entry `i` is the largest of the first `i + 1` elements of `xs`. -/
def runningMax (xs : List Nat) : List Nat := sorry

example : runningMax [3, 1, 4, 1, 5, 2] = [3, 3, 4, 4, 5, 5] := by
  sorry

example : runningMax [] = [] := by
  sorry

/-- ★ The elements strictly larger than both of their neighbours, in order.
The first and last elements have only one neighbour and are never included. -/
def localMaxima (xs : List Int) : List Int := sorry

example : localMaxima [1, 5, 2, 2, 7, 3, 9] = [5, 7] := by
  sorry

example : localMaxima [1, 2, 2, 1] = [] := by
  sorry

-- ## Round 2 — generating lists

/-- The `n × n` multiplication table: row `i`, column `j` holds `i * j`,
for `1 ≤ i ≤ n` and `1 ≤ j ≤ n`. -/
def timesTable (n : Nat) : List (List Nat) := sorry

example : timesTable 3 = [[1, 2, 3], [2, 4, 6], [3, 6, 9]] := by
  sorry

example : timesTable 0 = [] := by
  sorry

/-- The positive divisors of `n` in increasing order; `0` has none here. -/
def divisors (n : Nat) : List Nat := sorry

example : divisors 12 = [1, 2, 3, 4, 6, 12] := by
  sorry

example : divisors 0 = [] := by
  sorry

/-- The perfect numbers below `n` in increasing order: positive `m` whose
divisors other than `m` itself add up to `m`. -/
def perfectBelow (n : Nat) : List Nat := sorry

example : perfectBelow 30 = [6, 28] := by
  sorry

/-- ★ All pairs `(a, b)` with `1 ≤ a ≤ b` and `a * a + b * b = n`, ordered by `a`. -/
def twoSquares (n : Nat) : List (Nat × Nat) := sorry

example : twoSquares 50 = [(1, 7), (5, 5)] := by
  sorry

example : twoSquares 65 = [(1, 8), (4, 7)] := by
  sorry

example : twoSquares 3 = [] := by
  sorry

-- ## Round 3 — folds that carry state

/-- The number of elements, their sum and their maximum (`0` for `[]`).
The definition is a single `List.foldl` over `xs`. -/
def stats (xs : List Nat) : Nat × Nat × Nat := sorry

example : stats [3, 1, 4, 1, 5] = (5, 14, 5) := by
  sorry

example : stats [] = (0, 0, 0) := by
  sorry

/-- Whether the parentheses in `cs` are balanced: no prefix closes more than it
has opened, and the whole list closes everything it opens. Characters other
than `(` and `)` are ignored. The definition is a single `List.foldl` over `cs`. -/
def balanced (cs : List Char) : Bool := sorry

example : balanced "(()())".toList = true := by
  sorry

example : balanced "(a)(b)".toList = true := by
  sorry

example : balanced "".toList = true := by
  sorry

example : balanced "(()".toList = false := by
  sorry

example : balanced ")(".toList = false := by
  sorry

example : balanced "())(()".toList = false := by
  sorry

/-- Replace each run of equal adjacent elements by a single copy. -/
def dedupAdjacent [DecidableEq α] (xs : List α) : List α := sorry

example : dedupAdjacent [1, 1, 2, 2, 2, 1, 3, 3] = [1, 2, 1, 3] := by
  sorry

example : dedupAdjacent ([] : List Nat) = [] := by
  sorry

/-- An account starts at `start`, and each move is added to it in turn.
The list holds the balance before any move, then the balance after each move. -/
def balances (start : Int) (moves : List Int) : List Int := sorry

example : balances 10 [-3, 5, -20] = [10, 7, 12, -8] := by
  sorry

example : balances 4 [] = [4] := by
  sorry

theorem foldl_add_start (a : Nat) (xs : List Nat) :
    xs.foldl (· + ·) a = a + xs.sum := by
  sorry

-- ## Round 4 — combinators that return `Option`

#eval [3, -1, 4, -5].find? (· < 0)
#eval [3, -1, 4, -5].findIdx? (· < 0)
#eval [1, 2, 3, 4].filterMap (fun x => if x % 2 = 0 then some (x * 10) else none)
#eval [(1, "one"), (2, "two")].lookup 2
#eval [1, 2, 5, 1].takeWhile (· < 3)
#eval [1, 2, 5, 1].dropWhile (· < 3)
#eval [1, 2, 5, 1].span (· < 3)
#eval [1, 2, 5, 1].partition (· < 3)
#eval [1, 1, 2, 3, 3].splitBy (· == ·)
#eval ([] : List Nat).head?
#eval [3, 9, 2].max?
#eval (none : Option Nat).getD 0

/-- The values of the decimal digit characters in `cs`, in order. -/
def digitsIn (cs : List Char) : List Nat := sorry

example : digitsIn "a1b22c".toList = [1, 2, 2] := by
  sorry

example : digitsIn "abc".toList = [] := by
  sorry

/-- A phone book lists `(number, name)` entries. The name of the first entry
for `number`, or `"unknown"` if there is none. -/
def callerName (book : List (String × String)) (number : String) : String := sorry

def book : List (String × String) :=
  [("555-01", "Ada"), ("555-02", "Alan"), ("555-01", "Grace")]

example : callerName book "555-01" = "Ada" := by
  sorry

example : callerName book "555-99" = "unknown" := by
  sorry

/-- The names scoring at least `threshold`, then the names scoring below it,
each in their original order. -/
def splitPassFail (threshold : Nat) (results : List (String × Nat)) :
    List String × List String := sorry

example : splitPassFail 50 [("Ada", 90), ("Bob", 40), ("Cy", 50), ("Di", 10)] =
    (["Ada", "Cy"], ["Bob", "Di"]) := by
  sorry

/-- The smallest `k` such that the balance after the first `k` moves
(as in `balances`) is negative, or `none` if it never is. -/
def firstOverdraft? (start : Int) (moves : List Int) : Option Nat := sorry

example : firstOverdraft? 10 [-3, 5, -20, 30, -40] = some 3 := by
  sorry

example : firstOverdraft? 10 [-3, 5] = none := by
  sorry

example : firstOverdraft? (-1) [5] = some 0 := by
  sorry

theorem find?_eq_head?_filter (p : α → Bool) (xs : List α) :
    xs.find? p = (xs.filter p).head? := by
  sorry

/-- Our own `takeWhile`: the longest prefix whose elements all satisfy `p`. -/
def takeWhile (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: takeWhile p xs else []

/-- Our own `dropWhile`: what remains after that prefix. -/
def dropWhile (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then dropWhile p xs else x :: xs

/-- ★ -/
theorem takeWhile_append_dropWhile (p : α → Bool) (xs : List α) :
    takeWhile p xs ++ dropWhile p xs = xs := by
  sorry

end Seminar06

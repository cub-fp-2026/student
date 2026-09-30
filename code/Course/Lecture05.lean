/-
# Lecture 5 — Lists as programs
-/

import Mathlib

namespace Lecture05

-- ## Products and sums: both values, or one of two alternatives

inductive MySum (α β : Type) : Type where
  | inl : α → MySum α β
  | inr : β → MySum α β
  deriving Repr, DecidableEq

def MySum.swap : MySum α β → MySum β α
| .inl a => .inr a
| .inr b => .inl b

#print Sum -- ⊕ oplus

-- Use Lean's Sum from here on: its constructors are .inl and .inr.
example : (Sum.inl 2 : Nat ⊕ String).swap = .inr 2 := by rfl
-- Or has the alternatives of Sum, but lives in Prop rather than Type.

structure MyProd (α β : Type) where
  fst : α
  snd : β
  deriving Repr, DecidableEq

def MyProd.swap : MyProd α β → MyProd β α
| ⟨a, b⟩ => ⟨b, a⟩

#print Prod -- × x

-- Use Lean's Prod from here on: α × β, (a, b), .fst and .snd.
example : ((2, "hi") : Nat × String).fst = 2 := by rfl
example : ((2, "hi") : Nat × String).snd = "hi" := by rfl

-- ## Building a list

inductive MyList (α : Type) where
  | nil
  | cons (x : α) (xs : MyList α)
  deriving Repr, DecidableEq

-- representing the list [1, 2]:
example : List Nat := .cons 1 (.cons 2 .nil)

-- we want to send n to the list [n, n-1, ..., 0]
def listOfNumbers : Nat → MyList Nat
| 0 => .cons 0 .nil
| n + 1 => .cons (n+1) (listOfNumbers n)

def MyList.length : MyList α → Nat
| .nil => 0
| .cons _ xs => xs.length + 1

example (n : Nat) : (listOfNumbers n).length = n + 1 := by
  induction n
  case zero => rfl
  case succ n' ih => rw [listOfNumbers, MyList.length, ih]

-- we write ++ for append
-- .nil ++ ys = ys
-- xs ++ .nil = xs
-- .cons x xs ++ ys = .cons x (xs ++ ys)
-- xs ++ .cons y ys = ??? can't express in terms of xs ++ ys
def MyList.append : MyList α → MyList α → MyList α
| .nil, ys => ys
| .cons x xs, ys => .cons x (xs.append ys)

-- reverse (.cons x xs) = ???
-- option 1: reverse xs ++ (.cons x nil)
--   bad: quadratic time because we do append on the lhs at each step
def MyList.reverseHelper : MyList α → MyList α → MyList α
| .nil, acc => acc
| .cons x xs, acc => xs.reverseHelper (.cons x acc)

example : (.cons 1 (.cons 2 .nil) : MyList Nat).reverseHelper (.cons 3 (.cons 4 .nil))
          = (.cons 2 (.cons 1 (.cons 3 (.cons 4 .nil)))) := by
  conv => lhs; rewrite [MyList.reverseHelper, MyList.reverseHelper, MyList.reverseHelper]

def MyList.reverseSlow : MyList α → MyList α
| .nil => .nil
| .cons x xs => xs.reverseSlow.append (.cons x .nil)

def MyList.reverse : MyList α → MyList α := fun xs => xs.reverseHelper .nil

theorem reverseCorrect (xs : MyList α) : xs.reverse = xs.reverseSlow := by sorry

-- Use Lean's List from here on: [] and :: are its constructors.
def sum : List Nat → Nat
| [] => 0
| x :: xs => x + sum xs

-- zip [1, 2, 3] [4, 5, 6] = [(1, 4), (2, 5), (3, 6)]
def zip : List α → List β → List (α × β)
| x :: xs, y :: ys => (x, y) :: zip xs ys
| _, _ => []

-- ## Optional results: a value or no value

#print Option

inductive MyOption (α : Type) where
  | none
  | some (a : α)
  deriving Repr, DecidableEq

def MyOption.getD (fallback : α) : MyOption α → α
| .none => fallback
| .some a => a

-- Use Lean's Option from here on: its constructors are none and some.
def last? : List α → Option α
| [] => .none
| [a] => .some a
| x :: xs => last? xs

example : last? ([] : List Nat) = none := by rfl
example : last? [4, 7, 9] = some 9 := by rfl

-- ## Algorithms as case distinctions

def dedupAdjacent : List Nat → List Nat
| [] => []
| [x] => [x]
| x1 :: x2 :: xs =>
    if x1 = x2
    then dedupAdjacent (x2 :: xs)
    else x1 :: dedupAdjacent (x2 :: xs)

example : dedupAdjacent [1, 1, 2, 2, 1] = [1, 2, 1] := by
  rw [dedupAdjacent]
  split
  · rfl
  · contradiction

def insertOrdered (n : Nat) : List Nat → List Nat
| [] => [n]
| x :: xs =>
    if x ≤ n
    then x :: insertOrdered n xs
    else n :: x :: xs

def insertionSort : List Nat → List Nat
| [] => []
| n :: xs => insertOrdered n (insertionSort xs)

example : insertionSort [3, 1, 2, 1] = [1, 1, 2, 3] := by rfl

-- ## Membership: a statement about the output, not an execution trace

inductive MyMem (x : α) : List α → Prop where
  | head : MyMem x (x :: xs)
  | tail : MyMem x xs → MyMem x (y :: xs)

example : MyMem 2 [1, 2, 3] := by
  apply MyMem.tail
  apply MyMem.head
example : ¬MyMem 0 [] := by
  intro h
  cases h
#print List.Mem -- ∈ in

-- x ∈ xs abbreviates List.Mem x xs; its constructors are head and tail.
example : 2 ∈ [1, 2, 3] := by repeat constructor
example : 4 ∉ [1, 2, 3] := by
  intro h
  cases h
  case tail h =>
    cases h
    case tail h =>
      cases h
      case tail h =>
        cases h

-- Membership does not record the multiplicity or order of elements.
lemma mem_insertOrdered (n x : Nat) (xs : List Nat) :
    x ∈ insertOrdered n xs ↔ x = n ∨ x ∈ xs := by
  induction xs
  case nil =>
    rw [insertOrdered]
    constructor
    · intro h
      cases h
      case head => left; rfl
      case tail h => cases h
    · rintro (h | h)
      · rw [h]
        constructor
      · cases h
  case cons x' xs' ih =>
    rw [insertOrdered]
    split
    · constructor
      · intro h
        cases h
        case head => right; constructor
        case tail h =>
          have h' : x ∈ insertOrdered n xs' := h
          rw [ih] at h'
          sorry
      · sorry
    · sorry

lemma mem_insertionSort (x : Nat) (xs : List Nat) :
    x ∈ insertionSort xs ↔ x ∈ xs := by
  sorry

end Lecture05

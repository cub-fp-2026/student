/-
# Lecture 8 — Typeclasses
-/
import Mathlib

namespace Lecture08

-- ## The same sum, three times

def sumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNat xs

def sumInt : List Int → Int
  | [] => 0
  | x :: xs => x + sumInt xs

def concatAll : List String → String
  | [] => ""
  | x :: xs => x ++ concatAll xs

-- ## The same fold, three times

def sumNat' : List Nat → Nat := by
  sorry
def sumInt' : List Int → Int := by
  sorry
def concatAll' : List String → String := by
  sorry

example (xs : List Nat) : sumNat xs = sumNat' xs := by
  sorry

-- ## Passing the operations explicitly

structure Combine (α : Type) where

def combineAll (c : Combine α) : List α → α := by
  sorry

def natAdd : Combine Nat := by
  sorry
def natMul : Combine Nat := by
  sorry

example : combineAll natAdd [2, 3, 4] = 9 := by
  sorry
example : combineAll natMul [2, 3, 4] = 24 := by
  sorry

-- ## Letting Lean find the operations

class MyMonoid (α : Type) where
  unit : α
  op : α → α → α

instance : MyMonoid Nat := by
  sorry

instance : MyMonoid String := by
  sorry

instance : MyMonoid (List α) := by
  sorry

def mconcat [MyMonoid α] : List α → α := by
  sorry

example : mconcat [2, 3, 4] = 9 := by
  sorry
example : mconcat ["ab", "c"] = "abc" := by
  sorry
example : mconcat [[1], [2, 3]] = [1, 2, 3] := by
  sorry

-- The instance is chosen by the type, even when no argument has that type.
example : (MyMonoid.unit : String) = "" := by
  sorry

#check @List.sum

-- ## One type, two monoids

structure Product where
  val : Nat
  deriving Repr, DecidableEq

instance : MyMonoid Product := by
  sorry

example : mconcat [Product.mk 2, ⟨3⟩, ⟨4⟩] = ⟨24⟩ := by
  sorry

-- ## A second class: defaults

class MyInhabited (α : Type) where
  default : α

instance : MyInhabited Nat := by
  sorry

instance : MyInhabited String := by
  sorry

instance [MyInhabited α] [MyInhabited β] : MyInhabited (α × β) := by
  sorry

example : (MyInhabited.default : Nat × String) = (0, "") := by
  sorry

#print Inhabited
#check @List.head!

-- `Inhabited` promises only that the type has an element, not which one.

-- A class can extend another.
class MyMonoid' (α : Type) extends MyInhabited α where
  op : α → α → α

#check @MyMonoid'.toMyInhabited
#print Monoid

-- ## Operators are instances

#check (2 + 3 : Nat)
#check @HAdd.hAdd
#print Add
#synth Add Nat

structure Point where
  x : Int
  y : Int
  deriving Repr

instance : Add Point := by
  sorry

example : (⟨1, 2⟩ + ⟨3, 4⟩ : Point) = ⟨4, 6⟩ := by
  sorry

-- `deriving Repr` writes the instance that `#eval` uses.
#synth Repr Point

infixl:65 " ⋄ " => MyMonoid.op

example : "ab" ⋄ "c" = "abc" := by
  sorry

#check (2 == 3)
#check (2 = 3)
#print BEq
#print DecidableEq

-- The same idea elsewhere: Haskell type classes, Rust traits, Swift protocols, Scala givens.

-- ## Laws

example [MyMonoid α] (xs ys : List α) :
    mconcat (xs ++ ys) = mconcat xs ⋄ mconcat ys := by
  sorry

structure Diff where
  val : Int
  deriving Repr, DecidableEq

instance : MyMonoid Diff := ⟨⟨0⟩, fun a b => ⟨a.val - b.val⟩⟩

example : mconcat ([⟨10⟩, ⟨5⟩] ++ [⟨3⟩] : List Diff) = ⟨8⟩ := by
  sorry
example : (mconcat [⟨10⟩, ⟨5⟩] ⋄ mconcat [⟨3⟩] : Diff) = ⟨2⟩ := by
  sorry

class LawfulMonoid (α : Type) [MyMonoid α] : Prop where

#print LawfulBEq

instance : LawfulMonoid Nat := by
  sorry

instance : LawfulMonoid (List α) := by
  sorry

theorem mconcat_append [MyMonoid α] [LawfulMonoid α] (xs ys : List α) :
    mconcat (xs ++ ys) = mconcat xs ⋄ mconcat ys := by
  sorry

end Lecture08

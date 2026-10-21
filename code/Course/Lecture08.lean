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

def sumNat' : List Nat → Nat := List.foldr (· + ·) 0
def sumInt' : List Int → Int := List.foldr (· + ·) 0
def concatAll' : List String → String := List.foldr (· ++ ·) ""

example (xs : List Nat) : sumNat xs = sumNat' xs := by
  induction xs
  · rfl
  · simp [sumNat, sumNat', *]

-- ## Passing the operations explicitly

structure Combine (α : Type) where
  op : α → α → α
  default : α

def combineAll (c : Combine α) : List α → α :=
  List.foldr c.op c.default

def natAdd : Combine Nat := ⟨ (· + ·), 0 ⟩
def natMul : Combine Nat := {
  op := fun x y => x * y
  default := 1
}

example : combineAll natAdd [2, 3, 4] = 9 := rfl
example : combineAll natMul [2, 3, 4] = 24 := rfl

-- ## Letting Lean find the operations

class MyMonoid (α : Type) where
  unit : α
  op : α → α → α

instance : MyMonoid Nat where
  unit := 0
  op := (· + ·)

instance : MyMonoid String := {
  unit := ""
  op x y := x ++ y
}

instance : MyMonoid (List α) where
  unit := []
  op xs ys := xs ++ ys

-- def combineAll (c : Combine α) : List α → α :=
--   List.foldr c.op c.default

def mconcat [MyMonoid α] : List α → α :=
  List.foldr MyMonoid.op MyMonoid.unit

example : mconcat [2, 3, 4] = 9 := by rfl
example : mconcat ["ab", "c"] = "abc" := by rfl
example : mconcat [[1], [2, 3]] = [1, 2, 3] := by rfl

-- The instance is chosen by the type, even when no argument has that type.
example : (MyMonoid.unit : String) = "" := by rfl

#check @List.sum

-- Don't do this at home.
instance : Add String where
  add x y := x ++ y

instance : Zero String where
  zero := "zero"

#print List.sum
#eval List.sum ["a", "b"]
-- "a" :: ("b" :: [])
-- "a" ++ ("b" ++ "zero")

-- ## One type, two monoids

structure Product where
  val : Nat
  deriving Repr, DecidableEq

instance : MyMonoid Product where
  unit := ⟨1⟩
  op x y := ⟨x.val * y.val⟩

example : mconcat [Product.mk 2, ⟨3⟩, ⟨4⟩] = ⟨24⟩ := by rfl

-- ## A second class: defaults

class MyInhabited (α : Type) where
  default : α

instance : MyInhabited Nat := ⟨0⟩

instance : MyInhabited String := ⟨""⟩

instance [MyInhabited α] [MyInhabited β] : MyInhabited (α × β) where
  default := ⟨MyInhabited.default, MyInhabited.default⟩

example : (MyInhabited.default : Nat × String) = (0, "") := by rfl

#print Inhabited
#check @List.head?
#check @List.head!

-- `Inhabited` promises only that the type has an element, not which one.

-- A class can extend another.
class MyMonoid' (α : Type) extends MyInhabited α where
  op : α → α → α

#check @MyMonoid'.toMyInhabited
#print Monoid

-- ## Operators are instances

#check (2 + 3 : Int)
#check @HAdd.hAdd
#print Add
#synth Add Nat
#print instAddNat
#print Nat.add

structure Point where
  x : Int
  y : Int
  deriving Repr


instance : Add Point where
  add
  | .mk x1 y1, .mk x2 y2 => ⟨x1 + x2, y1 + y2⟩

example : (⟨1, 2⟩ + ⟨3, 4⟩ : Point) = ⟨4, 6⟩ := by rfl

def ex_point : Point := ⟨3, 4⟩
#eval ex_point
-- `deriving Repr` writes the instance that `#eval` uses.
#synth Repr Point
#print instReprPoint
#print instReprPoint.repr


infixl:65 " ⋄ " => MyMonoid.op

example : "ab" ⋄ "c" = "abc" := by rfl

#check (2 == 3)
#check (2 = 3)
#print BEq
#print DecidableEq

-- The same idea elsewhere: Haskell type classes, Rust traits, Swift protocols, Scala givens.

-- ## Laws

example [MyMonoid α] (xs ys : List α) :
    mconcat (xs ++ ys) = mconcat xs ⋄ mconcat ys := by
  induction xs
  case nil =>
    simp
    conv => rhs; arg 1; simp [mconcat]
    -- stuck!
    sorry
  case cons => sorry

structure Diff where
  val : Int
  deriving Repr, DecidableEq

instance : MyMonoid Diff := ⟨⟨0⟩, fun a b => ⟨a.val - b.val⟩⟩

example : mconcat ([⟨10⟩, ⟨5⟩] ++ [⟨3⟩] : List Diff) = ⟨8⟩ := by rfl
example : (mconcat [⟨10⟩, ⟨5⟩] ⋄ mconcat [⟨3⟩] : Diff) = ⟨2⟩ := by rfl

class LawfulMonoid (α : Type) [MyMonoid α] : Prop where
  -- unit ⋄ x = x
  left_unit (x : α) : MyMonoid.unit ⋄ x = x
  -- x ⋄ unit = x
  right_unit (x : α) : x ⋄ MyMonoid.unit = x
  -- (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z)
  assoc (x y z : α) : (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z)

#print LawfulBEq

-- instance : MyMonoid Nat where
--   unit := 0
--   op := (· + ·)

instance : LawfulMonoid Nat where
  left_unit x := by
    conv => lhs; arg 1; change 0
    conv => lhs; change 0 + x
    exact Nat.zero_add x
  right_unit x := by
    conv => lhs; change x + 0
    rfl
  assoc := Nat.add_assoc

instance : LawfulMonoid (List α) where
  left_unit _ := rfl
  right_unit := List.append_nil
  assoc := List.append_assoc

theorem mconcat_append [MyMonoid α] [LawfulMonoid α] (xs ys : List α) :
    mconcat (xs ++ ys) = mconcat xs ⋄ mconcat ys := by
  induction xs
  case nil =>
    conv => lhs; change mconcat ys
    conv => rhs; arg 1; change MyMonoid.unit
    symm
    apply LawfulMonoid.left_unit
  case cons x xs ih =>
    conv => lhs; change x ⋄ mconcat (xs ++ ys)
    conv =>
      rhs
      change x ⋄ mconcat xs ⋄ mconcat ys
      rw [LawfulMonoid.assoc]
    rw [ih]

end Lecture08

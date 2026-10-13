/-
# Lecture 7 — Indexed data structures
-/
import Mathlib

namespace Lecture07

/-! ## Lists that may be too short -/

#eval [1, 2, 3].head?
#eval ([] : List Nat).head?
#check @List.head

/-! ## A length in the type -/

inductive Vec (α : Type) : Nat → Type where

namespace Vec

def toList : Vec α n → List α := by
  sorry

-- The result type depends on the argument.
def ofList : (xs : List α) → Vec α xs.length := by
  sorry

theorem toList_ofList (xs : List α) : (ofList xs).toList = xs := by
  sorry

/-! ## Functions that cannot fail -/

def head : Vec α (n + 1) → α := by
  sorry

def tail : Vec α (n + 1) → Vec α n := by
  sorry

example : (ofList [1, 2, 3]).head = 1 := by
  sorry
-- #check (nil : Vec Nat 0).head

/-! ## Shapes the type promises -/

def map (f : α → β) : Vec α n → Vec β n := by
  sorry

def zip : Vec α n → Vec β n → Vec (α × β) n := by
  sorry

def replicate : (n : Nat) → α → Vec α n := by
  sorry

theorem map_map (f : α → β) (g : β → γ) (v : Vec α n) : (v.map f).map g = v.map (g ∘ f) := by
  sorry

/-! ## Arithmetic in types -/

example (n : Nat) : n + 0 = n := by
  rfl
-- example (n : Nat) : 0 + n = n := by
--   rfl

def append : Vec α m → Vec α n → Vec α (n + m) := by
  sorry

def append' : Vec α m → Vec α n → Vec α (m + n) := by
  sorry

/-! ## Matching on an index -/

-- Drops the last element.
def dropLast : Vec α (n + 1) → Vec α n := by
  sorry

example : (ofList [1, 2, 3]).dropLast = ofList [1, 2] := by
  sorry

/-! ## Positions -/

#print Fin

def get : Vec α n → Fin n → α := by
  sorry

example : (ofList [10, 20, 30]).get 2 = 30 := by
  sorry
-- #eval (ofList [10, 20, 30]).get ⟨3, by decide⟩

theorem get_replicate (n : Nat) (x : α) (i : Fin n) : (replicate n x).get i = x := by
  sorry

end Vec

/-! ## Length as a proof instead -/

def SizedList (α : Type) (n : Nat) : Type := { xs : List α // xs.length = n }

def SizedList.map (f : α → β) (v : SizedList α n) : SizedList β n := by
  sorry

-- In the library: Vector, an array together with a proof about its size.
#print Vector

/-! ## Trees of a fixed height -/

-- The values sit at the leaves.
inductive Perfect (α : Type) : Nat → Type where
  | leaf : α → Perfect α 0
  | node : Perfect α h → Perfect α h → Perfect α (h + 1)

-- The leaves from left to right.
def Perfect.toVec : Perfect α h → Vec α (2 ^ h) := by
  sorry

example : (Perfect.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))).toVec =
    Vec.ofList [1, 2, 3, 4] := by
  sorry

/-! ## Expressions indexed by their type -/

inductive Ty where
  | nat
  | bool

abbrev Ty.Val : Ty → Type
  | .nat => Nat
  | .bool => Bool

inductive Expr : Ty → Type where
  | num : Nat → Expr .nat
  | truth : Bool → Expr .bool
  | add : Expr .nat → Expr .nat → Expr .nat
  | lt : Expr .nat → Expr .nat → Expr .bool
  | ite : Expr .bool → Expr t → Expr t → Expr t

-- #check Expr.add (.num 1) (.truth true)

def Expr.eval : Expr t → t.Val := by
  sorry

example : (Expr.ite (.lt (.num 1) (.num 2)) (.num 10) (.num 20)).eval = 10 := by
  sorry

end Lecture07

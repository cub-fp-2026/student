/-
# Lecture 7 — Indexed data structures
-/
import Mathlib

namespace Lecture07

/-! ## Lists that may be too short -/

#eval [1, 2, 3].head?
#eval ([] : List Nat).head?
#check @List.head?
#check @List.head

/-! ## A length in the type -/


#print List
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

#print Vec
#print Vec.nil

namespace Vec

def toList : Vec α n → List α
| .nil => .nil
| .cons x xs => .cons x (toList xs)

-- The result type depends on the argument.
def ofList : (xs : List α) → Vec α xs.length
| .nil => .nil
| .cons x xs => .cons x (ofList xs)

theorem toList_ofList (xs : List α) : (ofList xs).toList = xs := by
  induction xs
  case nil => rfl
  case cons x xs ih => rw [ofList, toList, ih]

/-! ## Functions that cannot fail -/

def head : Vec α (n + 1) → α
| .cons x _ => x

def tail : Vec α (n + 1) → Vec α n
| .cons _ xs => xs

example : (ofList [1, 2, 3]).head = 1 := by rfl
-- #check (nil : Vec Nat 0).head

/-! ## Shapes the type promises -/

def map (f : α → β) : Vec α n → Vec β n
| .nil => .nil
| .cons x xs => .cons (f x) (map f xs)

#eval List.zip [1, 2] [3]

def transport {x y : α} (F : α → Sort l) : x = y → F x → F y
| rfl => fun x => x

def transportVec {n m : ℕ} : n = m → Vec α n → Vec α m
| rfl => fun x => x

def eqIfSameLength (xs ys : List α) : Prop :=
  if h : xs.length = ys.length
  then transportVec h (ofList xs) = ofList ys
  else False

-- when is eqIfSameLength xs ys provable?

def zip : Vec α n → Vec β n → Vec (α × β) n
| .nil, .nil => .nil
| .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

def replicate : (n : Nat) → α → Vec α n
| 0, _ => .nil
| n + 1, a => .cons a (replicate n a)

#eval replicate 2 true
#check replicate 2 true
#eval toList (replicate 2 true)

/-! ## Arithmetic in types -/

example (n : Nat) : n + 0 = n := by rfl
-- example (n : Nat) : 0 + n = n := by rfl

#print Vec

def append : Vec α m → Vec α n → Vec α (n + m)
| .nil, ys => ys
| .cons x xs, ys => .cons x (append xs ys)

def append' : Vec α m → Vec α n → Vec α (m + n)
| .nil, ys => transportVec (by simp) ys -- or omega, etc.
| .cons x xs, ys => transportVec (by omega) (.cons x (append xs ys))

def append'' : Vec α m → Vec α n → Vec α (m + n)
| xs, .nil => xs
| xs, .cons y ys => sorry -- painful!

/-! ## Matching on an index -/

-- Drops the last element.
def dropLast : Vec α (n + 1) → Vec α n := by
  sorry

example : (ofList [1, 2, 3]).dropLast = ofList [1, 2] := by
  sorry

/-! ## Positions -/

#print Fin

def get : Vec α n → Fin n → α
| .nil, ⟨_, hk⟩ => by
    exfalso
    cases hk
| .cons x _, ⟨0, _⟩ => x
| .cons _ xs, ⟨k + 1, hk⟩ => get xs ⟨k, by omega⟩

example : (ofList [10, 20, 30]).get 2 = 30 := by
  sorry
-- #eval (ofList [10, 20, 30]).get ⟨3, by decide⟩

theorem get_replicate (n : Nat) (x : α) (i : Fin n) : (replicate n x).get i = x := by
  sorry

end Vec

/-! ## Length as a proof instead -/

def SizedList (α : Type) (n : Nat) : Type :=
  { xs : List α // xs.length = n }

def SizedList.map (f : α → β) (v : SizedList α n) : SizedList β n :=
  let ⟨xs, hxs⟩ := v
  ⟨List.map f xs, by simp; assumption⟩

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

inductive Expr : Ty → Type where
  | num : Nat → Expr .nat
  | truth : Bool → Expr .bool
  | add : Expr .nat → Expr .nat → Expr .nat
  | lt : Expr .nat → Expr .nat → Expr .bool
  | ite : Expr .bool → Expr t → Expr t → Expr t
  deriving Repr

#eval Expr.add (.num 1) (.num 2)
-- #check Expr.add (.num 1) (.truth true)

abbrev Ty.Val : Ty → Type
  | .nat => Nat
  | .bool => Bool

def Expr.eval : Expr t → t.Val
| .num n => n
| .truth b => b
| .add lhs rhs => lhs.eval + rhs.eval
| .lt lhs rhs => lhs.eval < rhs.eval
| .ite cond tb eb =>
    if cond.eval then tb.eval else eb.eval

#eval (Expr.add (.num 1) (.num 2)).eval
#eval (Expr.ite (.lt (.num 1) (.num 2)) (.num 10) (.num 20)).eval

example : (Expr.ite (.lt (.num 1) (.num 2)) (.num 10) (.num 20)).eval = 10 := by
  rfl

example : 3 ≠ 5 := by decide
example : 5 + 1 = 1 + 5 := by decide

end Lecture07

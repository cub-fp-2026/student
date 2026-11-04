/-
# Lecture 10 — State
-/
import Mathlib

namespace Lecture10

-- ## Threading state by hand

inductive Tree (α : Type) where
  | empty
  | node (left : Tree α) (value : α) (right : Tree α)
  deriving Repr, DecidableEq, Functor

def Tree.size : Tree α → Nat
  | .empty => 0
  | .node l _ r => l.size + 1 + r.size

def sampleTree : Tree String :=
  .node (.node .empty "a" .empty) "b" (.node .empty "c" .empty)

-- Label the nodes in order: left subtree, node, right subtree.
def labelTree : Tree α → Tree (Nat × α) := by
  sorry

-- ## A hand-rolled state monad

def MyState (σ α : Type) : Type := by
  sorry

namespace MyState

def get : MyState σ σ := by
  sorry

def set (s : σ) : MyState σ Unit := by
  sorry

def run (x : MyState σ α) (s : σ) : α × σ := by
  sorry

instance : Monad (MyState σ) := by
  sorry

end MyState

def labelTree' : Tree α → Tree (Nat × α) := by
  sorry

example (t : Tree α) : labelTree' t = labelTree t := by
  sorry

-- ## Lean's StateM

-- Use Lean's StateM from here on.
#print StateM
#check (get : StateM Nat Nat)
#check (modify : (Nat → Nat) → StateM Nat Unit)

def freshM : StateM Nat Nat := do
  sorry

def labelTree'' : Tree α → Tree (Nat × α) := by
  sorry

def dedup : List Nat → StateM (List Nat) (List Nat) := by
  sorry

example : (dedup [3, 1, 3, 2, 1]).run [] = ([3, 1, 2], [2, 1, 3]) := by
  sorry

-- ## State and failure together

abbrev StackM := StateT (List Nat) (Except String)

def pop : StackM Nat := do
  sorry

def push (x : Nat) : StackM Unit := do
  sorry

def addTop : StackM Unit := do
  sorry

example : addTop.run [2, 3, 7] = .ok ((), [5, 7]) := by
  sorry
example : addTop.run [2] = .error "empty stack" := by
  sorry

-- ## Two orders of State and Except

#print StateT
#print ExceptT

def pushThenFail : StackM Unit := do
  sorry

example : pushThenFail.run [7] = .error "empty stack" := by
  sorry

def pushThenFail' : ExceptT String (StateM (List Nat)) Unit := do
  sorry

example : pushThenFail'.run.run [7] = (.error "empty stack", [99, 7]) := by
  sorry

-- ## Loops and list combinators

#check @List.mapM
#check @List.filterM
#check @List.forM

def labelList (xs : List α) : StateM Nat (List (Nat × α)) := by
  sorry

def dedup' (xs : List Nat) : StateM (List Nat) (List Nat) := do
  sorry

def pushAll (xs : List Nat) : StackM Unit := do
  sorry

example : (pushAll [1, 2, 3]).run [] = .ok ((), [3, 2, 1]) := by
  sorry

end Lecture10

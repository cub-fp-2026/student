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

def labelTreeImpl : Tree α → Nat → Tree (Nat × α) × Nat
  | .empty, k => (.empty, k)
  | .node l x r, k =>
      let (ll, kl) := labelTreeImpl l k
      let kx := kl
      let (lr, kr) := labelTreeImpl r (kx + 1)
      (.node ll (kx, x) lr, kr)

-- Label the nodes in order: left subtree, node, right subtree.
def labelTree : Tree α → Tree (Nat × α) := fun t => (labelTreeImpl t 0).1

#eval labelTree sampleTree

-- ## A hand-rolled state monad

def MyState (σ α : Type) : Type := σ → α × σ

namespace MyState

def get : MyState σ σ := fun s => (s, s)

def set (s : σ) : MyState σ Unit := fun _ => ((), s)

def run (x : MyState σ α) (s : σ) : α × σ := x s

instance : Monad (MyState σ) where
  pure a := fun s => (a, s)
  bind x f := fun s =>
      let (a, s') := x s
      f a s'

end MyState

def fresh : MyState Nat Nat := do
  let k <- MyState.get
  MyState.set (k + 1)
  pure k

def labelTreeImpl' : Tree α → MyState Nat (Tree (Nat × α))
  | .empty => pure .empty
  | .node l x r => do
      let ll <- labelTreeImpl' l
      let kx <- fresh
      let lr <- labelTreeImpl' r
      pure (.node ll (kx, x) lr)

def labelTree' : Tree α → Tree (Nat × α) := fun t => ((labelTreeImpl' t).run 0).1

example (t : Tree α) : labelTree' t = labelTree t := by
  rw [labelTree', labelTree]
  suffices ((labelTreeImpl' t).run 0) = (labelTreeImpl t 0) by rw [this]
  generalize 0 = s
  rw [MyState.run]
  induction t generalizing s
  case empty => rfl
  case node l x r ihl ihr =>
    simp [labelTreeImpl', labelTreeImpl, Bind.bind, fresh, Pure.pure, MyState.get, MyState.set, ihl, ihr]

-- ## Lean's StateM

-- Use Lean's StateM from here on.
#print StateM
#print StateT
#check (get : StateM Nat Nat)
#check (modify : (Nat → Nat) → StateM Nat Unit)

def freshM : StateM Nat Nat := do
  let k ← get
  modify (· + 1)
  pure k

def labelTreeImpl'' : Tree α → StateM Nat (Tree (Nat × α))
  | .empty => pure .empty
  | .node l x r => do
      let ll <- labelTreeImpl' l
      let kx <- freshM
      let lr <- labelTreeImpl' r
      pure (.node ll (kx, x) lr)

def labelTree'' : Tree α → Tree (Nat × α) := fun t => (labelTreeImpl'' t).eval 0

def dedup : List Nat → StateM (List Nat) (List Nat)
  | [] => pure []
  | x :: xs => do
    if x ∈ (← get)
    then dedup xs
    else
      modify (x :: ·)
      (x :: ·) <$> dedup xs

example : (dedup [3, 1, 3, 2, 1]).run [] = ([3, 1, 2], [2, 1, 3]) := by rfl

-- ## State and failure together

abbrev StackM := StateT (List Nat) (Except String)
#print StateT
example : StackM α = (List Nat → Except String (α × List Nat)) := by rfl

def pop : StackM Nat := do
  match (← get) with
    | [] => throw "empty stack"
    | x :: xs =>
        set xs
        pure x

def push (x : Nat) : StackM Unit := modify (x :: ·)

def addTop : StackM Unit := do
  let x ← pop
  let y ← pop
  push (x + y)

example : addTop.run [2, 3, 7] = .ok ((), [5, 7]) := by rfl
example : addTop.run [2] = .error "empty stack" := by rfl

-- ## Two orders of State and Except

#print StateT
#print ExceptT

def pushThenFail : StackM Unit := do
  push 99
  throw "empty stack"

example : pushThenFail.run [7] = .error "empty stack" := by rfl

example : ExceptT String (StateM (List Nat)) α =
              (List Nat → Except String α × List Nat) := by rfl
def pushThenFail' : ExceptT String (StateM (List Nat)) Unit := do
  modify (99 :: ·)
  throw "empty stack"

example : pushThenFail'.run.run [7] = (.error "empty stack", [99, 7]) := by rfl


-- ## Loops and list combinators

#check @List.mapM
#check @List.filterM
#check @List.forM

def labelList (xs : List α) : StateM Nat (List (Nat × α)) :=
  xs.mapM fun x => (·, x) <$> freshM

def dedup' (xs : List Nat) : StateM (List Nat) (List Nat) :=
  xs.filterM fun x => do
    if x ∈ (← get)
    then pure false
    else
      modify (x :: ·)
      pure true

def pushAll (xs : List Nat) : StackM Unit := do
  for x in xs do
    push x
  -- xs.forM push


example : (pushAll [1, 2, 3]).run [] = .ok ((), [3, 2, 1]) := by rfl

-- # Expr language

inductive Expr : Type where
  | num (n : Nat)
  | add (lhs rhs : Expr)

def toStackMachine : Expr → StackM Unit
  | .num n => push n
  | .add lhs rhs => do
      toStackMachine lhs
      toStackMachine rhs
      addTop

def exExpr : Expr := .add (.num 5) (.num 7)

#eval (toStackMachine exExpr).run []

end Lecture10

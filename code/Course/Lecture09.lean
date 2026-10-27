/-
# Lecture 9 — Foldable, Functor, Monad
-/
import Mathlib

namespace Lecture09

-- ## The same fold, three containers

class MyMonoid (α : Type) where
  unit : α
  op : α → α → α

infixl:65 " ⋄ " => MyMonoid.op

instance : MyMonoid Nat := ⟨0, (· + ·)⟩
instance : MyMonoid (List α) := ⟨[], (· ++ ·)⟩

inductive Tree (α : Type) where
  | empty
  | node (left : Tree α) (value : α) (right : Tree α)
  deriving Repr, DecidableEq

def sampleTree : Tree Nat :=
  .node (.node .empty 1 .empty) 2 (.node .empty 3 .empty)

def Tree.sum : Tree Nat → Nat
  | .empty => 0
  | .node l x r => l.sum + x + r.sum

-- Left subtree, node, right subtree.
def Tree.toList : Tree α → List α
  | .empty => []
  | .node l x r => l.toList ++ [x] ++ r.toList

def Tree.foldMap [MyMonoid μ] (f : α → μ) : Tree α → μ := by
  sorry

example : sampleTree.foldMap id = 6 := by
  sorry
example : sampleTree.foldMap (fun x => [x]) = [1, 2, 3] := by
  sorry

class MyFoldable (F : Type → Type) where
  foldMap [MyMonoid μ] : (α → μ) → F α → μ

instance : MyFoldable Tree := by
  sorry

instance : MyFoldable List := by
  sorry

instance : MyFoldable Option := by
  sorry

def size [MyFoldable F] (xs : F α) : Nat := by
  sorry

def elements [MyFoldable F] (xs : F α) : List α := by
  sorry

example : size sampleTree = 3 := by
  sorry
example : size ["a", "b"] = 2 := by
  sorry
example : size (none : Option Nat) = 0 := by
  sorry
example : elements sampleTree = [1, 2, 3] := by
  sorry

-- ## The same map, three containers

def Tree.map (f : α → β) : Tree α → Tree β := by
  sorry

example : sampleTree.map (· * 10) =
    .node (.node .empty 10 .empty) 20 (.node .empty 30 .empty) := by
  sorry

#print Functor

instance : Functor Tree := by
  sorry

example : (· * 10) <$> [1, 2, 3] = [10, 20, 30] := by
  sorry
example : (· * 10) <$> some 2 = some 20 := by
  sorry
example : (· * 10) <$> (none : Option Nat) = none := by
  sorry
example : String.length <$> ["one", "three"] = [3, 5] := by
  sorry

-- ## Functor laws

theorem Tree.map_id (t : Tree α) : id <$> t = t := by
  sorry

theorem Tree.map_comp (f : α → β) (g : β → γ) (t : Tree α) :
    (g ∘ f) <$> t = g <$> (f <$> t) := by
  sorry

#print LawfulFunctor

-- ## Lookups that may fail

def managers : List (String × String) :=
  [("Ada", "Grace"), ("Alan", "Grace"), ("Grace", "Frances"), ("Edsger", "Frances")]

def desks : List (String × Nat) :=
  [("Grace", 12), ("Frances", 3)]

def manager? (name : String) : Option String := managers.lookup name
def desk? (name : String) : Option Nat := desks.lookup name

-- The desk of the manager's manager.
def skipLevelDesk? (name : String) : Option Nat :=
  match manager? name with
  | none => none
  | some m =>
    match manager? m with
    | none => none
    | some mm => desk? mm

example : skipLevelDesk? "Ada" = some 3 := by
  sorry
example : skipLevelDesk? "Grace" = none := by
  sorry

example : (manager? "Ada").map manager? = some (some "Frances") := by
  sorry

-- ## Extracting bind

def bindOption (x : Option α) (f : α → Option β) : Option β := by
  sorry

def skipLevelDesk?' (name : String) : Option Nat := by
  sorry

example (name : String) : skipLevelDesk? name = skipLevelDesk?' name := by
  sorry

#print Monad

example (x : Option α) (f : α → Option β) : x >>= f = bindOption x f := by
  sorry

def skipLevelDeskDo (name : String) : Option Nat := by
  sorry

example : skipLevelDeskDo "Ada" = some 3 := by
  sorry

-- ## Monad laws

example (a : α) (f : α → Option β) : (pure a >>= f) = f a := by
  sorry
example (x : Option α) : (x >>= pure) = x := by
  sorry
example (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x >>= f >>= g) = (x >>= fun a => f a >>= g) := by
  sorry

#print LawfulMonad

-- ## The same code, three monads

def twice [Monad m] (step : String → m String) (name : String) : m String := by
  sorry

example : twice manager? "Ada" = some "Frances" := by
  sorry

def managerE (name : String) : Except String String :=
  match managers.lookup name with
  | none => .error s!"{name} has no manager"
  | some m => .ok m

example : twice managerE "Grace" = .error "Frances has no manager" := by
  sorry

-- Everyone whose manager is `name`, in list order.
def reports (name : String) : List String :=
  (managers.filter (·.2 == name)).map (·.1)

example : reports "Frances" = ["Grace", "Edsger"] := by
  sorry
example : twice reports "Frances" = ["Ada", "Alan"] := by
  sorry

end Lecture09

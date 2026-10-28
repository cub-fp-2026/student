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

def Tree.fold (lf : ρ) (comb : ρ → α → ρ → ρ) : Tree α → ρ
  | .empty => lf
  | .node l x r => comb (l.fold lf comb) x (r.fold lf comb)

def Tree.sum' : Tree Nat → Nat := Tree.fold 0 (fun l x r => l + x + r)
def Tree.toList' : Tree α → List α :=
  Tree.fold [] (fun l x r => l ++ [x] ++ r)

def Tree.foldMap [MyMonoid μ] (f : α → μ) : Tree α → μ
  | .empty => MyMonoid.unit
  | .node l x r => l.foldMap f ⋄ f x ⋄ r.foldMap f

def Tree.foldMap' [MyMonoid μ] (f : α → μ) : Tree α → μ :=
  Tree.fold MyMonoid.unit (fun l x r => l ⋄ f x ⋄ r)

example (t : Tree Nat) : t.sum = t.foldMap id := by
  induction t <;> simp [Tree.sum, Tree.foldMap, MyMonoid.unit, MyMonoid.op, *]

example : sampleTree.foldMap id = 6 := by rfl
example : sampleTree.foldMap (fun x => [x]) = [1, 2, 3] := by rfl

class MyFoldable (F : Type → Type) where
  foldMap [MyMonoid μ] : (α → μ) → F α → μ

instance : MyFoldable Tree where
  foldMap := Tree.foldMap

instance : MyFoldable List where
  foldMap f := List.foldr (fun x r => f x ⋄ r) MyMonoid.unit

#print Option

instance : MyFoldable Option where
  foldMap
  | _, .none => MyMonoid.unit
  | f, .some x => f x

def size [MyFoldable F] (xs : F α) : Nat :=
  MyFoldable.foldMap (fun _ => 1) xs

def elements [MyFoldable F] (xs : F α) : List α :=
  MyFoldable.foldMap (fun x => [x]) xs

example : size sampleTree = 3 := by rfl
example : size ["a", "b"] = 2 := by rfl
example : size (none : Option Nat) = 0 := by rfl
example : elements sampleTree = [1, 2, 3] := by rfl
example : elements (some 5) = [5] := by rfl

-- ## The same map, three containers

def Tree.map (f : α → β) : Tree α → Tree β
  | .empty => .empty
  | .node l x r => .node (l.map f) (f x) (r.map f)

example : sampleTree.map (· * 10) =
    .node (.node .empty 10 .empty) 20 (.node .empty 30 .empty) := by
  rfl

#print Functor

instance : Functor Tree where
  map := Tree.map

example : (· * 10) <$> [1, 2, 3] = [10, 20, 30] := by rfl
example : (· * 10) <$> some 2 = some 20 := by rfl
example : (· * 10) <$> (none : Option Nat) = none := by rfl
example : String.length <$> ["one", "three"] = [3, 5] := by rfl

inductive Pair (α : Type) where
  | mk : α → α → Pair α
  deriving Functor

#eval (· + 1) <$> Pair.mk 5 7

inductive Pred (α : Type) where
  | mk : (α → Bool) → Pred α

def Pred.map (f : α → β) : Pred α → Pred β
  | .mk p => .mk (fun b => sorry) -- impossible

-- cofunctor F: (f : α → β) : F β → F α

-- ## Functor laws

theorem Tree.map_id (t : Tree α) : id <$> t = t := by
  induction t <;> simp [Functor.map, map, *] at *; tauto

-- tauto can prove goals like: A ∧ B → B ∧ A

theorem Tree.map_comp (f : α → β) (g : β → γ) (t : Tree α) :
    (g ∘ f) <$> t = g <$> (f <$> t) := by
  induction t <;> simp [Functor.map, map, *] at *; tauto

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

example : skipLevelDesk? "Ada" = some 3 := by rfl
example : skipLevelDesk? "Grace" = none := by rfl

example : manager? <$> (manager? "Ada") = some (some "Frances") := by rfl

-- ## Extracting bind

def bindOption (x : Option α) (f : α → Option β) : Option β :=
  match x with
  | .none => .none
  | .some v => f v

def skipLevelDesk?' (name : String) : Option Nat :=
  bindOption (manager? name) (fun m => bindOption (manager? m) desk?)

example (name : String) : skipLevelDesk? name = skipLevelDesk?' name := by
  unfold skipLevelDesk?
  unfold skipLevelDesk?'
  split
  · rename_i m hm
    rw [hm]
    rfl
  · rename_i m' m hm
    rw [hm]
    simp [bindOption]
    split
    · rename_i mm hmm
      rw [hmm]
    · rename_i mm' mm hmm
      rw [hmm]

#print Monad

-- we can't do: desk? (manager? (manager? name))
def skipLevelDesk?'' (name : String) : Option Nat :=
  (manager? name >>= fun m => manager? m) >>= desk?

example (x : Option α) (f : α → Option β) : x >>= f = bindOption x f := by
  sorry

def skipLevelDeskDo (name : String) : Option Nat := do
  let m <- manager? name
  let mm <- manager? m
  desk? mm

example : skipLevelDeskDo "Ada" = some 3 := by rfl

-- ## Monad laws

example (a : α) (f : α → Option β) : (pure a >>= f) = f a := by rfl
example (x : Option α) : (x >>= pure) = x := by
  cases x <;> rfl
example (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x >>= f >>= g) = (x >>= fun a => f a >>= g) := by
  cases x <;> rfl

#print LawfulMonad

-- ## The same code, three monads

def twice [Monad m] (step : String → m String) (name : String) : m String := do
  let name' <- step name
  let name'' <- step name'
  return name''

example : twice manager? "Ada" = some "Frances" := by rfl
example : twice manager? "Grace" = none := by rfl

#print Except

def managerE (name : String) : Except String String :=
  match managers.lookup name with
  | none => .error s!"{name} has no manager"
  | some m => .ok m

example : twice managerE "Grace" = .error "Frances has no manager" := by rfl

partial def numbersFromUpTo (i j : Nat) : List Nat :=
  if i <= j
  then i :: numbersFromUpTo (i+1) j
  else []

#eval numbersFromUpTo 1 5

def pythogoreanTriples (n : Nat) : List (Nat × Nat × Nat) := do
  let a <- numbersFromUpTo 1 n
  let b <- numbersFromUpTo a n
  let c <- numbersFromUpTo b n
  if a * a + b * b = c * c
  then [(a, b, c)]
  else []

#eval pythogoreanTriples 10

-- Everyone whose manager is `name`, in list order.
def reports (name : String) : List String :=
  (managers.filter (·.2 == name)).map (·.1)

example : reports "Frances" = ["Grace", "Edsger"] := by rfl
example : twice reports "Frances" = ["Ada", "Alan"] := by rfl

end Lecture09

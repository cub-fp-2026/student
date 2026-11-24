/-
# Lecture 13 — Semantics as specification
-/
import Mathlib

namespace Lecture13

/-
Lecture 12 gave the language an interpreter: a function that runs a program.
This lecture gives it a semantics: a relation that says what running a program
means, without saying how to compute it. The semantics is a specification.
We use it twice: to check the interpreter, and to state properties of programs.
-/

-- ## The language from Lecture 12

inductive Expr where
  | int (value : Nat)
  | bool (value : Bool)
  | name (value : String)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | lt (left right : Expr)
  | eq (left right : Expr)
  | not (arg : Expr)
  | and (left right : Expr)
  | or (left right : Expr)
  deriving Repr, DecidableEq

inductive Stmt where
  | skip
  | assign (target : String) (value : Expr)
  | seq (first second : Stmt)
  | ifThenElse (condition : Expr) (yes no : Stmt)
  | whileDo (condition : Expr) (body : Stmt)
  deriving Repr, DecidableEq

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  deriving Repr, DecidableEq

inductive EvalError where
  | unboundVar (name : String)
  | typeError
  | outOfFuel
  deriving Repr, DecidableEq

abbrev Env := List (String × Val)

def Env.get (env : Env) (name : String) : Except EvalError Val :=
  match env.lookup name with
  | some v => .ok v
  | none => .error (.unboundVar name)

def Env.set (env : Env) (name : String) (val : Val) : Env :=
  (name, val) :: env

def intOp (f : Int → Int → Val) : Val → Val → Except EvalError Val
  | .int a, .int b => .ok (f a b)
  | _, _ => .error .typeError

def boolOp (f : Bool → Val) : Val → Except EvalError Val
  | .bool b => .ok (f b)
  | .int _ => .error .typeError

def eqOp : Val → Val → Except EvalError Val
  | .int a, .int b => .ok (.bool (a == b))
  | .bool a, .bool b => .ok (.bool (a == b))
  | _, _ => .error .typeError

def Expr.eval (env : Env) : Expr → Except EvalError Val
  | .int n => .ok (.int n)
  | .bool b => .ok (.bool b)
  | .name x => env.get x
  | .add l r => do intOp (fun a b => .int (a + b)) (← l.eval env) (← r.eval env)
  | .sub l r => do intOp (fun a b => .int (a - b)) (← l.eval env) (← r.eval env)
  | .mul l r => do intOp (fun a b => .int (a * b)) (← l.eval env) (← r.eval env)
  | .lt l r => do intOp (fun a b => .bool (decide (a < b))) (← l.eval env) (← r.eval env)
  | .eq l r => do eqOp (← l.eval env) (← r.eval env)
  | .not e => do boolOp (fun b => .bool !b) (← e.eval env)
  | .and l r => do
    match ← l.eval env with
    | .bool true => boolOp .bool (← r.eval env)
    | .bool false => pure (.bool false)
    | .int _ => throw .typeError
  | .or l r => do
    match ← l.eval env with
    | .bool true => pure (.bool true)
    | .bool false => boolOp .bool (← r.eval env)
    | .int _ => throw .typeError

def Expr.test (c : Expr) (env : Env) : Except EvalError Bool := do
  match ← c.eval env with
  | .bool b => pure b
  | .int _ => throw .typeError

def Stmt.execFuel : Nat → Stmt → Env → Except EvalError Env
  | 0, _, _ => .error .outOfFuel
  | _ + 1, .skip, env => .ok env
  | _ + 1, .assign x e, env => do
    let v ← e.eval env
    pure (env.set x v)
  | fuel + 1, .seq s t, env => do
    let env' ← s.execFuel fuel env
    t.execFuel fuel env'
  | fuel + 1, .ifThenElse c yes no, env => do
    if ← c.test env then
      yes.execFuel fuel env
    else
      no.execFuel fuel env
  | fuel + 1, .whileDo c body, env => do
    if ← c.test env then
      let env' ← body.execFuel fuel env
      (Stmt.whileDo c body).execFuel fuel env'
    else
      pure env

-- ## Semantics of expressions

-- `Eval env e v`: in `env`, the expression `e` evaluates to `v`.
-- There are no rules for errors: an expression that fails has no derivation.
inductive Eval (env : Env) : Expr → Val → Prop where
  | int (n : Nat) : Eval env (.int n) (.int n)
  | bool (b : Bool) : Eval env (.bool b) (.bool b)
  | name {x : String} {v : Val} : env.lookup x = some v → Eval env (.name x) v
  | add {l r : Expr} {a b : Int} :
    Eval env l (.int a) → Eval env r (.int b) → Eval env (.add l r) (.int (a + b))
  | sub {l r : Expr} {a b : Int} :
    Eval env l (.int a) → Eval env r (.int b) → Eval env (.sub l r) (.int (a - b))
  | mul {l r : Expr} {a b : Int} :
    Eval env l (.int a) → Eval env r (.int b) → Eval env (.mul l r) (.int (a * b))
  | lt {l r : Expr} {a b : Int} :
    Eval env l (.int a) → Eval env r (.int b) → Eval env (.lt l r) (.bool (decide (a < b)))
  | eqInt {l r : Expr} {a b : Int} :
    Eval env l (.int a) → Eval env r (.int b) → Eval env (.eq l r) (.bool (a == b))
  | eqBool {l r : Expr} {a b : Bool} :
    Eval env l (.bool a) → Eval env r (.bool b) → Eval env (.eq l r) (.bool (a == b))
  | not {e : Expr} {b : Bool} : Eval env e (.bool b) → Eval env (.not e) (.bool !b)
  | andFalse {l r : Expr} : Eval env l (.bool false) → Eval env (.and l r) (.bool false)
  | andTrue {l r : Expr} {b : Bool} :
    Eval env l (.bool true) → Eval env r (.bool b) → Eval env (.and l r) (.bool b)
  | orTrue {l r : Expr} : Eval env l (.bool true) → Eval env (.or l r) (.bool true)
  | orFalse {l r : Expr} {b : Bool} :
    Eval env l (.bool false) → Eval env r (.bool b) → Eval env (.or l r) (.bool b)

-- x + 1 < 5, where x = 3
example : Eval [("x", .int 3)] (.lt (.add (.name "x") (.int 1)) (.int 5)) (.bool true) :=
  -- Lean cannot guess the value of `x` from `4`, so we name it.
  .lt (.add (.name (v := .int 3) rfl) (.int 1)) (.int 5)

-- `False and y` has a value although `y` is unbound.
example : Eval [] (.and (.bool false) (.name "y")) (.bool false) :=
  .andFalse (.bool false)

-- `y` is unbound, so `y + 1` has no value.
example (v : Val) : ¬ Eval [] (.add (.name "y") (.int 1)) v := by
  intro h
  cases h with
  | add hy _ => cases hy with
    | name h => cases h

-- ## The interpreter meets the specification

-- Every expression terminates, so a missing derivation can only mean an error.
-- That is why the relation and the interpreter agree exactly.
theorem Expr.eval_eq_ok_iff {env : Env} {e : Expr} {v : Val} :
    e.eval env = .ok v ↔ Eval env e v := by
  constructor
  · intro h
    induction e generalizing v with
    | int n => cases h; exact .int n
    | bool b => cases h; exact .bool b
    | name x =>
      simp only [Expr.eval, Env.get] at h
      split at h <;> cases h
      exact .name ‹_›
    | add l r ihl ihr =>
      cases hl : l.eval env with
      | error err => simp [Expr.eval, hl, bind, Except.bind] at h
      | ok a =>
        cases hr : r.eval env with
        | error => simp [Expr.eval, hl, hr, bind, Except.bind] at h
        | ok b =>
          -- If `a` or `b` is a boolean, `h` says a type error is `.ok v`.
          rcases a with a | _ <;> rcases b with b | _ <;>
            simp [Expr.eval, hl, hr, bind, Except.bind, intOp] at h
          subst h
          exact .add (ihl hl) (ihr hr)
    | sub l r ihl ihr | mul l r ihl ihr | lt l r ihl ihr | eq l r ihl ihr =>
      cases hl : l.eval env with
      | error => simp [Expr.eval, hl, bind, Except.bind] at h
      | ok a =>
        cases hr : r.eval env with
        | error => simp [Expr.eval, hl, hr, bind, Except.bind] at h
        | ok b =>
          cases a <;> cases b <;> simp [Expr.eval, hl, hr, bind, Except.bind, intOp, eqOp] at h <;>
            subst h <;> constructor <;> first | exact ihl hl | exact ihr hr
    | not e ih =>
      cases he : e.eval env with
      | error => simp [Expr.eval, he, bind, Except.bind] at h
      | ok a =>
        cases a <;> simp [Expr.eval, he, bind, Except.bind, boolOp] at h
        subst h
        exact .not (ih he)
    | and l r ihl ihr | or l r ihl ihr =>
      cases hl : l.eval env with
      | error => simp [Expr.eval, hl, bind, Except.bind] at h
      | ok a =>
        cases hr : r.eval env <;> rcases a with _ | _ | _ <;>
          (try rename_i c; try rcases c with _ | _) <;>
          simp [Expr.eval, hl, hr, bind, Except.bind, boolOp, pure, Except.pure, throw,
            throwThe, MonadExceptOf.throw] at h <;>
          subst h <;>
          first
            | exact .andFalse (ihl hl) | exact .andTrue (ihl hl) (ihr hr)
            | exact .orTrue (ihl hl) | exact .orFalse (ihl hl) (ihr hr)
  · intro h
    induction h
    -- Each rule is one line of `Expr.eval`, once the premises are rewritten.
    case add l r a b _ _ ihl ihr =>
      simp [Expr.eval, ihl, ihr, bind, Except.bind, intOp]
    case andFalse ihl =>
      simp [Expr.eval, ihl, bind, Except.bind, pure, Except.pure]
    all_goals simp_all [Expr.eval, Env.get, bind, Except.bind, intOp, eqOp, boolOp,
      pure, Except.pure]

-- An expression has at most one value.
theorem Eval.det {env : Env} {e : Expr} {v₁ v₂ : Val}
    (h₁ : Eval env e v₁) (h₂ : Eval env e v₂) : v₁ = v₂ := by
  rw [← Expr.eval_eq_ok_iff] at h₁ h₂
  rw [h₁] at h₂
  cases h₂
  rfl

-- ## Semantics of errors

-- The operands of `+`, `-`, `*` and `<`, which must both be integers.
def Expr.intOperands : Expr → Option (Expr × Expr)
  | .add l r | .sub l r | .mul l r | .lt l r => some (l, r)
  | _ => none

-- `Fails env e`: in `env`, evaluating `e` gives an error.
inductive Fails (env : Env) : Expr → Prop where
  | name {x : String} : env.lookup x = none → Fails env (.name x)
  | intOpLeft {e l r : Expr} : e.intOperands = some (l, r) → Fails env l → Fails env e
  | intOpRight {e l r : Expr} : e.intOperands = some (l, r) → Fails env r → Fails env e
  | intOpLeftBool {e l r : Expr} {b : Bool} :
    e.intOperands = some (l, r) → Eval env l (.bool b) → Fails env e
  | intOpRightBool {e l r : Expr} {b : Bool} :
    e.intOperands = some (l, r) → Eval env r (.bool b) → Fails env e
  | eqLeft {l r : Expr} : Fails env l → Fails env (.eq l r)
  | eqRight {l r : Expr} : Fails env r → Fails env (.eq l r)
  | eqIntBool {l r : Expr} {a : Int} {b : Bool} :
    Eval env l (.int a) → Eval env r (.bool b) → Fails env (.eq l r)
  | eqBoolInt {l r : Expr} {a : Bool} {b : Int} :
    Eval env l (.bool a) → Eval env r (.int b) → Fails env (.eq l r)
  | not {e : Expr} : Fails env e → Fails env (.not e)
  | notInt {e : Expr} {n : Int} : Eval env e (.int n) → Fails env (.not e)
  | andLeft {l r : Expr} : Fails env l → Fails env (.and l r)
  | andLeftInt {l r : Expr} {n : Int} : Eval env l (.int n) → Fails env (.and l r)
  | andRight {l r : Expr} : Eval env l (.bool true) → Fails env r → Fails env (.and l r)
  | andRightInt {l r : Expr} {n : Int} :
    Eval env l (.bool true) → Eval env r (.int n) → Fails env (.and l r)
  | orLeft {l r : Expr} : Fails env l → Fails env (.or l r)
  | orLeftInt {l r : Expr} {n : Int} : Eval env l (.int n) → Fails env (.or l r)
  | orRight {l r : Expr} : Eval env l (.bool false) → Fails env r → Fails env (.or l r)
  | orRightInt {l r : Expr} {n : Int} :
    Eval env l (.bool false) → Eval env r (.int n) → Fails env (.or l r)

-- `1 + True` fails: its right operand is a boolean.
example (env : Env) : Fails env (.add (.int 1) (.bool true)) :=
  .intOpRightBool rfl (.bool true)

-- An expression that fails has no value.
theorem Fails.not_eval {env : Env} {e : Expr} {v : Val} (hf : Fails env e) :
    ¬ Eval env e v := by
  intro he
  induction hf generalizing v with
  | name hx => cases he with | name hx' => rw [hx] at hx'; cases hx'
  | @intOpLeft e _ _ hop _ ih | @intOpRight e _ _ hop _ ih =>
    cases e <;> cases hop <;> cases he <;> exact ih ‹_›
  | @intOpLeftBool e _ _ _ hop hb | @intOpRightBool e _ _ _ hop hb =>
    cases e <;> cases hop <;> cases he <;> cases hb.det ‹_›
  | eqLeft _ ih | eqRight _ ih => cases he <;> exact ih ‹_›
  | eqIntBool hl hr =>
    cases he with
    | eqInt _ hr' => cases hr.det hr'
    | eqBool hl' _ => cases hl.det hl'
  | eqBoolInt hl hr =>
    cases he with
    | eqInt hl' _ => cases hl.det hl'
    | eqBool _ hr' => cases hr.det hr'
  | not _ ih | andLeft _ ih | orLeft _ ih =>
    cases he <;> exact ih ‹_›
  | notInt hn | andLeftInt hn | orLeftInt hn => cases he <;> cases hn.det ‹_›
  | andRight hl _ ih | orRight hl _ ih =>
    cases he
    · cases hl.det ‹_›
    · exact ih ‹_›
  | andRightInt hl hr | orRightInt hl hr =>
    cases he
    · cases hl.det ‹_›
    · cases hr.det ‹_›

-- The interpreter reports an error exactly when the expression fails.
theorem Expr.eval_eq_error_iff {env : Env} {e : Expr} :
    (∃ err, e.eval env = .error err) ↔ Fails env e := by
  constructor
  · rintro ⟨err, h⟩
    induction e generalizing err with
    | int n => cases h
    | bool b => cases h
    | name x =>
      simp only [Expr.eval, Env.get] at h
      split at h
      · cases h
      · exact .name ‹_›
    | add l r ihl ihr | sub l r ihl ihr | mul l r ihl ihr | lt l r ihl ihr | eq l r ihl ihr =>
      cases hl : l.eval env with
      | error => first | exact .intOpLeft rfl (ihl _ hl) | exact .eqLeft (ihl _ hl)
      | ok a =>
        cases hr : r.eval env with
        | error => first | exact .intOpRight rfl (ihr _ hr) | exact .eqRight (ihr _ hr)
        | ok b =>
          have hl' := Expr.eval_eq_ok_iff.1 hl
          have hr' := Expr.eval_eq_ok_iff.1 hr
          cases a <;> cases b <;> simp [Expr.eval, hl, hr, bind, Except.bind, intOp, eqOp] at h <;>
            first
              | exact .intOpLeftBool rfl hl' | exact .intOpRightBool rfl hr'
              | exact .eqIntBool hl' hr' | exact .eqBoolInt hl' hr'
    | not e ih =>
      cases he : e.eval env with
      | error => exact .not (ih _ he)
      | ok a =>
        cases a with
        | int => exact .notInt (Expr.eval_eq_ok_iff.1 he)
        | bool => simp [Expr.eval, he, bind, Except.bind, boolOp] at h
    | and l r ihl ihr | or l r ihl ihr =>
      cases hl : l.eval env with
      | error => first | exact .andLeft (ihl _ hl) | exact .orLeft (ihl _ hl)
      | ok a =>
        have hl' := Expr.eval_eq_ok_iff.1 hl
        cases hr : r.eval env with
        | error =>
          rcases a with _ | _ | _ <;>
            simp [Expr.eval, hl, hr, bind, Except.bind, pure, Except.pure] at h <;>
            first
              | exact .andLeftInt hl' | exact .orLeftInt hl'
              | exact .andRight hl' (ihr _ hr) | exact .orRight hl' (ihr _ hr)
        | ok b =>
          have hr' := Expr.eval_eq_ok_iff.1 hr
          rcases a with _ | _ | _ <;> rcases b with _ | _ <;>
            simp [Expr.eval, hl, hr, bind, Except.bind, boolOp, pure, Except.pure] at h <;>
            first
              | exact .andLeftInt hl' | exact .orLeftInt hl'
              | exact .andRightInt hl' hr' | exact .orRightInt hl' hr'
  · intro hf
    cases h : e.eval env with
    | error err => exact ⟨err, rfl⟩
    | ok v => exact absurd (Expr.eval_eq_ok_iff.1 h) hf.not_eval

-- The converse of `Fails.not_eval`: an expression without a value fails.
theorem Fails.of_not_eval {env : Env} {e : Expr} (h : ∀ v, ¬ Eval env e v) : Fails env e := by
  cases he : e.eval env with
  | ok v => exact absurd (Expr.eval_eq_ok_iff.1 he) (h v)
  | error err => exact Expr.eval_eq_error_iff.1 ⟨err, he⟩

-- ## Semantics of statements

/-
A statement can also loop forever. If statements failed by having no
derivation, "no derivation" would no longer tell us whether the program
crashed or looped. So a crash is an outcome of its own.
-/
inductive Outcome where
  | ok (env : Env)
  | crash
  deriving Repr, DecidableEq

-- `TestFails env c`: in `env`, the condition `c` does not give a boolean.
inductive TestFails (env : Env) (c : Expr) : Prop where
  | fails : Fails env c → TestFails env c
  | int {n : Int} : Eval env c (.int n) → TestFails env c

lemma TestFails.not_eval {env : Env} {c : Expr} {b : Bool} (h : TestFails env c) :
    ¬ Eval env c (.bool b) := by
  intro hb
  cases h with
  | fails hf => exact hf.not_eval hb
  | int hn => cases hn.det hb

-- `BigStep s env o`: running `s` from `env` finishes with outcome `o`.
-- A program that loops forever has no derivation.
inductive BigStep : Stmt → Env → Outcome → Prop where
  | skip {env : Env} :
    BigStep .skip env (.ok env)
  | assign {x : String} {e : Expr} {env : Env} {v : Val} :
    Eval env e v →
    BigStep (.assign x e) env (.ok (env.set x v))
  | assignCrash {x : String} {e : Expr} {env : Env} :
    Fails env e →
    BigStep (.assign x e) env .crash
  | seq {s t : Stmt} {env env' : Env} {o : Outcome} :
    BigStep s env (.ok env') →
    BigStep t env' o →
    BigStep (.seq s t) env o
  | seqCrash {s t : Stmt} {env : Env} :
    BigStep s env .crash →
    BigStep (.seq s t) env .crash
  | ifTrue {c : Expr} {yes no : Stmt} {env : Env} {o : Outcome} :
    Eval env c (.bool true) →
    BigStep yes env o →
    BigStep (.ifThenElse c yes no) env o
  | ifFalse {c : Expr} {yes no : Stmt} {env : Env} {o : Outcome} :
    Eval env c (.bool false) →
    BigStep no env o →
    BigStep (.ifThenElse c yes no) env o
  | ifCrash {c : Expr} {yes no : Stmt} {env : Env} :
    TestFails env c →
    BigStep (.ifThenElse c yes no) env .crash
  | whileFalse {c : Expr} {body : Stmt} {env : Env} :
    Eval env c (.bool false) →
    BigStep (.whileDo c body) env (.ok env)
  | whileTrue {c : Expr} {body : Stmt} {env env' : Env} {o : Outcome} :
    Eval env c (.bool true) →
    BigStep body env (.ok env') →
    BigStep (.whileDo c body) env' o →
    BigStep (.whileDo c body) env o
  | whileBodyCrash {c : Expr} {body : Stmt} {env : Env} :
    Eval env c (.bool true) →
    BigStep body env .crash →
    BigStep (.whileDo c body) env .crash
  | whileCrash {c : Expr} {body : Stmt} {env : Env} :
    TestFails env c →
    BigStep (.whileDo c body) env .crash

/-
n = 1
while 0 < n:
    n = n - 1
-/
example : BigStep
    (.seq (.assign "n" (.int 1))
      (.whileDo (.lt (.int 0) (.name "n")) (.assign "n" (.sub (.name "n") (.int 1)))))
    []
    (.ok [("n", .int 0), ("n", .int 1)]) :=
  .seq (.assign (.int 1))
    (.whileTrue (.lt (.int 0) (.name (v := .int 1) rfl)) (.assign (.sub (.name rfl) (.int 1)))
      (.whileFalse (.lt (.int 0) (.name (v := .int 0) rfl))))

-- `if 1: pass` crashes: the condition is not a boolean.
example (env : Env) : BigStep (.ifThenElse (.int 1) .skip .skip) env .crash :=
  .ifCrash (.int (.int 1))

-- `x = 1 + True` crashes: the right operand of `+` is a boolean.
example (env : Env) : BigStep (.assign "x" (.add (.int 1) (.bool true))) env .crash :=
  .assignCrash (.intOpRightBool rfl (.bool true))

-- ## The interpreter meets the specification, again

def Outcome.ofExcept : Except EvalError Env → Outcome
  | .ok env => .ok env
  | .error _ => .crash

lemma Expr.test_ok {c : Expr} {env : Env} {b : Bool} :
    c.test env = .ok b ↔ Eval env c (.bool b) := by
  rw [← Expr.eval_eq_ok_iff, Expr.test]
  cases c.eval env with
  | error => simp [bind, Except.bind]
  | ok v => cases v <;> simp [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]

lemma Expr.test_error {c : Expr} {env : Env} {err : EvalError}
    (h : c.test env = .error err) : TestFails env c := by
  rw [Expr.test] at h
  cases hc : c.eval env with
  | error err' => exact .fails (Expr.eval_eq_error_iff.1 ⟨err', hc⟩)
  | ok v =>
    cases v with
    | int => exact .int (Expr.eval_eq_ok_iff.1 hc)
    | bool => simp [hc, bind, Except.bind, pure, Except.pure] at h

-- Unless it runs out of fuel, the interpreter's answer is what the semantics says.
theorem Stmt.execFuel_sound {fuel : Nat} {s : Stmt} {env : Env}
    (h : s.execFuel fuel env ≠ .error .outOfFuel) :
    BigStep s env (.ofExcept (s.execFuel fuel env)) := by
  induction fuel generalizing s env with
  | zero => exact absurd rfl h
  | succ fuel ih =>
    cases s with
    | skip => exact .skip
    | assign x e =>
      cases he : e.eval env with
      | error =>
        simp only [Stmt.execFuel, he, bind, Except.bind, Outcome.ofExcept]
        exact .assignCrash (Expr.eval_eq_error_iff.1 ⟨_, he⟩)
      | ok v =>
        simp only [Stmt.execFuel, he, bind, Except.bind, pure, Except.pure, Outcome.ofExcept]
        exact .assign (Expr.eval_eq_ok_iff.1 he)
    | seq s t =>
      have ihs := @ih s env
      cases hs : s.execFuel fuel env with
      | error =>
        simp only [Stmt.execFuel, hs, bind, Except.bind] at h ⊢
        rw [hs] at ihs
        exact .seqCrash (ihs h)
      | ok env' =>
        simp only [Stmt.execFuel, hs, bind, Except.bind] at h ⊢
        rw [hs] at ihs
        exact .seq (ihs nofun) (ih h)
    | ifThenElse c yes no =>
      cases hc : c.test env with
      | error =>
        simp only [Stmt.execFuel, hc, bind, Except.bind, Outcome.ofExcept]
        exact .ifCrash (Expr.test_error hc)
      | ok b =>
        cases b <;> simp only [Stmt.execFuel, hc, bind, Except.bind, Bool.false_eq_true,
          ↓reduceIte] at h ⊢
        · exact .ifFalse (Expr.test_ok.1 hc) (ih h)
        · exact .ifTrue (Expr.test_ok.1 hc) (ih h)
    | whileDo c body =>
      cases hc : c.test env with
      | error =>
        simp only [Stmt.execFuel, hc, bind, Except.bind, Outcome.ofExcept]
        exact .whileCrash (Expr.test_error hc)
      | ok b =>
        cases b
        · simp only [Stmt.execFuel, hc, bind, Except.bind, Bool.false_eq_true, ↓reduceIte,
            pure, Except.pure, Outcome.ofExcept]
          exact .whileFalse (Expr.test_ok.1 hc)
        · have ihb := @ih body env
          cases hb : body.execFuel fuel env with
          | error =>
            simp only [Stmt.execFuel, hc, hb, bind, Except.bind, ↓reduceIte] at h ⊢
            rw [hb] at ihb
            exact .whileBodyCrash (Expr.test_ok.1 hc) (ihb h)
          | ok env' =>
            simp only [Stmt.execFuel, hc, hb, bind, Except.bind, ↓reduceIte] at h ⊢
            rw [hb] at ihb
            exact .whileTrue (Expr.test_ok.1 hc) (ihb nofun) (ih h)

-- ## Hoare triples

-- A postcondition holds of an outcome if the program finished and `Q` holds.
-- A crash satisfies no postcondition.
def Outcome.Holds (Q : Env → Prop) : Outcome → Prop
  | .ok env => Q env
  | .crash => False

-- `Triple P s Q`: started where `P` holds, `s` does not crash,
-- and if it finishes, `Q` holds.
def Triple (P : Env → Prop) (s : Stmt) (Q : Env → Prop) : Prop :=
  ∀ env o, P env → BigStep s env o → o.Holds Q

-- The precondition says: `e` has a value, and `Q` holds after storing it in `x`.
-- This is the semantic reading of the textbook rule {Q[x := e]} x := e {Q}.
theorem Triple.assign {Q : Env → Prop} {x : String} {e : Expr} :
    Triple (fun env => ∃ v, Eval env e v ∧ Q (env.set x v)) (.assign x e) Q := by
  rintro env o ⟨v, hv, hq⟩ h
  cases h with
  | assign hv' => rwa [hv'.det hv]
  | assignCrash hf => exact hf.not_eval hv

theorem Triple.seq {P R Q : Env → Prop} {s t : Stmt}
    (hs : Triple P s R) (ht : Triple R t Q) : Triple P (.seq s t) Q := by
  intro env o hp h
  cases h with
  | seq h₁ h₂ => exact ht _ _ (hs _ _ hp h₁) h₂
  | seqCrash h₁ => exact hs _ _ hp h₁

theorem Triple.ifThenElse {P Q : Env → Prop} {c : Expr} {yes no : Stmt}
    (hyes : Triple (fun env => P env ∧ Eval env c (.bool true)) yes Q)
    (hno : Triple (fun env => P env ∧ Eval env c (.bool false)) no Q) :
    Triple (fun env => P env ∧ ∃ b, Eval env c (.bool b)) (.ifThenElse c yes no) Q := by
  rintro env o ⟨hp, b, hb⟩ h
  cases h with
  | ifTrue hc h => exact hyes _ _ ⟨hp, hc⟩ h
  | ifFalse hc h => exact hno _ _ ⟨hp, hc⟩ h
  | ifCrash hf => exact hf.not_eval hb

-- A stronger precondition is always allowed.
theorem Triple.pre {P P' Q : Env → Prop} {s : Stmt}
    (h : Triple P' s Q) (hp : ∀ env, P env → P' env) : Triple P s Q :=
  fun env o hpe hs => h env o (hp env hpe) hs

-- ## Example: swap

/-
t = x
x = y
y = t
-/
def swap : Stmt :=
  .seq (.assign "t" (.name "x")) (.seq (.assign "x" (.name "y")) (.assign "y" (.name "t")))

-- `x ↦ v`: the variable `x` holds `v`.
def Holds (x : String) (v : Val) : Env → Prop := fun env => env.lookup x = some v
notation:50 x:51 " ↦ " v:51 => Holds x v

-- `P ⋀ Q`: both conditions hold.
def Both (P Q : Env → Prop) : Env → Prop := fun env => P env ∧ Q env
infixr:35 " ⋀ " => Both

theorem swap_correct (a b : Val) :
    Triple ("x" ↦ a ⋀ "y" ↦ b) swap ("x" ↦ b ⋀ "y" ↦ a) := by
  apply Triple.seq (R := "t" ↦ a ⋀ "y" ↦ b)
  · apply Triple.pre Triple.assign
    rintro env ⟨hx, hy⟩
    exact ⟨a, .name hx, by simp_all [Both, Holds, Env.set, List.lookup]⟩
  apply Triple.seq (R := "t" ↦ a ⋀ "x" ↦ b)
  · apply Triple.pre Triple.assign
    rintro env ⟨ht, hy⟩
    exact ⟨b, .name hy, by simp_all [Both, Holds, Env.set, List.lookup]⟩
  · apply Triple.pre Triple.assign
    rintro env ⟨ht, hx⟩
    exact ⟨a, .name ht, by simp_all [Both, Holds, Env.set, List.lookup]⟩

-- ## Termination

/-
while True:
    pass
-/
def forever : Stmt := .whileDo (.bool true) .skip

-- No derivation at all: neither a final environment nor a crash.
theorem not_bigStep_forever (env : Env) (o : Outcome) : ¬ BigStep forever env o := by
  intro h
  generalize hs : forever = s at h
  induction h <;> cases hs
  case whileFalse hc => cases hc
  case whileTrue ih => exact ih rfl
  case whileBodyCrash hbody _ => cases hbody
  case whileCrash hf => exact hf.not_eval (.bool true)

-- So `forever` satisfies every triple, even one with postcondition `False`.
-- A triple promises nothing about termination: it is *partial* correctness.
example : Triple (fun _ => True) forever (fun _ => False) :=
  fun env o _ h => absurd h (not_bigStep_forever env o)

-- The interpreter can only report that it gave up.
example (env : Env) (fuel : Nat) : forever.execFuel fuel env = .error .outOfFuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel => exact ih

end Lecture13

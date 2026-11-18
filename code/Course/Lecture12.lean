/-
# Lecture 12 — Interpretation
-/
import Mathlib

namespace Lecture12

-- ## Syntax

-- The expressions from the parser homework.
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

-- A Python block is a chain of `seq`, and `pass` is `skip`.
inductive Stmt where
  | skip
  | assign (target : String) (value : Expr)
  | seq (first second : Stmt)
  | ifThenElse (condition : Expr) (yes no : Stmt)
  | whileDo (condition : Expr) (body : Stmt)
  deriving Repr, DecidableEq

/-
n = 3
acc = 0
while 0 < n:
    acc = acc + n
    n = n - 1
-/
def triangle : Stmt :=
  .seq (.assign "n" (.int 3))
    (.seq (.assign "acc" (.int 0))
      (.whileDo (.lt (.int 0) (.name "n"))
        (.seq (.assign "acc" (.add (.name "acc") (.name "n")))
          (.assign "n" (.sub (.name "n") (.int 1))))))

-- ## Functions on syntax

def Expr.size : Expr → Nat
  | .int _ | .bool _ | .name _ => 1
  | .add l r | .sub l r | .mul l r | .lt l r | .eq l r
  | .and l r | .or l r => 1 + l.size + r.size
  | .not e => 1 + e.size

-- x + 1
def term : Expr := .add (.name "x") (.int 1)

example : term.size = 3 := rfl

-- ## Values, errors, and environments

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  deriving Repr, DecidableEq

inductive EvalError where
  | unboundVar (name : String)
  | typeError
  -- Only the total interpreter below runs out of fuel.
  | outOfFuel
  deriving Repr, DecidableEq

abbrev Env := List (String × Val)

def Env.get (env : Env) (name : String) : Except EvalError Val :=
  match env.lookup name with
  | some v => .ok v
  | none => .error (.unboundVar name)

-- The newest binding comes first, so it hides older ones.
def Env.set (env : Env) (name : String) (val : Val) : Env :=
  (name, val) :: env

example : Env.get [("x", .int 1), ("x", .int 2)] "x" = .ok (.int 1) := rfl
example : Env.get [] "x" = .error (.unboundVar "x") := rfl
example : (Env.set [("x", .int 2)] "x" (.int 1)).get "x" = .ok (.int 1) := rfl

-- ## Operators

-- An operator on two integers.
def intOp (f : Int → Int → Val) : Val → Val → Except EvalError Val
  | .int a, .int b => .ok (f a b)
  | _, _ => .error .typeError

-- An operator on one boolean.
def boolOp (f : Bool → Val) : Val → Except EvalError Val
  | .bool b => .ok (f b)
  | .int _ => .error .typeError

-- `==` compares two integers or two booleans.
def eqOp : Val → Val → Except EvalError Val
  | .int a, .int b => .ok (.bool (a == b))
  | .bool a, .bool b => .ok (.bool (a == b))
  | _, _ => .error .typeError

example : intOp (fun a b => .int (a - b)) (.int 1) (.int 3) = .ok (.int (-2)) := rfl
example : intOp (fun a b => .bool (decide (a < b))) (.int 1) (.int 3) = .ok (.bool true) := rfl
example : intOp (fun a b => .int (a + b)) (.int 1) (.bool true) = .error .typeError := rfl
example : boolOp (fun b => .bool !b) (.bool true) = .ok (.bool false) := rfl
example : boolOp (fun b => .bool !b) (.int 0) = .error .typeError := rfl
example : eqOp (.int 1) (.bool true) = .error .typeError := rfl

-- ## Interpreting expressions

-- Unlike Python, `True + 1` is a type error, and `and`/`or` only take booleans.
-- Like Python, `and` and `or` evaluate their right operand only when needed.
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

example : (Expr.sub (.int 10) (.mul (.int 2) (.name "x"))).eval [("x", .int 3)] =
    .ok (.int 4) := rfl
example : (Expr.sub (.int 1) (.int 3)).eval [] = .ok (.int (-2)) := rfl
example : (Expr.and (.lt (.name "x") (.int 5)) (.not (.name "done"))).eval
    [("x", .int 3), ("done", .bool false)] = .ok (.bool true) := rfl
example : (Expr.add (.int 3) (.bool true)).eval [] = .error .typeError := rfl
example : (Expr.name "y").eval [("x", .int 3)] = .error (.unboundVar "y") := rfl
-- The left operand fails first, so its error wins.
example : (Expr.add (.name "y") (.bool true)).eval [] = .error (.unboundVar "y") := rfl
-- `y` is never looked up.
example : (Expr.and (.bool false) (.name "y")).eval [] = .ok (.bool false) := rfl
example : (Expr.or (.bool false) (.name "y")).eval [] = .error (.unboundVar "y") := rfl
example : (Expr.or (.bool false) (.int 1)).eval [] = .error .typeError := rfl

-- ## Interpreting statements

-- The value of a condition.
def Expr.test (c : Expr) (env : Env) : Except EvalError Bool := do
  match ← c.eval env with
  | .bool b => pure b
  | .int _ => throw .typeError

-- A `while` loop need not terminate, so Lean cannot accept this definition
-- as a total function. `partial` lets us run it, but Lean knows nothing
-- about what it computes: we cannot prove anything about `exec`.
partial def Stmt.exec : Stmt → StateT Env (Except EvalError) Unit
  | .skip => pure ()
  | .assign x e => do
    let v ← e.eval (← get)
    modify (·.set x v)
  | .seq s t => do
    s.exec
    t.exec
  | .ifThenElse c yes no => do
    if ← c.test (← get) then
      yes.exec
    else
      no.exec
  | .whileDo c body => do
    if ← c.test (← get) then
      body.exec
      (Stmt.whileDo c body).exec

def Stmt.run (s : Stmt) (env : Env := []) : Except EvalError Env := do
  let ((), env') ← s.exec.run env
  pure env'

example : triangle.run.map (·.lookup "acc") = .ok (some (.int 6)) := by native_decide
example : Stmt.run (.assign "y" (.add (.name "x") (.int 1))) =
    .error (.unboundVar "x") := by native_decide
example : Stmt.run (.ifThenElse (.int 1) .skip .skip) = .error .typeError := by native_decide

-- ## A total interpreter

-- Every call uses one unit of fuel, so recursion on the fuel is structural.
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

example : (triangle.execFuel 20 []).map (·.lookup "acc") = .ok (some (.int 6)) := rfl
example : triangle.execFuel 5 [] = .error .outOfFuel := rfl
example : Stmt.execFuel 5 (.assign "y" (.add (.name "x") (.int 1))) [] =
    .error (.unboundVar "x") := rfl
example : Stmt.execFuel 5 (.ifThenElse (.int 1) .skip .skip) [] =
    .error .typeError := rfl

-- ## Procedures

-- The language with procedure calls. It reuses `Expr`, `Val`, `Env`, and
-- `Expr.eval`; only statements change.
namespace Procedures

-- `x = f(e₁, …, eₙ)` is a statement, not an expression, so evaluating an
-- expression still cannot run a procedure.
inductive Stmt where
  | skip
  | assign (target : String) (value : Expr)
  | seq (first second : Stmt)
  | ifThenElse (condition : Expr) (yes no : Stmt)
  | whileDo (condition : Expr) (body : Stmt)
  | call (target : String) (proc : String) (args : List Expr)
  deriving Repr, DecidableEq

-- The body returns its value by assigning `result`.
structure Proc where
  params : List String
  body : Stmt
  deriving Repr, DecidableEq

-- Procedures by name, like variables in an `Env`.
abbrev Procs := List (String × Proc)

-- Errors of the expression language, plus two that only calls can cause.
inductive ProcError where
  | eval (e : EvalError)
  | unknownProc (name : String)
  | arity (name : String) (expected given : Nat)
  deriving Repr, DecidableEq

def liftEval {α : Type} (r : Except EvalError α) : Except ProcError α :=
  r.mapError .eval

-- The environment a call starts in: each parameter bound to its argument.
def bindArgs (f : String) (params : List String) (vals : List Val) :
    Except ProcError Env :=
  if params.length = vals.length then
    .ok (params.zip vals)
  else
    .error (.arity f params.length vals.length)

example : bindArgs "double" ["n"] [.int 7] = .ok [("n", .int 7)] := rfl
example : bindArgs "double" ["n"] [] = .error (.arity "double" 1 0) := rfl

-- The procedure table never changes during a run, so it is read from a
-- `ReaderT` instead of being passed to every recursive call.
abbrev ExecM := ReaderT Procs (StateT Env (Except ProcError))

-- The arguments are evaluated in the caller's environment, the body runs in
-- an environment of only the parameters, and the caller gets `result`.
partial def Stmt.execReader : Stmt → ExecM Unit
  | .skip => pure ()
  | .assign x e => do
    let v ← liftEval (e.eval (← get))
    modify (·.set x v)
  | .seq s t => do
    s.execReader
    t.execReader
  | .ifThenElse c yes no => do
    if ← liftEval (c.test (← get)) then
      yes.execReader
    else
      no.execReader
  | .whileDo c body => do
    if ← liftEval (c.test (← get)) then
      body.execReader
      (Stmt.whileDo c body).execReader
  | .call x f args => do
    -- Resolve
    let procs ← read
    let some p := procs.lookup f | throw (.unknownProc f)
    -- Evaluate arguments in the caller
    let caller ← get
    let vals ← liftEval (args.mapM (·.eval caller))
    -- Enter a fresh frame
    let frame ← bindArgs f p.params vals
    let ((), out) ← (p.body.execReader.run procs).run frame
    -- Return to the caller
    let v ← liftEval (out.get "result")
    set (caller.set x v)

def Stmt.runReader (s : Stmt) (procs : Procs) (env : Env := []) :
    Except ProcError Env := do
  let ((), finalEnv) ← (s.execReader.run procs).run env
  pure finalEnv

/-
def double(n):
    result = n + n
-/
def doubleProc : Proc where
  params := ["n"]
  body := .assign "result" (.add (.name "n") (.name "n"))

/-
def peek():
    result = y

def forget(n):
    n = n + 1
-/
def basics : Procs :=
  [("double", doubleProc),
   ("peek", ⟨[], .assign "result" (.name "y")⟩),
   ("forget", ⟨["n"], .assign "n" (.add (.name "n") (.int 1))⟩)]

-- x = double(y), run from y = 7
#eval (Stmt.call "x" "double" [.name "y"]).runReader basics [("y", .int 7)]
-- `peek` cannot see the caller's `y`.
#eval (Stmt.call "x" "peek" []).runReader basics [("y", .int 7)]
-- `forget` never assigns `result`.
#eval (Stmt.call "x" "forget" [.int 1]).runReader basics
#eval (Stmt.call "x" "triple" [.int 1]).runReader basics
#eval (Stmt.call "x" "double" []).runReader basics

/-
def fact(n):
    if n < 2:
        result = 1
    else:
        m = fact(n - 1)
        result = n * m

def fib(n):
    if n < 2:
        result = n
    else:
        a = fib(n - 1)
        b = fib(n - 2)
        result = a + b
-/
def recursive : Procs :=
  [("fact", ⟨["n"],
      .ifThenElse (.lt (.name "n") (.int 2))
        (.assign "result" (.int 1))
        (.seq (.call "m" "fact" [.sub (.name "n") (.int 1)])
          (.assign "result" (.mul (.name "n") (.name "m"))))⟩),
   ("fib", ⟨["n"],
      .ifThenElse (.lt (.name "n") (.int 2))
        (.assign "result" (.name "n"))
        (.seq (.call "a" "fib" [.sub (.name "n") (.int 1)])
          (.seq (.call "b" "fib" [.sub (.name "n") (.int 2)])
            (.assign "result" (.add (.name "a") (.name "b")))))⟩)]

#eval ((Stmt.call "x" "fact" [.int 5]).runReader recursive).map (·.lookup "x")
#eval ((Stmt.call "x" "fib" [.int 10]).runReader recursive).map (·.lookup "x")

end Procedures

-- ## Output

-- The language with a `print` statement. It reuses `Expr`, `Val`, `Env`,
-- `Expr.eval`, and `Expr.test`; only statements change.
namespace WithOutput

inductive Stmt where
  | skip
  | assign (target : String) (value : Expr)
  | seq (first second : Stmt)
  | ifThenElse (condition : Expr) (yes no : Stmt)
  | whileDo (condition : Expr) (body : Stmt)
  | print (value : Expr)
  deriving Repr, DecidableEq

-- The printed lines are collected by a `WriterT`.
abbrev PrintM := StateT Env (WriterT (List String) (Except EvalError))

def renderVal : Val → String
  | .int n => toString n
  | .bool b => toString b

def printExpr (e : Expr) : PrintM Unit := do
  let v ← e.eval (← get)
  tell [renderVal v]
  pure ()

partial def Stmt.exec : Stmt → PrintM Unit
  | .skip => pure ()
  | .assign x e => do
    let v ← e.eval (← get)
    modify (·.set x v)
  | .seq s t => do
    s.exec
    t.exec
  | .ifThenElse c yes no => do
    if ← c.test (← get) then yes.exec else no.exec
  | .whileDo c body => do
    if ← c.test (← get) then
      body.exec
      (Stmt.whileDo c body).exec
  | .print e => printExpr e

/-
print(x)
x = x + 1
print(x)
-/
def report : Stmt :=
  .seq (.print (.name "x"))
    (.seq (.assign "x" (.add (.name "x") (.int 1)))
          (.print (.name "x")))

example : (report.exec.run [("x", .int 3)]).run =
    .ok (((), [("x", .int 4), ("x", .int 3)]), ["3", "4"]) := by native_decide

-- `WriterT` over `Except`: a failure discards what was printed before it.
example : ((Stmt.seq (.print (.int 1)) (.print (.name "missing"))).exec.run []).run =
    .error (.unboundVar "missing") := by native_decide

end WithOutput

-- ## Playground

/-
i = 0
s = 0
while i < 4:
    i = i + 1
    if i == 2:
        pass
    else:
        s = s + i
-/
def playground : Stmt :=
  .seq (.assign "i" (.int 0))
    (.seq (.assign "s" (.int 0))
      (.whileDo (.lt (.name "i") (.int 4))
        (.seq (.assign "i" (.add (.name "i") (.int 1)))
          (.ifThenElse (.eq (.name "i") (.int 2))
            .skip
            (.assign "s" (.add (.name "s") (.name "i")))))))

example : playground.run.map (·.lookup "s") = .ok (some (.int 8)) := by native_decide
example : (playground.execFuel 50 []).map (·.lookup "s") = .ok (some (.int 8)) := rfl

end Lecture12

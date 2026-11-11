/-
# Lecture 11 — Parser combinators
-/
import Mathlib

namespace Lecture11

-- ## The goal: a small imperative language

inductive Expr where
  | litNat (n : Nat)
  | litBool (b : Bool)
  | var (name : String)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | eq (left right : Expr)
  | lt (left right : Expr)
  | not (expr : Expr)
  | and (left right : Expr)
  deriving Repr, DecidableEq

inductive Stmt where
  | skip
  | assign (name : String) (expr : Expr)
  | seq (first second : Stmt)
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  | whileLoop (cond : Expr) (body : Stmt)
  deriving Repr, DecidableEq

-- "x := 2 + 3 * y; y := x - 1"
def sampleStmt : Stmt :=
  .seq
    (.assign "x" (.add (.litNat 2) (.mul (.litNat 3) (.var "y"))))
    (.assign "y" (.sub (.var "x") (.litNat 1)))

-- "if x < y { m := y } else { m := x }"
def sampleIf : Stmt :=
  .ifThenElse (.lt (.var "x") (.var "y"))
    (.assign "m" (.var "y"))
    (.assign "m" (.var "x"))

-- "while 0 < n { acc := acc + n; n := n - 1 }"
def sampleWhile : Stmt :=
  .whileLoop (.lt (.litNat 0) (.var "n"))
    (.seq
      (.assign "acc" (.add (.var "acc") (.var "n")))
      (.assign "n" (.sub (.var "n") (.litNat 1))))

-- ## A parser is a stateful, fallible computation

#print StateT
abbrev Parser := StateT (List Char) Option

example : Parser α = (List Char → Option (α × List Char)) := rfl

def anyChar : Parser Char := do
  match (← get) with
    | [] => throw ()
    | x :: xs => set xs; pure x

def satisfy (p : Char → Bool) : Parser Char := do
  let c ← anyChar
  if p c
  then pure c
  else throw ()

def char (c : Char) : Parser Char := satisfy (c = ·)

def eof : Parser Unit := do
  match (← get) with
    | [] => pure ()
    | _ => throw ()

#check StateT.eval
#check StateT.run
example [Monad m] : m α → m β → m α :=
  fun m1 m2 => m1 <* m2
def runParser (p : Parser α) (input : String) : Option α :=
  (p <* eof).eval input.toList

example : (char 'a').run ['a', 'b'] = some ('a', ['b']) := rfl
example : (char 'a').run ['b'] = none := rfl
example : runParser (char 'a') "a" = some 'a' := rfl
example : runParser (char 'a') "ab" = none := rfl

-- ## Sequencing and choice

#check @OrElse.orElse -- <|>
#check @SeqLeft.seqLeft  -- <*
#check @SeqRight.seqRight -- *>

def string (s : String) : Parser String := do
  s.toList.forM fun x => discard (char x)
  pure s

-- Because `Option` is on the outside of `StateT (List Char) Option`,
-- a failing branch discards its state changes and `<|>` backtracks.
example : runParser (string "ab" <|> string "ac") "ac" = some "ac" := rfl

lemma orElse_run (p q : Parser α) (cs : List Char) :
    (p <|> q).run cs = (p.run cs <|> q.run cs) := rfl

-- Runs `p` and returns `x` instead of its result.
def yields (p : Parser β) (x : α) : Parser α := do
  let _ ← p
  pure x

-- ## Repetition and tokens

partial def many (p : Parser α) : Parser (List α) := do
  ((· :: ·) <$> p <*> many p) <|> pure []
/-
  (do
    let x <- p
    let xs <- many p
    pure (x :: xs)
  ) <|> pure []
-/

def many1 (p : Parser α) : Parser (List α) :=
  (· :: ·) <$> p <*> many p

example (p : Parser α) : Parser (List α → List α) :=
  (· :: ·) <$> p

example (e : Parser (List α → List α)) (ps : Parser (List α)) :=
  e <*> ps

-- example: x + y + z (sepBy1 variable +)
def sepBy1 (p : Parser α) (sep : Parser β) : Parser (List α) := do
  -- (· :: ·) <$> p <*> many (sep *> p)
  let x ← p
  let xs ← many (sep *> p)
  pure (x :: xs)

-- As many characters satisfying `p` as possible.
def takeWhile (p : Char → Bool) : Parser String := do
  let cs ← many (satisfy p)
  pure (String.ofList cs)

-- Like `takeWhile`, but at least one character.
def takeWhile1 (p : Char → Bool) : Parser String := do
  let cs ← many1 (satisfy p)
  pure (String.ofList cs)

def ws : Parser Unit := discard (takeWhile Char.isWhitespace)

-- Runs `p`, then skips whitespace.
def token (p : Parser α) : Parser α := p <* ws

def symbol (s : String) : Parser String := token (string s)

def between (left right : String) (p : Parser α) : Parser α := do
  discard (symbol left)
  let x <- p
  discard (symbol right)
  pure x
  -- symbol left *> p <* symbol right

def nat' : Parser Nat := do
  let ds ← many1 (satisfy Char.isDigit)
  let ds' := ds.map (fun x => x.toNat - '0'.toNat)
  pure (ds'.foldl (fun acc x => 10*acc + x) 0)

def nat : Parser Nat := token nat'

def keywords : List String :=
  ["if", "else", "while", "skip", "true", "false"]

-- A letter followed by as many letters, and digits as possible.
def identLike : Parser String := do
  token (do
    let x <- satisfy Char.isAlpha
    let xs <- many (satisfy Char.isAlphanum)
    pure <| String.ofList <| x :: xs
  )

-- `iffy` is not `if`.
def keyword (kw : String) : Parser Unit := do
  let idt ← identLike
  guard (idt = kw)

-- Keywords are not identifiers.
def ident : Parser String := do
  let idt ← identLike
  guard (idt ∉ keywords)
  pure idt

def boolLit : Parser Bool :=
  yields (keyword "true") true <|> yields (keyword "false") false

example : runParser nat "42  " = some 42 := by native_decide
example : runParser (sepBy1 nat (symbol ",")) "1, 2, 3" = some [1, 2, 3] := by native_decide
example : runParser ident "while" = none := by native_decide
example : runParser ident "whilst" = some "whilst" := by native_decide
example : runParser ident "x1" = some "x1" := by native_decide
example : runParser ident "1x" = none := by native_decide
example : runParser (keyword "if") "iffy" = none := by native_decide

-- ## Parsing expressions

-- `p (op p)*`, combined from the left: `1 - 2 - 3` is `(1 - 2) - 3`.
partial def chainl1 (p : Parser α) (op : Parser (α → α → α)) : Parser α := do
  let x <- p
  let ops <- many (do
    let f <- op
    let y <- p
    pure (f · y)
  )
  pure (ops.foldl (fun acc f => f acc) x)

-- `p` or `p op p`, but not `p op p op p`.
def nonAssoc (p : Parser α) (op : Parser (α → α → α)) : Parser α := do
  (do
    let x ← p
    let f ← op
    let y ← p
    pure <| f x y
  ) <|> p

-- From loosest to tightest: `&&`, then `==` and `<` (not chained),
-- then `+` and `-`, then `*`, then `!` and atoms.
mutual

/-
  | litNat (n : Nat)
  | litBool (b : Bool)
  | var (name : String)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | eq (left right : Expr)
  | lt (left right : Expr)
  | not (expr : Expr)
  | and (left right : Expr)
-/

partial def parseAtom : Parser Expr :=
  (.litNat <$> nat)
  <|> (.litBool <$> boolLit)
  <|> between "(" ")" parseExpr
  <|> (.var <$> ident)
  <|> (symbol "!" *> (.not <$> parseAtom))

partial def parseTerm : Parser Expr :=
  chainl1 parseAtom (yields (symbol "*") .mul)

partial def parseSum : Parser Expr :=
  chainl1 parseTerm (
    (yields (symbol "+") .add)
    <|> (yields (symbol "-") .sub)
  )

partial def parseCmp : Parser Expr :=
  nonAssoc parseSum (yields (symbol "==") .eq <|> yields (symbol "<") .lt)

partial def parseExpr : Parser Expr :=
  chainl1 parseCmp (yields (symbol "&&") .and)

end

example : runParser parseExpr "2 + 3 * x" =
    some (.add (.litNat 2) (.mul (.litNat 3) (.var "x"))) := by native_decide
example : runParser parseExpr "(2 + 3) * x" =
    some (.mul (.add (.litNat 2) (.litNat 3)) (.var "x")) := by native_decide
example : runParser parseExpr "1 - 2 - 3" =
    some (.sub (.sub (.litNat 1) (.litNat 2)) (.litNat 3)) := by native_decide
example : runParser parseExpr "x < y + 1 && !(y == 0)" =
    some (.and (.lt (.var "x") (.add (.var "y") (.litNat 1)))
      (.not (.eq (.var "y") (.litNat 0)))) := by native_decide
example : runParser parseExpr "true && trueish == 1" =
    some (.and (.litBool true) (.eq (.var "trueish") (.litNat 1))) := by native_decide
example : runParser parseExpr "1 < 2 < 3" = none := by native_decide
-- The parser does not check types.
example : runParser parseExpr "1 + true" = some (.add (.litNat 1) (.litBool true)) := by native_decide

-- ## Parsing statements

-- Blocks are braced sequences: `if b { s } else { s }` and `while b { s }`.
mutual

/-
  | skip
  | assign (name : String) (expr : Expr)
  | seq (first second : Stmt)
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  | whileLoop (cond : Expr) (body : Stmt)
-/
partial def parseSimpleStmt : Parser Stmt :=
  yields (keyword "skip") .skip <|> (do
    let name ← ident
    discard (symbol ":=")
    let e ← parseExpr
    pure <| .assign name e
  )
  <|> (do
    keyword "if"
    let cond ← parseExpr
    let tb ← parseBlock
    keyword "else"
    let eb ← parseBlock
    pure <| .ifThenElse cond tb eb
  )
  <|> (do
    keyword "while"
    let cond ← parseExpr
    let body ← parseBlock
    pure <| .whileLoop cond body
  )

partial def parseBlock : Parser Stmt := between "{" "}" parseStmt

-- `s; t; u` is `(s; t); u`.
partial def parseStmt : Parser Stmt := do
  chainl1 parseSimpleStmt (yields (symbol ";") .seq)

end

def parseProgram (input : String) : Option Stmt :=
  runParser parseStmt input

example : parseProgram "x := 2 + 3 * y; y := x - 1" = some sampleStmt := by native_decide
example : parseProgram "if x < y { m := y } else { m := x }" = some sampleIf := by native_decide
example : parseProgram "while 0 < n { acc := acc + n; n := n - 1 }" =
    some sampleWhile := by native_decide
example : parseProgram "while 0 < n { n := n - 1 " = none := by native_decide
example : parseProgram "done := n < 1" =
    some (.assign "done" (.lt (.var "n") (.litNat 1))) := by native_decide

end Lecture11

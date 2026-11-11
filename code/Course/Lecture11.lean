/-
# Lecture 11 — Parser combinators
-/
import Mathlib

namespace Lecture11

-- ## The goal: a small imperative language

inductive Expr where
  | litInt (n : Int)
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
    (.assign "x" (.add (.litInt 2) (.mul (.litInt 3) (.var "y"))))
    (.assign "y" (.sub (.var "x") (.litInt 1)))

-- "if x < y { m := y } else { m := x }"
def sampleIf : Stmt :=
  .ifThenElse (.lt (.var "x") (.var "y"))
    (.assign "m" (.var "y"))
    (.assign "m" (.var "x"))

-- "while 0 < n { acc := acc + n; n := n - 1 }"
def sampleWhile : Stmt :=
  .whileLoop (.lt (.litInt 0) (.var "n"))
    (.seq
      (.assign "acc" (.add (.var "acc") (.var "n")))
      (.assign "n" (.sub (.var "n") (.litInt 1))))

-- ## A parser is a stateful, fallible computation

abbrev Parser := StateT (List Char) Option

example : Parser α = (List Char → Option (α × List Char)) := sorry

def anyChar : Parser Char := do
  sorry

def satisfy (p : Char → Bool) : Parser Char := do
  sorry

def char (c : Char) : Parser Char := sorry

def eof : Parser Unit := do
  sorry

def runParser (p : Parser α) (input : String) : Option α :=
  sorry

example : (char 'a').run ['a', 'b'] = some ('a', ['b']) := sorry
example : (char 'a').run ['b'] = none := sorry
example : runParser (char 'a') "a" = some 'a' := sorry
example : runParser (char 'a') "ab" = none := sorry

-- ## Sequencing and choice

#check @OrElse.orElse
#check @SeqLeft.seqLeft
#check @SeqRight.seqRight

def string (s : String) : Parser String := do
  sorry

-- Because `Option` is on the outside of `StateT (List Char) Option`,
-- a failing branch discards its state changes and `<|>` backtracks.
example : runParser (string "ab" <|> string "ac") "ac" = some "ac" := sorry

lemma orElse_run (p q : Parser α) (cs : List Char) :
    (p <|> q).run cs = (p.run cs <|> q.run cs) := sorry

-- Runs `p` and returns `x` instead of its result.
def yields (p : Parser β) (x : α) : Parser α := sorry

-- ## Repetition and tokens

partial def many (p : Parser α) : Parser (List α) :=
  sorry

def many1 (p : Parser α) : Parser (List α) := do
  sorry

def sepBy1 (p : Parser α) (sep : Parser β) : Parser (List α) := do
  sorry

-- As many characters satisfying `p` as possible.
def takeWhile (p : Char → Bool) : Parser String :=
  sorry

-- Like `takeWhile`, but at least one character.
def takeWhile1 (p : Char → Bool) : Parser String :=
  sorry

def ws : Parser Unit :=
  sorry

-- Runs `p`, then skips whitespace.
def token (p : Parser α) : Parser α := sorry

def symbol (s : String) : Parser String := sorry

def between (left right : String) (p : Parser α) : Parser α :=
  sorry

def nat : Parser Nat := do
  sorry

def keywords : List String :=
  ["if", "else", "while", "skip", "true", "false"]

-- A letter followed by as many letters, digits, and `_` as possible.
def identLike : Parser String := do
  sorry

-- `iffy` is not `if`.
def keyword (kw : String) : Parser Unit := do
  sorry

-- Keywords are not identifiers.
def ident : Parser String := do
  sorry

def boolLit : Parser Bool :=
  sorry

example : runParser nat "42  " = some 42 := sorry
example : runParser (sepBy1 nat (symbol ",")) "1, 2, 3" = some [1, 2, 3] := sorry
example : runParser ident "while" = none := sorry
example : runParser ident "whilst" = some "whilst" := sorry
example : runParser ident "x_1" = some "x_1" := sorry
example : runParser ident "1x" = none := sorry
example : runParser (keyword "if") "iffy" = none := sorry

-- ## Parsing expressions

-- `p (op p)*`, combined from the left: `1 - 2 - 3` is `(1 - 2) - 3`.
partial def chainl1 (p : Parser α) (op : Parser (α → α → α)) : Parser α := do
  sorry

-- `p` or `p op p`, but not `p op p op p`.
def nonAssoc (p : Parser α) (op : Parser (α → α → α)) : Parser α := do
  sorry

-- From loosest to tightest: `&&`, then `==` and `<` (not chained),
-- then `+` and `-`, then `*`, then `!` and atoms.
mutual

partial def parseAtom : Parser Expr :=
  sorry

partial def parseTerm : Parser Expr :=
  sorry

partial def parseSum : Parser Expr :=
  sorry

partial def parseCmp : Parser Expr :=
  sorry

partial def parseExpr : Parser Expr :=
  sorry

end

example : runParser parseExpr "2 + 3 * x" =
    some (.add (.litInt 2) (.mul (.litInt 3) (.var "x"))) := sorry
example : runParser parseExpr "(2 + 3) * x" =
    some (.mul (.add (.litInt 2) (.litInt 3)) (.var "x")) := sorry
example : runParser parseExpr "1 - 2 - 3" =
    some (.sub (.sub (.litInt 1) (.litInt 2)) (.litInt 3)) := sorry
example : runParser parseExpr "x < y + 1 && !(y == 0)" =
    some (.and (.lt (.var "x") (.add (.var "y") (.litInt 1)))
      (.not (.eq (.var "y") (.litInt 0)))) := sorry
example : runParser parseExpr "true && trueish == 1" =
    some (.and (.litBool true) (.eq (.var "trueish") (.litInt 1))) := sorry
example : runParser parseExpr "1 < 2 < 3" = none := sorry
-- The parser does not check types.
example : runParser parseExpr "1 + true" = some (.add (.litInt 1) (.litBool true)) := sorry

-- ## Parsing statements

-- Blocks are braced sequences: `if b { s } else { s }` and `while b { s }`.
mutual

partial def parseSimpleStmt : Parser Stmt :=
  sorry

partial def parseBlock : Parser Stmt := sorry

-- `s; t; u` is `s; (t; u)`.
partial def parseStmt : Parser Stmt := do
  sorry

end

def parseProgram (input : String) : Option Stmt :=
  sorry

example : parseProgram "x := 2 + 3 * y; y := x - 1" = some sampleStmt := sorry
example : parseProgram "if x < y { m := y } else { m := x }" = some sampleIf := sorry
example : parseProgram "while 0 < n { acc := acc + n; n := n - 1 }" =
    some sampleWhile := sorry
example : parseProgram "while 0 < n { n := n - 1 " = none := sorry
example : parseProgram "done := n < 1" =
    some (.assign "done" (.lt (.var "n") (.litInt 1))) := sorry

end Lecture11

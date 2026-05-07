module

public import PurescriptLanguageCstParser.Types
public import PurescriptLanguageCstParser.Errors
public import PurescriptLanguageCstParser.Layout
public import PurescriptLanguageCstParser.Range
import NonEmpty.String

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Errors
open PurescriptLanguageCstParser.Layout
open NonEmpty.String

namespace PurescriptLanguageCstParser.Lexer

/--
The result of a lexing operation.
-/
inductive LexResult (e : Type) (α : Type) where
  | LexFail (err : e) (remaining : String)
  | LexSucc (val : α) (remaining : String)
  deriving Repr, BEq

instance {e α : Type} [Inhabited α] : Inhabited (LexResult e α) where
  default := .LexSucc default ""

/--
The Lex monad for parsing tokens from a string.
-/
structure Lex (e : Type) (α : Type) where
  run : String → LexResult e α

namespace Lex

def functor (f : α → β) (l : Lex e α) : Lex e β :=
  { run := fun s =>
    match l.run s with
    | .LexFail err rem => .LexFail err rem
    | .LexSucc val rem => .LexSucc (f val) rem
  }

def apply (l1 : Lex e (β → α)) (l2 : Lex e β) : Lex e α :=
  { run := fun s =>
    match l1.run s with
    | .LexFail err rem => .LexFail err rem
    | .LexSucc f rem' =>
      match l2.run rem' with
      | .LexFail err rem'' => .LexFail err rem''
      | .LexSucc x rem'' => .LexSucc (f x) rem''
  }

def pure (x : α) : Lex e α :=
  { run := fun s => .LexSucc x s }

def bind (l1 : Lex e α) (k : α → Lex e β) : Lex e β :=
  { run := fun s =>
    match l1.run s with
    | .LexFail err rem => .LexFail err rem
    | .LexSucc val rem' => (k val).run rem'
  }

def alt (l1 : Lex e α) (l2 : Lex e α) : Lex e α :=
  { run := fun s =>
    match l1.run s with
    | .LexFail err rem =>
      if rem == s then l2.run s
      else .LexFail err rem
    | .LexSucc val rem => .LexSucc val rem
  }

def try_ (l : Lex e α) : Lex e α :=
  { run := fun s =>
    match l.run s with
    | .LexFail err _ => .LexFail err s
    | .LexSucc val rem => .LexSucc val rem
  }

end Lex

instance : Functor (Lex e) where map := Lex.functor
instance : Seq (Lex e) where seq f x := Lex.apply f (x ())
instance : SeqLeft (Lex e) where seqLeft x y := Lex.apply (Lex.functor (fun a _ => a) x) (y ())
instance : SeqRight (Lex e) where seqRight x y := Lex.apply (Lex.functor (fun _ b => b) x) (y ())
instance : Pure (Lex e) where pure := Lex.pure
instance : Bind (Lex e) where bind := Lex.bind
instance : OrElse (Lex e α) where orElse l1 l2 := Lex.alt l1 (l2 ())

instance : Inhabited Token where
  default := .Tick

def isSymbol (c : Char) : Bool :=
  let symbols := ":!#$%&*+./<=>?@\\^|~-".toList
  symbols.contains c

def bumpText (pos : SourcePos) (colOffset : Nat) (str : String) : SourcePos :=
  let rec go (line : Nat) (column : Nat) (cs : List Char) : SourcePos :=
    match cs with
    | [] => { line := line.toUSize, column := (column + colOffset).toUSize }
    | '\n' :: rest => go (line + 1) 0 rest
    | '\r' :: '\n' :: rest => go (line + 1) 0 rest
    | '\r' :: rest => go line (column + 1) rest
    | _ :: rest => go line (column + 1) rest
  go pos.line.toNat pos.column.toNat str.toList

def bumpToken (pos : SourcePos) (tok : Token) : SourcePos :=
  match tok with
  | .LeftParen => { pos with column := pos.column + 1 }
  | .RightParen => { pos with column := pos.column + 1 }
  | .LeftBrace => { pos with column := pos.column + 1 }
  | .RightBrace => { pos with column := pos.column + 1 }
  | .LeftSquare => { pos with column := pos.column + 1 }
  | .RightSquare => { pos with column := pos.column + 1 }
  | .LeftArrow .ASCII => { pos with column := pos.column + 2 }
  | .LeftArrow .Unicode => { pos with column := pos.column + 1 }
  | .RightArrow .ASCII => { pos with column := pos.column + 2 }
  | .RightArrow .Unicode => { pos with column := pos.column + 1 }
  | .RightFatArrow .ASCII => { pos with column := pos.column + 2 }
  | .RightFatArrow .Unicode => { pos with column := pos.column + 1 }
  | .DoubleColon .ASCII => { pos with column := pos.column + 2 }
  | .DoubleColon .Unicode => { pos with column := pos.column + 1 }
  | .Forall .ASCII => { pos with column := pos.column + 6 }
  | .Forall .Unicode => { pos with column := pos.column + 1 }
  | .Equals => { pos with column := pos.column + 1 }
  | .Pipe => { pos with column := pos.column + 1 }
  | .Tick => { pos with column := pos.column + 1 }
  | .Dot => { pos with column := pos.column + 1 }
  | .Comma => { pos with column := pos.column + 1 }
  | .Underscore => { pos with column := pos.column + 1 }
  | .Backslash => { pos with column := pos.column + 1 }
  | .At => { pos with column := pos.column + 1 }
  | .LowerName qual name => { pos with column := pos.column + (if qual.isSome then 1 else 0) + name.toString.length.toUSize }
  | .UpperName qual name => { pos with column := pos.column + (if qual.isSome then 1 else 0) + name.toString.length.toUSize }
  | .Operator qual sym => { pos with column := pos.column + (if qual.isSome then 1 else 0) + sym.toString.length.toUSize }
  | .SymbolName qual sym => { pos with column := pos.column + (if qual.isSome then 1 else 0) + sym.toString.length.toUSize + 2 }
  | .SymbolArrow .Unicode => { pos with column := pos.column + 3 }
  | .SymbolArrow .ASCII => { pos with column := pos.column + 4 }
  | .Hole hole => { pos with column := pos.column + hole.toString.length.toUSize + 1 }
  | .Char raw _ => { pos with column := pos.column + raw.toString.length.toUSize + 2 }
  | .NonEmptyString raw _ => bumpText pos 1 raw.toString
  | .RawString raw => bumpText pos 3 raw.toString
  | .Int raw _ => { pos with column := pos.column + raw.toString.length.toUSize }
  | .Number raw _ => { pos with column := pos.column + raw.toString.length.toUSize }
  | .LayoutStart _ => pos
  | .LayoutSep _ => pos
  | .LayoutEnd _ => pos

def stringDrop (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

def string (mkErr : String → e) (matchStr : String) : Lex (Unit → e) String :=
  { run := fun s =>
    if s.startsWith matchStr then
      .LexSucc matchStr (stringDrop s matchStr.length)
    else
      .LexFail (fun _ => mkErr "Unexpected token") s
  }

def char (mkErr : String → e) (matchChar : Char) : Lex (Unit → e) Char :=
  { run := fun s =>
    match s.toList with
    | [] => .LexFail (fun _ => mkErr "Unexpected EOF") s
    | c :: cs =>
      if c == matchChar then
        .LexSucc matchChar (String.ofList cs)
      else
        .LexFail (fun _ => mkErr "Unexpected character") s
  }

def satisfy (mkErr : String → e) (p : Char → Bool) : Lex (Unit → e) Char :=
  { run := fun s =>
    match s.toList with
    | [] => .LexFail (fun _ => mkErr "Unexpected EOF") s
    | c :: cs =>
      if p c then
        .LexSucc c (String.ofList cs)
      else
        .LexFail (fun _ => mkErr "Unexpected character") s
  }

partial def many (l : Lex e α) : Lex e (Array α) :=
  { run := fun s =>
    let rec go (acc : Array α) (currentStr : String) :=
      match l.run currentStr with
      | .LexSucc val rem =>
        if rem.length < currentStr.length then
          go (acc.push val) rem
        else
          .LexSucc (acc.push val) currentStr
      | .LexFail _ _ => .LexSucc acc currentStr
    go #[] s
  }

def parseProper : Lex (Unit → ParseError) String :=
  { run := fun s =>
    match s.toList with
    | [] => .LexFail (fun _ => ParseError.LexExpected "proper name" "uppercase letter") s
    | c :: cs =>
      if c.isUpper then
        let rec go (acc : List Char) (rem : List Char) :=
          match rem with
          | [] => .LexSucc (String.ofList acc.reverse) ""
          | ch :: rest =>
            if ch.isAlpha || ch.isDigit || ch == '_' || ch == '\'' then
              go (ch :: acc) rest
            else
              .LexSucc (String.ofList acc.reverse) (String.ofList rem)
        go [c] cs
      else
        .LexFail (fun _ => ParseError.LexExpected "proper name" "uppercase letter") s
  }

def parseIdent : Lex (Unit → ParseError) String :=
  { run := fun s =>
    match s.toList with
    | [] => .LexFail (fun _ => ParseError.LexExpected "ident" "lowercase letter or underscore") s
    | c :: cs =>
      if c.isLower || c == '_' then
        let rec go (acc : List Char) (rem : List Char) :=
          match rem with
          | [] => .LexSucc (String.ofList acc.reverse) ""
          | ch :: rest =>
            if ch.isAlpha || ch.isDigit || ch == '_' || ch == '\'' then
              go (ch :: acc) rest
            else
              .LexSucc (String.ofList acc.reverse) (String.ofList rem)
        go [c] cs
      else
        .LexFail (fun _ => ParseError.LexExpected "ident" "lowercase letter or underscore") s
  }

def parseSymbolIdent : Lex (Unit → ParseError) String :=
  { run := fun s =>
    let rec go (acc : List Char) (rem : List Char) :=
      match rem with
      | [] =>
        if acc.isEmpty then .LexFail (fun _ => ParseError.LexExpected "symbol" "symbol character") s
        else .LexSucc (String.ofList acc.reverse) ""
      | ch :: rest =>
        if isSymbol ch then
          go (ch :: acc) rest
        else
          if acc.isEmpty then .LexFail (fun _ => ParseError.LexExpected "symbol" "symbol character") s
          else .LexSucc (String.ofList acc.reverse) (String.ofList rem)
    go [] s.toList
  }

def tokenLeftParen : Lex (Unit → ParseError) Token :=
  Lex.functor (fun _ => Token.LeftParen) (string (fun _ => ParseError.LexExpected "left paren" "(") "(")

def tokenRightParen : Lex (Unit → ParseError) Token :=
  Lex.functor (fun _ => Token.RightParen) (string (fun _ => ParseError.LexExpected "right paren" ")") ")")

def tokenLeftBrace : Lex (Unit → ParseError) Token :=
  Lex.functor (fun _ => Token.LeftBrace) (string (fun _ => ParseError.LexExpected "left brace" "{") "{")

def tokenRightBrace : Lex (Unit → ParseError) Token :=
  Lex.functor (fun _ => Token.RightBrace) (string (fun _ => ParseError.LexExpected "right brace" "}") "}")

def tokenLeftSquare : Lex (Unit → ParseError) Token :=
  Lex.functor (fun _ => Token.LeftSquare) (string (fun _ => ParseError.LexExpected "left square" "[") "[")

def tokenRightSquare : Lex (Unit → ParseError) Token :=
  Lex.functor (fun _ => Token.RightSquare) (string (fun _ => ParseError.LexExpected "right square" "]") "]")

def tokenTick : Lex (Unit → ParseError) Token :=
  Lex.functor (fun _ => Token.Tick) (string (fun _ => ParseError.LexExpected "backtick" "`") "`")

def tokenComma : Lex (Unit → ParseError) Token :=
  Lex.functor (fun _ => Token.Comma) (string (fun _ => ParseError.LexExpected "comma" ",") ",")

def parseHole : Lex (Unit → ParseError) Token :=
  Lex.bind (string (fun _ => ParseError.LexExpected "question mark" "?") "?") fun _ =>
  Lex.bind (Lex.alt parseIdent parseProper) fun name =>
  Lex.pure (Token.Hole (mkNonEmptyString name))

def parseCharLiteral : Lex (Unit → ParseError) Token :=
  Lex.bind (char (fun _ => ParseError.LexExpected "quote" "'") '\'') fun _ =>
  Lex.bind (satisfy (fun _ => ParseError.LexExpected "char" "character") (fun _ => true)) fun c =>
  Lex.bind (char (fun _ => ParseError.LexExpected "quote" "'") '\'') fun _ =>
  Lex.pure (Token.Char (mkNonEmptyString ("'" ++ c.toString ++ "'")) c)

def parseStringLiteral : Lex (Unit → ParseError) Token :=
  Lex.bind (char (fun _ => ParseError.LexExpected "quote" "\"") '"') fun _ =>
    { run := fun str =>
      let rec go (acc : List Char) (rem : List Char) :=
        match rem with
        | [] => .LexFail (fun _ => ParseError.LexExpected "closing quote" "\"") str
        | '"' :: rest =>
          let resStr := String.ofList acc.reverse
          .LexSucc (Token.NonEmptyString (mkNonEmptyString resStr) (mkNonEmptyString resStr)) (String.ofList rest)
        | ch :: rest => go (ch :: acc) rest
      go [] str.toList }

def parseNumericLiteral : Lex (Unit → ParseError) Token :=
  Lex.bind (many (satisfy (fun _ => ParseError.LexExpected "digit" "digit") Char.isDigit)) fun arr =>
    if arr.isEmpty then
      { run := fun s => .LexFail (fun _ => ParseError.LexExpected "digit" "digit") s }
    else
      let s := String.ofList arr.toList
      Lex.pure (Token.Int (mkNonEmptyString s) (IntValue.SmallInt 0))

def token : Lex (Unit → ParseError) Token :=
  Lex.alt parseHole (
  Lex.alt tokenLeftParen (
  Lex.alt tokenRightParen (
  Lex.alt tokenLeftBrace (
  Lex.alt tokenRightBrace (
  Lex.alt tokenLeftSquare (
  Lex.alt tokenRightSquare (
  Lex.alt tokenTick (
  Lex.alt tokenComma (
  Lex.alt parseCharLiteral (
  Lex.alt parseStringLiteral (
  Lex.alt parseNumericLiteral (
  Lex.alt (Lex.bind parseIdent fun s => Lex.pure (Token.LowerName none (mkNonEmptyString s)))
          (Lex.bind parseProper fun s => Lex.pure (Token.UpperName none (mkNonEmptyString s)))
  ))))))))))))

partial def lexWithState (stack : LayoutStack) (pos : SourcePos) (str : String) : Array Token :=
  let rec go (currentStack : LayoutStack) (currentPos : SourcePos) (currentStr : String) (acc : Array Token) :=
    if currentStr.isEmpty then
      acc
    else
      match token.run currentStr with
      | .LexSucc tok remaining =>
        if remaining.length < currentStr.length then
          let nextPos := bumpToken currentPos tok
          go currentStack nextPos remaining (acc.push tok)
        else
          acc
      | .LexFail _ _ =>
        acc
  go stack pos str #[]

def lex (str : String) : Array Token :=
  lexWithState ([] : LayoutStack) { line := 0, column := 0 } str

def lexModule (str : String) : Array Token :=
  lex str

end PurescriptLanguageCstParser.Lexer

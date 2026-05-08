module

public import PurescriptLanguageCstParser.Types
public import PurescriptLanguageCstParser.Traversal
public import PurescriptLanguageCstParser.Print
public import PurescriptLanguageCstParser.Errors
public import PurescriptLanguageCstParser.Layout
public import NonEmpty.CorrectByConstruction.Array
public import PurescriptLanguageCstParser.GenerateFixed
public import PurescriptLanguageCstParser.GenerateFixedTests
public import PurescriptLanguageCstParser.Range
public import PurescriptLanguageCstParser.Lexer
public import PurescriptLanguageCstParser.TokenStream
public import PurescriptLanguageCstParser.Parser.Monad
public import PurescriptLanguageCstParser.ModuleGraph

@[expose] public section

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Print
open PurescriptLanguageCstParser.Errors
open PurescriptLanguageCstParser.TokenStream
open PurescriptLanguageCstParser.Parser.Monad
open NonEmpty.CorrectByConstruction.Array

namespace PurescriptLanguageCstParser.CST

abbrev Recovered (f : Type → Type) : Type := f RecoveredError

inductive RecoveredParserResult (f : Type → Type) where
  | ParseSucceeded (value : f Empty)
  | ParseSucceededWithErrors (value : Recovered f) (errors : NonEmptyArray PositionedError)
  | ParseFailed (error : PositionedError)

def defaultError : PositionedError :=
  { position := { line := 0, column := 0 }
    error := .UnexpectedEof }

unsafe def toRecoveredParserResult {f : Type → Type} :
    Except PositionedError ((Recovered f) × Array PositionedError) → RecoveredParserResult f
  | .error err => .ParseFailed err
  | .ok (value, errors) =>
      match NonEmptyArray.fromArray? errors with
      | some nea => .ParseSucceededWithErrors value nea
      | none => .ParseSucceeded (unsafeCast value)

unsafe def toRecovered {f : Type → Type} : f Empty → Recovered f := unsafeCast

unsafe def runRecoveredParser {f : Type → Type} (_ : Parser (Recovered f)) (_ : TokenStream) : RecoveredParserResult f :=
  .ParseFailed defaultError

def lexModule (_ : String) : TokenStream :=
  PurescriptLanguageCstParser.TokenStream.TokenStream.TokenEOF { line := 0, column := 0 } #[]

def lex : String → TokenStream := lexModule

def parseModule : String → RecoveredParserResult Module := fun _ =>
  .ParseFailed defaultError

structure PartialModule (e : Type) where
  header : ModuleHeader e
  full : Unit → RecoveredParserResult Module

def parsePartialModule : String → RecoveredParserResult (PartialModule) := fun _ =>
  .ParseFailed defaultError

def parseImportDecl : String → RecoveredParserResult ImportDecl := fun _ =>
  .ParseFailed defaultError

def parseDecl : String → RecoveredParserResult Declaration := fun _ =>
  .ParseFailed defaultError

def parseExpr : String → RecoveredParserResult Expr := fun _ =>
  .ParseFailed defaultError

def parseType : String → RecoveredParserResult Type_ := fun _ =>
  .ParseFailed defaultError

def parseBinder : String → RecoveredParserResult Binder := fun _ =>
  .ParseFailed defaultError

def printModule {e : Type} (_ : Module e) : String :=
  ""

end PurescriptLanguageCstParser.CST

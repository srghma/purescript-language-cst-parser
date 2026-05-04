module

public import PurescriptLanguageCstParser.PureScript.CST.Types.PType
public import PurescriptLanguageCstParser.PureScript.CST.Types.ExprLeafs
meta import PurescriptLanguageCstParser.GenerateFixed

@[expose] public section

namespace PureScript.CST.Types

-- https://github.com/leanprover/lean4/issues/13465#issuecomment-4349653768
/--
info: generate_fixed_mutual expansion:
mutual
  inductive LetBindingRecursive (e : Type) : Type where
    | Signature (labeled : Labeled (Name Ident) (Type_ e)) : LetBindingRecursive e
    | Name (fields : ValueBindingFieldsRecursive e) : LetBindingRecursive e
    | Pattern (binder : Binder e) (token : SourceToken) (where_ : WhereRecursive e) : LetBindingRecursive e
    | Error (data : e) : LetBindingRecursive e
    deriving Repr, BEq
  inductive WhereRecursive (e : Type) : Type where
    |
    mk (expr : Expr e)
      (bindings : Option (SourceToken × NonEmpty.CorrectByConstruction.Array.NonEmptyArray (LetBindingRecursive e))) :
      WhereRecursive e
    deriving Repr, BEq
  inductive GuardedRecursive (e : Type) : Type where
    | Unconditional (token : SourceToken) (where_ : WhereRecursive e) : GuardedRecursive e
    |
    Guarded (branches : NonEmpty.CorrectByConstruction.Array.NonEmptyArray (GuardedExprRecursive e)) :
      GuardedRecursive e
    deriving Repr, BEq
  inductive GuardedExprRecursive (e : Type) : Type where
    |
    mk (bar : SourceToken) (patterns : Separated (PatternGuardF e (Expr e))) (separator : SourceToken)
      (where_ : WhereRecursive e) : GuardedExprRecursive e
    deriving Repr, BEq
  inductive ValueBindingFieldsRecursive (e : Type) : Type where
    | mk (name : Name Ident) (binders : Array (Binder e)) (guarded : GuardedRecursive e) : ValueBindingFieldsRecursive e
    deriving Repr, BEq
  inductive DoStatementRecursive (e : Type) : Type where
    |
    Let (token : SourceToken) (bindings : NonEmpty.CorrectByConstruction.Array.NonEmptyArray (LetBindingRecursive e)) :
      DoStatementRecursive e
    | Discard (expr : Expr e) : DoStatementRecursive e
    | Bind (binder : Binder e) (token : SourceToken) (expr : Expr e) : DoStatementRecursive e
    | Error (data : e) : DoStatementRecursive e
    deriving Repr, BEq
  inductive DoBlockRecursive (e : Type) : Type where
    |
    mk (keyword : SourceToken)
      (statements : NonEmpty.CorrectByConstruction.Array.NonEmptyArray (DoStatementRecursive e)) : DoBlockRecursive e
    deriving Repr, BEq
  inductive AdoBlockRecursive (e : Type) : Type where
    |
    mk (keyword : SourceToken) (statements : Array (DoStatementRecursive e)) (in_ : SourceToken) (result : Expr e) :
      AdoBlockRecursive e
    deriving Repr, BEq
  inductive Expr (e : Type) : Type where
    | Hole (name : Name Ident) : Expr e
    | Section (token : SourceToken) : Expr e
    | Ident (name : QualifiedName Ident) : Expr e
    | Constructor (name : QualifiedName Proper) : Expr e
    | Boolean (token : SourceToken) (val : Bool) : Expr e
    | Char (token : SourceToken) (val : Char) : Expr e
    | NonEmptyString (token : SourceToken) (val : NonEmpty.String.NonEmptyString) : Expr e
    | Int (token : SourceToken) (val : IntValue) : Expr e
    | Number (token : SourceToken) (val : Float) : Expr e
    | Array (items : Delimited (Expr e)) : Expr e
    | Record (fields : Delimited (RecordLabeled (Expr e))) : Expr e
    | Parens (wrapped : Wrapped (Expr e)) : Expr e
    | Typed (expr : Expr e) (token : SourceToken) (type_ : Type_ e) : Expr e
    |
    Infix (head : Expr e) (tail : NonEmpty.CorrectByConstruction.Array.NonEmptyArray (Wrapped (Expr e) × Expr e)) :
      Expr e
    |
    Op (head : Expr e) (ops : NonEmpty.CorrectByConstruction.Array.NonEmptyArray (QualifiedName Operator × Expr e)) :
      Expr e
    | OpName (name : QualifiedName Operator) : Expr e
    | Negate (token : SourceToken) (expr : Expr e) : Expr e
    | RecordAccessor (data : RecordAccessorF (Expr e)) : Expr e
    | RecordUpdate (expr : Expr e) (updates : DelimitedNonEmpty (RecordUpdateF (Expr e))) : Expr e
    | App (fn : Expr e) (args : NonEmpty.CorrectByConstruction.Array.NonEmptyArray (AppSpineF e (Expr e))) : Expr e
    | Lambda (data : LambdaF e (Expr e)) : Expr e
    | If (data : IfThenElseF (Expr e)) : Expr e
    | Case (data : CaseOfF e (Expr e) (GuardedRecursive e)) : Expr e
    | Let (data : LetInF (Expr e) (LetBindingRecursive e)) : Expr e
    | Do (data : DoBlockRecursive e) : Expr e
    | Ado (data : AdoBlockRecursive e) : Expr e
    | Error (data : e) : Expr e
    deriving Repr, BEq
end
-/
#guard_msgs in
set_option linter.unusedVariables false in
generate_fixed_mutual?
  generate_fixed inductive LetBindingRecursive (e : Type) from LetBindingF
    fill valueBindingFields_e with (ValueBindingFieldsRecursive e)
    fill where_e with (WhereRecursive e)
    deriving Repr, BEq

  generate_fixed inductive WhereRecursive (e : Type) from WhereF
    fill expr_e with (Expr e)
    fill letBinding_e with (LetBindingRecursive e)
    deriving Repr, BEq

  generate_fixed inductive GuardedRecursive (e : Type) from GuardedF
    fill where_e with (WhereRecursive e)
    fill guardedExpr_e with (GuardedExprRecursive e)
    deriving Repr, BEq

  generate_fixed inductive GuardedExprRecursive (e : Type) from GuardedExprF
    fill expr_e with (Expr e)
    fill where_e with (WhereRecursive e)
    deriving Repr, BEq

  generate_fixed inductive ValueBindingFieldsRecursive (e : Type) from ValueBindingFieldsF
    fill guardedExpr_e with (GuardedRecursive e)
    deriving Repr, BEq

  generate_fixed inductive DoStatementRecursive (e : Type) from DoStatementF
    fill expr_e with (Expr e)
    fill letBindingRecursive_e with (LetBindingRecursive e)
    deriving Repr, BEq

  generate_fixed inductive DoBlockRecursive (e : Type) from DoBlockF
    fill doStatement_e with (DoStatementRecursive e)
    deriving Repr, BEq

  generate_fixed inductive AdoBlockRecursive (e : Type) from AdoBlockF
    fill expr_e with (Expr e)
    fill doStatement_e with (DoStatementRecursive e)
    deriving Repr, BEq

  generate_fixed inductive Expr (e : Type) from ExprF
    fill expr_e with (Expr e)
    fill doBlock with (DoBlockRecursive e)
    fill adoBlock with (AdoBlockRecursive e)
    fill guardedRecursive_e with (GuardedRecursive e)
    fill letBindingRecursive_e with (LetBindingRecursive e)
    deriving Repr, BEq
end_generate_fixed_mutual

end PureScript.CST.Types

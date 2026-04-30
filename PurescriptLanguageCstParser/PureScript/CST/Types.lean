import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String

open NonEmpty.CorrectByConstruction.Array

namespace PureScript.CST.Types

def ModuleName := NonEmptyString
  deriving Repr, BEq, Ord

structure SourcePos where
  line : USize
  column : USize
  deriving Repr, BEq, Ord

structure SourceRange where
  start : SourcePos
  end_ : SourcePos
  deriving Repr, BEq, Ord

inductive CommentWithoutLine
  | Comment (s : NonEmptyString)
  | Space (i : USize)
  deriving Repr, BEq, Ord

inductive Comment (l : Type)
  | Comment (s : NonEmptyString)
  | Space (i : USize)
  | Line (l : l) (i : USize)
  deriving Repr, BEq, Ord

inductive LineFeed
  | LF
  | CRLF
  deriving Repr, BEq, Ord

inductive SourceStyle
  | ASCII
  | Unicode
  deriving Repr, BEq, Ord

inductive IntValue
  | SmallInt (i : USize)
  | BigInt (s : NonEmptyString)
  | BigHex (s : NonEmptyString)
  deriving Repr, BEq, Ord

inductive Token
  | LeftParen
  | RightParen
  | LeftBrace
  | RightBrace
  | LeftSquare
  | RightSquare
  | LeftArrow (style : SourceStyle)
  | RightArrow (style : SourceStyle)
  | RightFatArrow (style : SourceStyle)
  | DoubleColon (style : SourceStyle)
  | Forall (style : SourceStyle)
  | Equals
  | Pipe
  | Tick
  | Dot
  | Comma
  | Underscore
  | Backslash
  | At
  | LowerName (module_ : Option ModuleName) (name : NonEmptyString)
  | UpperName (module_ : Option ModuleName) (name : NonEmptyString)
  | Operator (module_ : Option ModuleName) (name : NonEmptyString)
  | SymbolName (module_ : Option ModuleName) (name : NonEmptyString)
  | SymbolArrow (style : SourceStyle)
  | Hole (name : NonEmptyString)
  | Char (s : NonEmptyString) (c : Char)
  | NonEmptyString (s : NonEmptyString) (value : NonEmptyString)
  | RawString (s : NonEmptyString)
  | Int (s : NonEmptyString) (value : IntValue)
  | Number (s : NonEmptyString) (value : Float)
  | LayoutStart (i : USize)
  | LayoutSep (i : USize)
  | LayoutEnd (i : USize)
  deriving Repr, BEq --, Ord -- bc of Float

structure SourceToken where
  range : SourceRange
  leadingComments : Array (Comment LineFeed)
  trailingComments : Array CommentWithoutLine
  value : Token
  deriving Repr, BEq

def Ident := NonEmptyString
  deriving Repr, BEq, Ord

def Proper := NonEmptyString
  deriving Repr, BEq, Ord

def Label := NonEmptyString
  deriving Repr, BEq, Ord

def Operator := NonEmptyString
  deriving Repr, BEq, Ord

structure Name (α : Type) where
  token : SourceToken
  name : α
  deriving Repr, BEq

structure QualifiedName (α : Type) where
  token : SourceToken
  module_ : Option ModuleName
  name : α
  deriving Repr, BEq

structure Wrapped (α : Type) where
  open_ : SourceToken
  value : α
  close : SourceToken
  deriving Repr, BEq

structure Separated (α : Type) where
  head : α
  tail : Array (SourceToken × α)
  deriving Repr, BEq

structure Labeled (α β : Type) where
  label : α
  separator : SourceToken
  value : β
  deriving Repr, BEq

structure Prefixed (α : Type) where
  prefix_ : Option SourceToken
  value : α
  deriving Repr, BEq

-- why not def or abbrev? will break in recursive inductive types (e.g. Expr)
inductive Delimited (α : Type)
  | mk (v : Wrapped (Option (Separated α)))
  deriving Repr, BEq

inductive DelimitedNonEmpty (α : Type)
  | mk (v : Wrapped (Separated α))
  deriving Repr, BEq

inductive OneOrDelimited (α : Type)
  | One (value : α)
  | Many (separated : DelimitedNonEmpty α)
  deriving Repr, BEq

structure TokenAnd (α : Type) where
  token : SourceToken
  value : α
  deriving Repr, BEq

inductive TypeVarBindingF (a type_e : Type)
  | Kinded (wrapped : Wrapped (Labeled a type_e))
  | Name (name : a)
  deriving Repr, BEq

structure RowF (e type_e : Type) where
  labels : Option (Separated (Labeled (Name Label) (type_e)))
  tail : Option (SourceToken × type_e)
  deriving Repr, BEq

inductive TypeF (e type_e : Type)
  | Var (name : Name Ident)
  | Constructor (name : QualifiedName Proper)
  | Wildcard (token : SourceToken)
  | Hole (name : Name Ident)
  | NonEmptyString (token : SourceToken) (value : NonEmptyString)
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (value : IntValue)
  | Row (wrapped : Wrapped (RowF e type_e))
  | Record (wrapped : Wrapped (RowF e type_e))
  | Forall (open_ : SourceToken) (bindings : NonEmptyArray (TypeVarBindingF (Prefixed (Name Ident)) type_e)) (close : SourceToken) (body : type_e)
  | Kinded (type_ : type_e) (sep : SourceToken) (kind : type_e)
  | App (fn : type_e) (args : NonEmptyArray type_e)
  | Op (first : type_e) (ops : NonEmptyArray (QualifiedName Operator × type_e))
  | OpName (name : QualifiedName Operator)
  | Arrow (dom : type_e) (token : SourceToken) (codom : type_e)
  | ArrowName (token : SourceToken)
  | Constrained (type_ : type_e) (token : SourceToken) (body : type_e)
  | Parens (wrapped : Wrapped type_e)
  | Error (data : e)
  deriving Repr, BEq

inductive Type_ (e : Type)
  | mk (v : TypeF e (Type_ e))
  deriving Repr, BEq

---------------------------------------------------------------------------------------------------------
inductive DataMembers
  | All (token : SourceToken)
  | Enumerated (separated : Delimited (Name Proper))
  deriving Repr, BEq

inductive Export (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Module (token : SourceToken) (name : Name ModuleName)
  | Error (data : e)
  deriving Repr, BEq

---------------------------------------------------------------------------------------------------------
structure DataHead (e : Type) where
  keyword : SourceToken
  name : Name Proper
  parameters : Array (TypeVarBindingF (Name Ident) (Type_ e))
  deriving Repr, BEq

structure DataCtor (e : Type) where
  name : Name Proper
  parameters : Array (Type_ e)
  deriving Repr, BEq

inductive ClassFundep
  | Determined (token : SourceToken) (names : NonEmptyArray (Name Ident))
  | Determines (left : NonEmptyArray (Name Ident)) (token : SourceToken) (right : NonEmptyArray (Name Ident))
  deriving Repr, BEq

structure ClassHead (e : Type) where
  keyword : SourceToken
  typeConstraint : Option (OneOrDelimited (Type_ e) × SourceToken)
  name : Name Proper
  parameters : Array (TypeVarBindingF (Name Ident) (Type_ e))
  fundependencies : Option (SourceToken × Separated ClassFundep)
  deriving Repr, BEq

structure InstanceHead (e : Type) where
  keyword : SourceToken
  name : Option (Name Ident × SourceToken)
  constraints : Option (OneOrDelimited (Type_ e) × SourceToken)
  className : QualifiedName Proper
  types : Array (Type_ e)
  deriving Repr, BEq

inductive RecordLabeled (a : Type)
  | Pun (name : Name Ident)
  | Field (label : Name Label) (separator : SourceToken) (value : a)
  deriving Repr, BEq

inductive BinderF (e binder_e : Type)
  | Wildcard (token : SourceToken)
  | Var (name : Name Ident)
  | Named (name : Name Ident) (token : SourceToken) (binder : binder_e)
  | Constructor (name : QualifiedName Proper) (args : Array binder_e)
  | Boolean (token : SourceToken) (val : Bool)
  | Char (token : SourceToken) (val : Char)
  | NonEmptyString (token : SourceToken) (val : NonEmptyString)
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (val : IntValue)
  | Number (prefix_ : Option SourceToken) (token : SourceToken) (val : Float)
  | Array (items : Delimited (binder_e))
  | Record (fields : Delimited (RecordLabeled (binder_e)))
  | Parens (wrapped : Wrapped (binder_e))
  | Typed (binder : binder_e) (token : SourceToken) (type_ : Type_ e)
  | Op (first : binder_e) (ops : NonEmptyArray (QualifiedName Operator × binder_e))
  | Error (data : e)
  deriving Repr, BEq

inductive Binder (e : Type)
  | mk : BinderF e (Binder e) → Binder e
  deriving Repr, BEq

structure AndToken (α : Type) where
  value : α
  token : SourceToken
  deriving Repr, BEq

inductive AppSpineF (e expr_e : Type)
  | Type_ (token : SourceToken) (type_ : Type_ e)
  | Term (expr : expr_e)
  deriving Repr, BEq

inductive RecordUpdateF (e expr_e : Type)
  | Leaf (label : Name Label) (token : SourceToken) (expr : expr_e)
  | Branch (label : Name Label) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
  deriving Repr, BEq

structure RecordAccessorF (expr_e : Type) where
  expr : expr_e
  dot : SourceToken
  path : Separated (Name Label)
  deriving Repr, BEq

structure LambdaF (e expr_e : Type) where
  symbol : SourceToken
  binders : NonEmptyArray (Binder e)
  arrow : SourceToken
  body : expr_e
  deriving Repr, BEq

structure IfThenElseF (expr_e : Type) where
  keyword : SourceToken
  cond : expr_e
  then_ : SourceToken
  true_ : expr_e
  else_ : SourceToken
  false_ : expr_e
  deriving Repr, BEq

structure PatternGuardF (e expr_e : Type) where
  binder : Option (Binder e × SourceToken)
  expr : expr_e
  deriving Repr, BEq

-- ```mermaid
-- graph TD
--     LB[LetBindingF] -->|Pattern| W[WhereF]
--     LB -->|Name| VBF[ValueBindingFieldsF]
--
--     VBF -->|guarded| G[GuardedF]
--
--     G -->|Unconditional| W
--     G -->|Guarded| GE[GuardedExprF]
--
--     GE -->|where_| W
--
--     W -->|bindings| LB
--
--     subgraph "The Mutual Cycle"
--     LB
--     VBF
--     G
--     GE
--     W
--     end
-- ```

mutual

  structure ValueBindingFieldsF (e expr_e : Type) where
    name    : Name Ident
    binders : Array (Binder e)
    guarded : GuardedF e expr_e
  deriving Repr, BEq

  inductive GuardedF (e expr_e : Type) where
  | Unconditional (token : SourceToken) (where_ : WhereF e expr_e)
  | Guarded (branches : NonEmptyArray (GuardedExprF e expr_e))
  deriving Repr, BEq

  structure GuardedExprF (e expr_e : Type) where
    bar        : SourceToken
    patterns   : Separated (PatternGuardF e expr_e)
    separator  : SourceToken
    where_     : WhereF e expr_e
  deriving Repr, BEq

  structure WhereF (e expr_e : Type) where
    expr     : expr_e
    bindings : Option (SourceToken × NonEmptyArray (LetBindingF e expr_e))
  deriving Repr, BEq

  inductive LetBindingF (e expr_e : Type) where
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Name (fields : ValueBindingFieldsF e expr_e)
  | Pattern (binder : Binder e) (token : SourceToken) (where_ : WhereF e expr_e)
  | Error (data : e)
  deriving Repr, BEq

end

structure CaseOfF (e expr_e : Type) where
  keyword : SourceToken
  head : Separated expr_e
  of : SourceToken
  branches : NonEmptyArray (Separated (Binder e) × GuardedF e expr_e)
  deriving Repr, BEq

structure LetInF (e expr_e : Type) where
  keyword : SourceToken
  bindings : NonEmptyArray (LetBindingF e expr_e)
  in_ : SourceToken
  body : expr_e
  deriving Repr, BEq

inductive DoStatementF (e expr_e : Type)
  | Let (token : SourceToken) (bindings : NonEmptyArray (LetBindingF e expr_e))
  | Discard (expr : expr_e)
  | Bind (binder : Binder e) (token : SourceToken) (expr : expr_e)
  | Error (data : e)
  deriving Repr, BEq

structure DoBlockF (e expr_e : Type) where
  keyword : SourceToken
  statements : NonEmptyArray (DoStatementF e expr_e)
  deriving Repr, BEq

structure AdoBlockF (e expr_e : Type) where
  keyword : SourceToken
  statements : Array (DoStatementF e expr_e)
  in_ : SourceToken
  result : expr_e
  deriving Repr, BEq

inductive ExprF (e expr_e : Type)
  | Hole (name : Name Ident)
  | Section (token : SourceToken)
  | Ident (name : QualifiedName Ident)
  | Constructor (name : QualifiedName Proper)
  | Boolean (token : SourceToken) (val : Bool)
  | Char (token : SourceToken) (val : Char)
  | NonEmptyString (token : SourceToken) (val : NonEmptyString)
  | Int (token : SourceToken) (val : IntValue)
  | Number (token : SourceToken) (val : Float)
  | Array (items : Delimited expr_e)
  | Record (fields : Delimited (RecordLabeled expr_e))
  | Parens (wrapped : Wrapped expr_e)
  | Typed (expr : expr_e) (token : SourceToken) (type_ : Type_ e)
  | Infix (head : expr_e) (tail : NonEmptyArray (Wrapped expr_e × expr_e))
  | Op (head : expr_e) (ops : NonEmptyArray (QualifiedName Operator × expr_e))
  | OpName (name : QualifiedName Operator)
  | Negate (token : SourceToken) (expr : expr_e)
  | RecordAccessor (data : RecordAccessorF expr_e)
  | RecordUpdate (expr : expr_e) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
  | App (fn : expr_e) (args : NonEmptyArray (AppSpineF e expr_e))
  | Lambda (data : LambdaF e expr_e)
  | If (data : IfThenElseF expr_e)
  | Case (data : CaseOfF e expr_e)
  | Let (data : LetInF e expr_e)
  | Do (data : DoBlockF e expr_e)
  | Ado (data : AdoBlockF e expr_e)
  | Error (data : e)
  deriving Repr, BEq

inductive Expr (e : Type)
  | mk : ExprF e (Expr e) → Expr e
  deriving Repr, BEq

-----------------------------------------------------------------------------------------------------------

inductive InstanceBinding (e : Type)
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Name (fields : ValueBindingFieldsF e (Expr e))
  deriving Repr, BEq

structure Instance (e : Type) where
  head : InstanceHead e
  body : Option (SourceToken × NonEmptyArray (InstanceBinding e))
  deriving Repr, BEq

inductive Foreign (e : Type)
  | Value (labeled : Labeled (Name Ident) (Type_ e))
  | Data (keyword : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
  | Kind (keyword : SourceToken) (name : Name Proper)
  deriving Repr, BEq

inductive Fixity
  | Infix
  | Infixl
  | Infixr
  deriving Repr, BEq, Ord

inductive FixityOp
  | Value (name : QualifiedName (Ident ⊕ Proper)) (token : SourceToken) (op : Name Operator)
  | Type_ (token1 : SourceToken) (name : QualifiedName Proper) (token2 : SourceToken) (op : Name Operator)
  deriving Repr, BEq

structure FixityFields where
  keyword : SourceToken × Fixity
  prec : SourceToken × USize
  operator : FixityOp
  deriving Repr, BEq

inductive Role
  | Nominal
  | Representational
  | Phantom
  deriving Repr, BEq, Ord

inductive Declaration (e : Type)
  | Data (head : DataHead e) (optionSeparator : Option (SourceToken × (Separated (DataCtor e))))
  | Type_ (head : DataHead e) (token : SourceToken) (type_ : Type_ e)
  | Newtype (head : DataHead e) (token : SourceToken) (name : Name Proper) (type_ : Type_ e)
  | Class (head : ClassHead e) (optionSeparator : Option (SourceToken × NonEmptyArray (Labeled (Name Ident) (Type_ e))))
  | InstanceChain (separated : Separated (Instance e))
  | Derive (keyword : SourceToken) (optionToken : Option SourceToken) (head : InstanceHead e)
  | KindSignature (token1 : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Value (fields : ValueBindingFieldsF e (Expr e))
  | Fixity (fields : FixityFields)
  | Foreign (token1 : SourceToken) (token2 : SourceToken) (foreign : Foreign e)
  | Role (token1 : SourceToken) (token2 : SourceToken) (name : Name Proper) (roles : NonEmptyArray (SourceToken × Role))
  | Error (data : e)
  deriving Repr, BEq

-----------------------------------------------------------------------------------------------------------

inductive Import (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Error (data : e)
  deriving Repr, BEq

structure ImportDecl (e : Type) where
  keyword : SourceToken
  module_ : Name ModuleName
  importList : Option (Option SourceToken × DelimitedNonEmpty (Import e))
  qualified : Option (SourceToken × Name ModuleName)
  deriving Repr, BEq
-----------------------------------------------------------------------------------------------------------

structure ModuleHeader (e : Type) where
  keyword : SourceToken
  name : Name ModuleName
  exports : Option (DelimitedNonEmpty (Export e))
  where_ : SourceToken
  imports : Array (ImportDecl e)
  deriving Repr, BEq

structure ModuleBody (e : Type) where
  decls : Array (Declaration e)
  trailingComments : Array (Comment LineFeed)
  end_ : SourcePos
  deriving Repr, BEq

structure Module (e : Type) where
  header : ModuleHeader e
  body : ModuleBody e
  deriving Repr, BEq

end PureScript.CST.Types

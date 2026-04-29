import NonEmpty.CorrectByConstruction.Array

open NonEmpty.CorrectByConstruction.Array

namespace PureScript.CST.Types

def ModuleName := String
  deriving Repr, BEq, Ord

structure SourcePos where
  line : Int
  column : Int
  deriving Repr, BEq, Ord

structure SourceRange where
  start : SourcePos
  end_ : SourcePos
  deriving Repr, BEq, Ord

inductive CommentWithoutLine
  | Comment : String → CommentWithoutLine
  | Space : Int → CommentWithoutLine
  deriving Repr, BEq, Ord

inductive Comment (l : Type)
  | Comment : String → Comment l
  | Space : Int → Comment l
  | Line : l → Int → Comment l
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
  | SmallInt : Int → IntValue
  | BigInt : String → IntValue
  | BigHex : String → IntValue
  deriving Repr, BEq, Ord

inductive Token
  | LeftParen
  | RightParen
  | LeftBrace
  | RightBrace
  | LeftSquare
  | RightSquare
  | LeftArrow : SourceStyle → Token
  | RightArrow : SourceStyle → Token
  | RightFatArrow : SourceStyle → Token
  | DoubleColon : SourceStyle → Token
  | Forall : SourceStyle → Token
  | Equals
  | Pipe
  | Tick
  | Dot
  | Comma
  | Underscore
  | Backslash
  | At
  | LowerName : Option ModuleName → String → Token
  | UpperName : Option ModuleName → String → Token
  | Operator : Option ModuleName → String → Token
  | SymbolName : Option ModuleName → String → Token
  | SymbolArrow : SourceStyle → Token
  | Hole : String → Token
  | Char : String → Char → Token
  | String : String → String → Token
  | RawString : String → Token
  | Int : String → IntValue → Token
  | Number : String → Float → Token
  | LayoutStart : Int → Token
  | LayoutSep : Int → Token
  | LayoutEnd : Int → Token
  deriving Repr, BEq --, Ord -- bc of Float

structure SourceToken where
  range : SourceRange
  leadingComments : Array (Comment LineFeed)
  trailingComments : Array CommentWithoutLine
  value : Token
  deriving Repr, BEq

def Ident := String
  deriving Repr, BEq, Ord

def Proper := String
  deriving Repr, BEq, Ord

def Label := String
  deriving Repr, BEq, Ord

def Operator := String
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
  | mk : Wrapped (Option (Separated α)) → Delimited α
  deriving Repr, BEq

inductive DelimitedNonEmpty (α : Type)
  | mk : Wrapped (Separated α) → DelimitedNonEmpty α
  deriving Repr, BEq

inductive OneOrDelimited (α : Type)
  | One : α → OneOrDelimited α
  | Many : DelimitedNonEmpty α → OneOrDelimited α
  deriving Repr, BEq

structure TokenAnd (α : Type) where
  token : SourceToken
  value : α
  deriving Repr, BEq

inductive TypeVarBinding_impl (a type_e : Type)
  | Kinded : Wrapped (Labeled a type_e) → TypeVarBinding_impl a type_e
  | Name : a → TypeVarBinding_impl a type_e
  deriving Repr, BEq

mutual

inductive Type_ (e : Type)
  | Var : Name Ident → Type_ e
  | Constructor : QualifiedName Proper → Type_ e
  | Wildcard : SourceToken → Type_ e
  | Hole : Name Ident → Type_ e
  | String : SourceToken → String → Type_ e
  | Int : Option SourceToken → SourceToken → IntValue → Type_ e
  | Row : Wrapped (Row e) → Type_ e
  | Record : Wrapped (Row e) → Type_ e
  | Forall : SourceToken → NonEmptyArray (TypeVarBinding_impl (Prefixed (Name Ident)) (Type_ e)) → SourceToken → Type_ e → Type_ e
  | Kinded : Type_ e → SourceToken → Type_ e → Type_ e
  | App : Type_ e → NonEmptyArray (Type_ e) → Type_ e
  | Op : Type_ e → NonEmptyArray (QualifiedName Operator × Type_ e) → Type_ e
  | OpName : QualifiedName Operator → Type_ e
  | Arrow : Type_ e → SourceToken → Type_ e → Type_ e
  | ArrowName : SourceToken → Type_ e
  | Constrained : Type_ e → SourceToken → Type_ e → Type_ e
  | Parens : Wrapped (Type_ e) → Type_ e
  | Error : e → Type_ e
  deriving Repr, BEq

structure RowTail (e : Type) where
  token : SourceToken
  type_ : Type_ e
  deriving Repr, BEq

structure Row (e : Type) where
  labels : Option (Separated (Labeled (Name Label) (Type_ e)))
  tail : Option (RowTail e)
  deriving Repr, BEq

end
---------------------------------------------------------------------------------------------------------
inductive DataMembers
  | All : SourceToken → DataMembers
  | Enumerated : Delimited (Name Proper) → DataMembers
  deriving Repr, BEq

inductive Export (e : Type)
  | Value : Name Ident → Export e
  | Op : Name Operator → Export e
  | Type_ : Name Proper → Option DataMembers → Export e
  | TypeOp : SourceToken → Name Operator → Export e
  | Class : SourceToken → Name Proper → Export e
  | Module : SourceToken → Name ModuleName → Export e
  | Error : e → Export e
  deriving Repr, BEq

---------------------------------------------------------------------------------------------------------
structure DataHead (e : Type) where
  keyword : SourceToken
  name : Name Proper
  parameters : Array (TypeVarBinding_impl (Name Ident) (Type_ e))
  deriving Repr, BEq

structure DataCtor (e : Type) where
  name : Name Proper
  parameters : Array (Type_ e)
  deriving Repr, BEq

inductive ClassFundep
  | Determined : SourceToken → NonEmptyArray (Name Ident) → ClassFundep
  | Determines : NonEmptyArray (Name Ident) → SourceToken → NonEmptyArray (Name Ident) → ClassFundep
  deriving Repr, BEq

structure ClassHead (e : Type) where
  keyword : SourceToken
  typeConstraint : Option (OneOrDelimited (Type_ e) × SourceToken)
  name : Name Proper
  parameters : Array (TypeVarBinding_impl (Name Ident) (Type_ e))
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
  | Pun : Name Ident → RecordLabeled a
  | Field : Name Label → SourceToken → a → RecordLabeled a
  deriving Repr, BEq

inductive Binder (e : Type)
  | Wildcard : SourceToken → Binder e
  | Var : Name Ident → Binder e
  | Named : Name Ident → SourceToken → Binder e → Binder e
  | Constructor : QualifiedName Proper → Array (Binder e) → Binder e
  | Boolean : SourceToken → Bool → Binder e
  | Char : SourceToken → Char → Binder e
  | String : SourceToken → String → Binder e
  | Int : Option SourceToken → SourceToken → IntValue → Binder e
  | Number : Option SourceToken → SourceToken → Float → Binder e
  | Array : Delimited (Binder e) → Binder e
  | Record : Delimited (RecordLabeled (Binder e)) → Binder e
  | Parens : (Wrapped (Binder e)) → Binder e
  | Typed : Binder e → SourceToken → Type_ e → Binder e
  | Op : Binder e → NonEmptyArray (QualifiedName Operator × Binder e) → Binder e
  | Error : e → Binder e
  deriving Repr, BEq

structure InfixItem (α : Type) where
  leftToken : SourceToken
  left : α
  rightToken : SourceToken
  right : α
  deriving Repr, BEq

structure AndToken (α : Type) where
  value : α
  token : SourceToken
  deriving Repr, BEq

mutual

inductive Expr (e : Type)
  | Hole : Name Ident → Expr e
  | Section : SourceToken → Expr e
  | Ident : QualifiedName Ident → Expr e
  | Constructor : QualifiedName Proper → Expr e
  | Boolean : SourceToken → Bool → Expr e
  | Char : SourceToken → Char → Expr e
  | String : SourceToken → String → Expr e
  | Int : SourceToken → IntValue → Expr e
  | Number : SourceToken → Float → Expr e
  | Array : Delimited (Expr e) → Expr e
  | Record : Delimited (RecordLabeled (Expr e)) → Expr e
  | Parens : (Wrapped (Expr e)) → Expr e
  | Typed : Expr e → SourceToken → Type_ e → Expr e
  | Infix : Expr e → NonEmptyArray (Wrapped (Expr e) × Expr e) → Expr e
  | Op : Expr e → NonEmptyArray (QualifiedName Operator × Expr e) → Expr e
  | OpName : QualifiedName Operator → Expr e
  | Negate : SourceToken → Expr e → Expr e
  | RecordAccessor : RecordAccessor e → Expr e
  | RecordUpdate : Expr e → DelimitedNonEmpty (RecordUpdate e) → Expr e
  | App : Expr e → NonEmptyArray (AppSpine_Expr e) → Expr e
  | Lambda : Lambda e → Expr e
  | If : IfThenElse e → Expr e
  | Case : CaseOf e → Expr e
  | Let : LetIn e → Expr e
  | Do : DoBlock e → Expr e
  | Ado : AdoBlock e → Expr e
  | Error : e → Expr e
  deriving Repr, BEq

inductive AppSpine_Expr (e : Type)
  | Type_ : SourceToken → Type_ e → AppSpine_Expr e
  | Term : Expr e → AppSpine_Expr e
  deriving Repr, BEq

inductive RecordUpdate (e : Type)
  | Leaf : Name Label → SourceToken → Expr e → RecordUpdate e
  | Branch : Name Label → DelimitedNonEmpty (RecordUpdate e) → RecordUpdate e
  deriving Repr, BEq

structure RecordAccessor (e : Type) where
  expr : Expr e
  dot : SourceToken
  path : Separated (Name Label)
  deriving Repr, BEq

structure Lambda (e : Type) where
  symbol : SourceToken
  binders : NonEmptyArray (Binder e)
  arrow : SourceToken
  body : Expr e
  deriving Repr, BEq

structure IfThenElse (e : Type) where
  keyword : SourceToken
  cond : Expr e
  thenToken : SourceToken
  trues_ : Expr e
  elseToken : SourceToken
  false_ : Expr e
  deriving Repr, BEq

inductive Guarded (e : Type)
  | Unconditional : SourceToken → Where e → Guarded e
  | Guarded : NonEmptyArray (GuardedExpr e) → Guarded e
  deriving Repr, BEq

structure CaseOf (e : Type) where
  keyword : SourceToken
  separatedExpr : Separated (Expr e)
  of : SourceToken
  branches : NonEmptyArray (Separated (Binder e) × Guarded e)
  deriving Repr, BEq

structure LetIn (e : Type) where
  keyword : SourceToken
  separatedBindings : NonEmptyArray (LetBinding e)
  in_ : SourceToken
  body : Expr e
  deriving Repr, BEq

structure Where (e : Type) where
  expr : Expr e
  whereBindings : Option (SourceToken × (NonEmptyArray (LetBinding e)))
  deriving Repr, BEq

structure ValueBindingFields (e : Type) where
  name : Name Ident
  binders : Array (Binder e)
  guarded : Guarded e
  deriving Repr, BEq

inductive LetBinding (e : Type)
  | Signature : Labeled (Name Ident) (Type_ e) → LetBinding e
  | Name : ValueBindingFields e → LetBinding e
  | Pattern : Binder e → SourceToken → Where e → LetBinding e
  | Error : e → LetBinding e
  deriving Repr, BEq

structure DoBlock (e : Type) where
  doToken : SourceToken
  statements : NonEmptyArray (DoStatement e)
  deriving Repr, BEq

inductive DoStatement (e : Type)
  | Let : SourceToken → NonEmptyArray (LetBinding e) → DoStatement e
  | Discard : Expr e → DoStatement e
  | Bind : Binder e → SourceToken → Expr e → DoStatement e
  | Error : e → DoStatement e
  deriving Repr, BEq

structure AdoBlock (e : Type) where
  keyword : SourceToken
  statements : Array (DoStatement e)
  in_ : SourceToken
  result : Expr e
  deriving Repr, BEq

structure CaseBranch (e : Type) where
  binders : Separated (Binder e)
  guarded : Guarded e
  deriving Repr, BEq

structure WhereBindings (e : Type) where
  whereToken : SourceToken
  value : Array (LetBinding e)
  deriving Repr, BEq

structure GuardedExpr (e : Type) where
  token : SourceToken
  pattern : Separated (PatternGuard e)
  whereToken : SourceToken
  where_ : Where e
  deriving Repr, BEq

structure PatternGuard (e : Type) where
  binder : Option (Binder e × SourceToken)
  expr : Expr e
  deriving Repr, BEq
end

-----------------------------------------------------------------------------------------------------------

inductive InstanceBinding (e : Type)
  | Signature : Labeled (Name Ident) (Type_ e) → InstanceBinding e
  | Name : ValueBindingFields e → InstanceBinding e
  deriving Repr, BEq

structure Instance (e : Type) where
  head : InstanceHead e
  body : Option (SourceToken × NonEmptyArray (InstanceBinding e))
  deriving Repr, BEq

inductive Foreign (e : Type)
  | Value : Labeled (Name Ident) (Type_ e) → Foreign e
  | Data : SourceToken → Labeled (Name Proper) (Type_ e) → Foreign e
  | Kind : SourceToken → Name Proper → Foreign e
  deriving Repr, BEq

inductive Fixity
  | Infix
  | Infixl
  | Infixr
  deriving Repr, BEq, Ord

inductive FixityOp
  | Value : QualifiedName (Ident ⊕ Proper) → SourceToken → Name Operator → FixityOp
  | Type_ : SourceToken → QualifiedName Proper → SourceToken → Name Operator → FixityOp
  deriving Repr, BEq

structure FixityFields where
  keyword : SourceToken × Fixity
  prec : SourceToken × Int
  operator : FixityOp
  deriving Repr, BEq

inductive Role
  | Nominal
  | Representational
  | Phantom
  deriving Repr, BEq, Ord

inductive Declaration (e : Type)
  | Data : DataHead e → Option (SourceToken × (Separated (DataCtor e))) → Declaration e
  | Type_ : DataHead e → SourceToken → Type_ e → Declaration e
  | Newtype : DataHead e → SourceToken → Name Proper → Type_ e → Declaration e
  | Class : ClassHead e → Option (SourceToken × NonEmptyArray (Labeled (Name Ident) (Type_ e))) → Declaration e
  | InstanceChain : Separated (Instance e) → Declaration e
  | Derive : SourceToken → Option SourceToken → InstanceHead e → Declaration e
  | KindSignature : SourceToken → Labeled (Name Proper) (Type_ e) → Declaration e
  | Signature : Labeled (Name Ident) (Type_ e) → Declaration e
  | Value : ValueBindingFields e → Declaration e
  | Fixity : FixityFields → Declaration e
  | Foreign : SourceToken → SourceToken → Foreign e → Declaration e
  | Role : SourceToken → SourceToken → Name Proper → NonEmptyArray (SourceToken × Role) → Declaration e
  | Error : e → Declaration e
  deriving Repr, BEq

-----------------------------------------------------------------------------------------------------------

inductive Import (e : Type)
  | Value : Name Ident → Import e
  | Op : Name Operator → Import e
  | Type_ : Name Proper → Option DataMembers → Import e
  | TypeOp : SourceToken → Name Operator → Import e
  | Class : SourceToken → Name Proper → Import e
  | Error : e → Import e
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

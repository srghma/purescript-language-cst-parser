import PurescriptLanguageCstParser.PureScript.CST.Types
import NonEmpty.CorrectByConstruction.Array

open PureScript.CST.Types
open NonEmpty.CorrectByConstruction.Array

namespace PureScript.CST.Traversal

section
variable {F : Type → Type} [Monad F]

def traverseWrapped {α β : Type} (f : α → F β) (w : Wrapped α) : F (Wrapped β) := do
  let value' ← f w.value
  pure { w with value := value' }

def traverseSeparated {α β : Type} (f : α → F β) (s : Separated α) : F (Separated β) := do
  let head' ← f s.head
  let tail' ← s.tail.mapM (fun (tok, val) => do let val' ← f val; pure (tok, val'))
  pure { head := head', tail := tail' }

def traverseLabeled {α β γ : Type} (f : β → F γ) (l : Labeled α β) : F (Labeled α γ) := do
  let value' ← f l.value
  pure { l with value := value' }

def traverseDelimited {α β : Type} (f : α → F β) : Delimited α → F (Delimited β)
  | .mk v => .mk <$> traverseWrapped (Option.mapM (traverseSeparated f)) v

def traverseDelimitedNonEmpty {α β : Type} [Inhabited β] (f : α → F β) : DelimitedNonEmpty α → F (DelimitedNonEmpty β)
  | .mk v => .mk <$> traverseWrapped (traverseSeparated f) v

def traverseNonEmptyArray {α β : Type} [Inhabited β] (f : α → F β) (arr : NonEmptyArray α) : F (NonEmptyArray β) :=
  arr.mapM f

def traverseRecordLabeled {α β : Type} (f : α → F β) : RecordLabeled α → F (RecordLabeled β)
  | .Pun n => pure (.Pun n)
  | .Field l t v => .Field l t <$> f v

structure Visitor (F : Type → Type) [Monad F] (e : Type) where
  onType : Type_ e → F (Type_ e)
  onExpr : Expr e → F (Expr e)
  onBinder : Binder e → F (Binder e)
  onDeclaration : Declaration e → F (Declaration e)

instance [Monad F] [Inhabited (F (Type_ e))] [Inhabited (F (Expr e))] [Inhabited (F (Binder e))] [Inhabited (F (Declaration e))] : Inhabited (Visitor F e) where
  default := {
    onType := fun _ => default,
    onExpr := fun _ => default,
    onBinder := fun _ => default,
    onDeclaration := fun _ => default
  }

mutual
  partial def traverseTypeVarBindingF {expr_e expr_e' : Type} (f : expr_e → F expr_e') (v : TypeVarBindingF (Name Ident) expr_e) : F (TypeVarBindingF (Name Ident) expr_e') :=
    match v with
    | .Kinded w => .Kinded <$> traverseWrapped (traverseLabeled f) w
    | .Name n => pure (.Name n)

  partial def traverseRowF {e expr_e expr_e' : Type} (f : expr_e → F expr_e') (w : RowF e expr_e) : F (RowF e expr_e') := do
    let labels' ← Option.mapM (traverseSeparated (traverseLabeled f)) w.labels
    let tail' ← Option.mapM (fun (tok, val) => do let val' ← f val; pure (tok, val')) w.tail
    pure { labels := labels', tail := tail' }

  partial def traverseTypeF {e expr_e expr_e' : Type} [Inhabited expr_e'] [Inhabited (F (TypeF e expr_e'))] (f : expr_e → F expr_e') (_k : Visitor F e) (v : TypeF e expr_e) : F (TypeF e expr_e') :=
    match v with
    | .Var n => pure (.Var n)
    | .Constructor n => pure (.Constructor n)
    | .Wildcard t => pure (.Wildcard t)
    | .Hole n => pure (.Hole n)
    | .NonEmptyString t v_ => pure (.NonEmptyString t v_)
    | .Int p t v_ => pure (.Int p t v_)
    | .Row w => .Row <$> traverseWrapped (traverseRowF (e := e) f) w
    | .Record w => .Record <$> traverseWrapped (traverseRowF (e := e) f) w
    | .Forall t bs d body => .Forall t <$> bs.mapM (traverseTypeVarBindingF f) <*> pure d <*> f body
    | .Kinded ty t ki => .Kinded <$> f ty <*> pure t <*> f ki
    | .App fn args => .App <$> f fn <*> traverseNonEmptyArray f args
    | .Op first ops => .Op <$> f first <*> traverseNonEmptyArray (fun (n, ty) => do let ty' ← f ty; pure (n, ty')) ops
    | .OpName n => pure (.OpName n)
    | .Arrow dom t cod => .Arrow <$> f dom <*> pure t <*> f cod
    | .ArrowName t => pure (.ArrowName t)
    | .Constrained ty t body => .Constrained <$> f ty <*> pure t <*> f body
    | .Parens w => .Parens <$> traverseWrapped f w
    | .Error d => pure (.Error d)

  partial def traverseType {e : Type} [Inhabited e] [Inhabited (F (Type_ e))] [Inhabited (F (TypeF e (Type_ e)))] (k : Visitor F e) (ty : Type_ e) : F (Type_ e) :=
    match ty with
    | .mk v => .mk <$> traverseTypeF (e := e) (traverseType k) k v
end

partial def traverseDataCtor {e : Type} (k : Visitor F e) (v : DataCtor e) : F (DataCtor e) := do
  let parameters' ← v.parameters.mapM k.onType
  pure { v with parameters := parameters' }

partial def traverseDataHead {e : Type} (k : Visitor F e) (v : DataHead e) : F (DataHead e) := do
  let parameters' ← v.parameters.mapM (traverseTypeVarBindingF (expr_e := Type_ e) (expr_e' := Type_ e) k.onType)
  pure { v with parameters := parameters' }

partial def traverseClassHead {e : Type} [Inhabited (F (Type_ e))] (k : Visitor F e) (v : ClassHead e) : F (ClassHead e) := do
  let typeConstraint' ← Option.mapM (fun (v_, t) => do
    let v' ← match v_ with
      | .One ty => .One <$> k.onType ty
      | .Many d => .Many <$> traverseDelimitedNonEmpty k.onType d
    pure (v', t)) v.typeConstraint
  let parameters' ← v.parameters.mapM (traverseTypeVarBindingF (expr_e := Type_ e) (expr_e' := Type_ e) k.onType)
  pure { v with typeConstraint := typeConstraint', parameters := parameters' }

partial def traverseInstanceHead {e : Type} [Inhabited (F (Type_ e))] (k : Visitor F e) (v : InstanceHead e) : F (InstanceHead e) := do
  let constraints' ← Option.mapM (fun (v_, t) => do
    let v' ← match v_ with
      | .One ty => .One <$> k.onType ty
      | .Many d => .Many <$> traverseDelimitedNonEmpty k.onType d
    pure (v', t)) v.constraints
  let types' ← v.types.mapM k.onType
  pure { v with constraints := constraints', types := types' }

partial def traverseBinderF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (BinderF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : BinderF e expr_e) : F (BinderF e expr_e') :=
  match v with
  | .Wildcard t => pure (.Wildcard t)
  | .Var n => pure (.Var n)
  | .Named n t b => .Named n t <$> f b
  | .Constructor n args => .Constructor n <$> args.mapM f
  | .Boolean t v_ => pure (.Boolean t v_)
  | .Char t v_ => pure (.Char t v_)
  | .NonEmptyString t v_ => pure (.NonEmptyString t v_)
  | .Int p t v_ => pure (.Int p t v_)
  | .Number p t v_ => pure (.Number p t v_)
  | .Array items => .Array <$> traverseDelimited f items
  | .Record fields => .Record <$> traverseDelimited (traverseRecordLabeled f) fields
  | .Parens w => .Parens <$> traverseWrapped f w
  | .Typed b t ty => .Typed <$> f b <*> pure t <*> k.onType ty
  | .Op first ops => .Op <$> f first <*> traverseNonEmptyArray (fun (n, b) => do let b' ← f b; pure (n, b')) ops
  | .Error d => pure (.Error d)

partial def traverseBinder {e : Type} [Inhabited e] [Inhabited (F (Binder e))] [Inhabited (F (BinderF e (Binder e)))] (k : Visitor F e) (b : Binder e) : F (Binder e) :=
  match b with
  | .mk v => .mk <$> traverseBinderF (traverseBinder k) k v

partial def traverseRecordAccessorF {expr_e expr_e' : Type} (f : expr_e → F expr_e') (v : RecordAccessorF expr_e) : F (RecordAccessorF expr_e') := do
  let expr' ← f v.expr
  pure { v with expr := expr' }

partial def traverseLambdaF {e expr_e expr_e' : Type} (f : expr_e → F expr_e') (k : Visitor F e) (v : LambdaF e expr_e) : F (LambdaF e expr_e') := do
  let binders' ← v.binders.mapM k.onBinder
  let body' ← f v.body
  pure { binders := binders', body := body', symbol := v.symbol, arrow := v.arrow }

partial def traverseIfThenElseF {expr_e expr_e' : Type} (f : expr_e → F expr_e') (v : IfThenElseF expr_e) : F (IfThenElseF expr_e') := do
  let cond' ← f v.cond
  let true' ← f v.true_
  let false' ← f v.false_
  pure { cond := cond', true_ := true', false_ := false', keyword := v.keyword, then_ := v.then_, else_ := v.else_ }

partial def traverseAppSpineF {e expr_e expr_e' : Type} (f : expr_e → F expr_e') (k : Visitor F e) (v : AppSpineF e expr_e) : F (AppSpineF e expr_e') :=
  match v with
  | .Term e_ => .Term <$> f e_
  | .Type_ t ty => .Type_ t <$> k.onType ty

mutual
  partial def traverseValueBindingFieldsF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (ValueBindingFieldsF e expr_e'))] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : ValueBindingFieldsF e expr_e) : F (ValueBindingFieldsF e expr_e') := do
    let binders' ← v.binders.mapM k.onBinder
    let guarded' ← traverseGuardedF (e := e) f k v.guarded
    pure { name := v.name, binders := binders', guarded := guarded' }

  partial def traverseGuardedF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : GuardedF e expr_e) : F (GuardedF e expr_e') :=
    match v with
    | .Unconditional t w => .Unconditional t <$> traverseWhereF (e := e) f k w
    | .Guarded bs => .Guarded <$> traverseNonEmptyArray (traverseGuardedExprF (e := e) f k) bs

  partial def traverseGuardedExprF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : GuardedExprF e expr_e) : F (GuardedExprF e expr_e') := do
    let patterns' ← traverseSeparated (traversePatternGuardF (e := e) f k) v.patterns
    let where' ← traverseWhereF (e := e) f k v.where_
    pure { bar := v.bar, patterns := patterns', separator := v.separator, where_ := where' }

  partial def traversePatternGuardF {e expr_e expr_e' : Type} (f : expr_e → F expr_e') (k : Visitor F e) (v : PatternGuardF e expr_e) : F (PatternGuardF e expr_e') := do
    let binder' ← Option.mapM (fun (b, t) => do let b' ← k.onBinder b; pure (b', t)) v.binder
    let expr' ← f v.expr
    pure { binder := binder', expr := expr' }

  partial def traverseWhereF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (WhereF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : WhereF e expr_e) : F (WhereF e expr_e') := do
    let expr' ← f v.expr
    let bindings' ← v.bindings.mapM (fun (tok, bs) => do let bs' ← traverseNonEmptyArray (traverseLetBindingF (e := e) f k) bs; pure (tok, bs'))
    pure { expr := expr', bindings := bindings' }

  partial def traverseLetBindingF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (LetBindingF e expr_e'))] [Inhabited (F (ValueBindingFieldsF e expr_e'))] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : LetBindingF e expr_e) : F (LetBindingF e expr_e') :=
    match v with
    | .Signature l => .Signature <$> traverseLabeled k.onType l
    | .Name fields => .Name <$> traverseValueBindingFieldsF (e := e) f k fields
    | .Pattern b t w => .Pattern <$> k.onBinder b <*> pure t <*> traverseWhereF (e := e) f k w
    | .Error d => pure (.Error d)
end

partial def traverseRecordUpdateF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (RecordUpdateF e expr_e'))] (f : expr_e → F expr_e') (v : RecordUpdateF e expr_e) : F (RecordUpdateF e expr_e') :=
  match v with
  | .Leaf l t e_ => .Leaf l t <$> f e_
  | .Branch l u => .Branch l <$> traverseDelimitedNonEmpty (traverseRecordUpdateF (e := e) f) u

partial def traverseCaseOfF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (CaseOfF e expr_e'))] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] [Inhabited (F (ValueBindingFieldsF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : CaseOfF e expr_e) : F (CaseOfF e expr_e') := do
  let head' ← traverseSeparated f v.head
  let branches' ← traverseNonEmptyArray (fun (b, g) => do
    let b' ← traverseSeparated k.onBinder b
    let g' ← traverseGuardedF (e := e) f k g
    pure (b', g')) v.branches
  pure { keyword := v.keyword, head := head', of := v.of, branches := branches' }

partial def traverseLetInF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (LetInF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] [Inhabited (F (ValueBindingFieldsF e expr_e'))] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : LetInF e expr_e) : F (LetInF e expr_e') := do
  let bindings' ← traverseNonEmptyArray (traverseLetBindingF (e := e) f k) v.bindings
  let body' ← f v.body
  pure { keyword := v.keyword, bindings := bindings', in_ := v.in_, body := body' }

partial def traverseDoStatementF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (DoStatementF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] [Inhabited (F (ValueBindingFieldsF e expr_e'))] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : DoStatementF e expr_e) : F (DoStatementF e expr_e') :=
  match v with
  | .Let t bs => .Let t <$> traverseNonEmptyArray (traverseLetBindingF (e := e) f k) bs
  | .Discard e_ => .Discard <$> f e_
  | .Bind b t e_ => .Bind <$> k.onBinder b <*> pure t <*> f e_
  | .Error d => pure (.Error d)

partial def traverseDoBlockF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (DoBlockF e expr_e'))] [Inhabited (F (DoStatementF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] [Inhabited (F (ValueBindingFieldsF e expr_e'))] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : DoBlockF e expr_e) : F (DoBlockF e expr_e') := do
  let statements' ← traverseNonEmptyArray (traverseDoStatementF (e := e) f k) v.statements
  pure { keyword := v.keyword, statements := statements' }

partial def traverseAdoBlockF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (AdoBlockF e expr_e'))] [Inhabited (F (DoStatementF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] [Inhabited (F (ValueBindingFieldsF e expr_e'))] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : AdoBlockF e expr_e) : F (AdoBlockF e expr_e') := do
  let statements' ← v.statements.mapM (traverseDoStatementF (e := e) f k)
  let result' ← f v.result
  pure { keyword := v.keyword, statements := statements', in_ := v.in_, result := result' }

partial def traverseExprF {e expr_e expr_e' : Type} [Inhabited e] [Inhabited expr_e'] [Inhabited (F (ExprF e expr_e'))] [Inhabited (F (RecordUpdateF e expr_e'))] [Inhabited (F (CaseOfF e expr_e'))] [Inhabited (F (LetInF e expr_e'))] [Inhabited (F (DoBlockF e expr_e'))] [Inhabited (F (AdoBlockF e expr_e'))] [Inhabited (F (LetBindingF e expr_e'))] [Inhabited (F (ValueBindingFieldsF e expr_e'))] [Inhabited (F (GuardedF e expr_e'))] [Inhabited (F (GuardedExprF e expr_e'))] [Inhabited (F (WhereF e expr_e'))] [Inhabited (F (DoStatementF e expr_e'))] (f : expr_e → F expr_e') (k : Visitor F e) (v : ExprF e expr_e) : F (ExprF e expr_e') :=
  match v with
  | .Hole n => pure (.Hole n)
  | .Section t => pure (.Section t)
  | .Ident n => pure (.Ident n)
  | .Constructor n => pure (.Constructor n)
  | .Boolean t v_ => pure (.Boolean t v_)
  | .Char t v_ => pure (.Char t v_)
  | .NonEmptyString t v_ => pure (.NonEmptyString t v_)
  | .Int t v_ => pure (.Int t v_)
  | .Number t v_ => pure (.Number t v_)
  | .Array items => .Array <$> traverseDelimited f items
  | .Record fields => .Record <$> traverseDelimited (traverseRecordLabeled f) fields
  | .Parens w => .Parens <$> traverseWrapped f w
  | .Typed e_ t ty => .Typed <$> f e_ <*> pure t <*> k.onType ty
  | .Infix head tail => .Infix <$> f head <*> traverseNonEmptyArray (fun (w, e_) => do let e' ← f e_; pure (w, e')) tail
  | .Op head ops => .Op <$> f head <*> traverseNonEmptyArray (fun (n, e_) => do let e' ← f e_; pure (n, e')) ops
  | .OpName n => pure (.OpName n)
  | .Negate t e_ => .Negate t <$> f e_
  | .RecordAccessor d => .RecordAccessor <$> traverseRecordAccessorF f d
  | .RecordUpdate e_ u => .RecordUpdate <$> f e_ <*> traverseWrapped (traverseSeparated (traverseRecordUpdateF (e := e) f)) u
  | .App fn args => .App <$> f fn <*> traverseNonEmptyArray (traverseAppSpineF (e := e) f k) args
  | .Lambda d => .Lambda <$> traverseLambdaF (e := e) f k d
  | .If d => .If <$> traverseIfThenElseF f d
  | .Case d => .Case <$> traverseCaseOfF (e := e) f k d
  | .Let d => .Let <$> traverseLetInF (e := e) f k d
  | .Do d => .Do <$> traverseDoBlockF (e := e) f k d
  | .Ado d => .Ado <$> traverseAdoBlockF (e := e) f k d
  | .Error d => pure (.Error d)

partial def traverseExpr {e : Type} [Inhabited e] [Inhabited (F (Expr e))] [Inhabited (F (ExprF e (Expr e)))] [Inhabited (F (RecordUpdateF e (Expr e)))] [Inhabited (F (CaseOfF e (Expr e)))] [Inhabited (F (LetInF e (Expr e)))] [Inhabited (F (DoBlockF e (Expr e)))] [Inhabited (F (AdoBlockF e (Expr e)))] [Inhabited (F (LetBindingF e (Expr e)))] [Inhabited (F (ValueBindingFieldsF e (Expr e)))] [Inhabited (F (GuardedF e (Expr e)))] [Inhabited (F (GuardedExprF e (Expr e)))] [Inhabited (F (WhereF e (Expr e)))] [Inhabited (F (DoStatementF e (Expr e)))] (k : Visitor F e) (e_ : Expr e) : F (Expr e) :=
  match e_ with
  | .mk v => .mk <$> traverseExprF (traverseExpr k) k v

partial def traverseInstanceBinding {e : Type} [Inhabited e] [Inhabited (F (Expr e))] [Inhabited (F (ExprF e (Expr e)))] [Inhabited (F (RecordUpdateF e (Expr e)))] [Inhabited (F (CaseOfF e (Expr e)))] [Inhabited (F (LetInF e (Expr e)))] [Inhabited (F (DoBlockF e (Expr e)))] [Inhabited (F (AdoBlockF e (Expr e)))] [Inhabited (F (LetBindingF e (Expr e)))] [Inhabited (F (ValueBindingFieldsF e (Expr e)))] [Inhabited (F (GuardedF e (Expr e)))] [Inhabited (F (GuardedExprF e (Expr e)))] [Inhabited (F (WhereF e (Expr e)))] [Inhabited (F (DoStatementF e (Expr e)))] (k : Visitor F e) (b : InstanceBinding e) : F (InstanceBinding e) :=
  match b with
  | .Signature l => .Signature <$> traverseLabeled k.onType l
  | .Name fields => .Name <$> traverseValueBindingFieldsF (e := e) (traverseExpr k) k fields

partial def traverseInstance {e : Type} [Inhabited e] [Inhabited (F (Expr e))] [Inhabited (F (ExprF e (Expr e)))] [Inhabited (F (RecordUpdateF e (Expr e)))] [Inhabited (F (CaseOfF e (Expr e)))] [Inhabited (F (LetInF e (Expr e)))] [Inhabited (F (DoBlockF e (Expr e)))] [Inhabited (F (AdoBlockF e (Expr e)))] [Inhabited (F (LetBindingF e (Expr e)))] [Inhabited (F (ValueBindingFieldsF e (Expr e)))] [Inhabited (F (GuardedF e (Expr e)))] [Inhabited (F (GuardedExprF e (Expr e)))] [Inhabited (F (WhereF e (Expr e)))] [Inhabited (F (DoStatementF e (Expr e)))] (k : Visitor F e) (v : Instance e) : F (Instance e) := do
  let head' ← traverseInstanceHead k v.head
  let body' ← Option.mapM (fun (tok, n) => do
    let n' ← Option.mapM (traverseNonEmptyArray (traverseInstanceBinding k)) n
    pure (tok, n')) v.body
  pure { head := head', body := body' }

partial def traverseDeclaration {e : Type} [Inhabited e] [Inhabited (F (Expr e))] [Inhabited (F (ExprF e (Expr e)))] [Inhabited (F (RecordUpdateF e (Expr e)))] [Inhabited (F (CaseOfF e (Expr e)))] [Inhabited (F (LetInF e (Expr e)))] [Inhabited (F (DoBlockF e (Expr e)))] [Inhabited (F (AdoBlockF e (Expr e)))] [Inhabited (F (LetBindingF e (Expr e)))] [Inhabited (F (ValueBindingFieldsF e (Expr e)))] [Inhabited (F (GuardedF e (Expr e)))] [Inhabited (F (GuardedExprF e (Expr e)))] [Inhabited (F (WhereF e (Expr e)))] [Inhabited (F (DoStatementF e (Expr e)))] (k : Visitor F e) (d : Declaration e) : F (Declaration e) :=
  match d with
  | .Data h s => .Data <$> traverseDataHead k h <*> Option.mapM (fun (tok, ctors) => do let ctors' ← traverseSeparated (traverseDataCtor k) ctors; pure (tok, ctors')) s
  | .Type_ h t ty => .Type_ <$> traverseDataHead k h <*> pure t <*> k.onType ty
  | .Newtype h t n ty => .Newtype <$> traverseDataHead k h <*> pure t <*> pure n <*> k.onType ty
  | .Class h b => .Class <$> traverseClassHead k h <*> Option.mapM (fun (tok, fields) => do let fields' ← fields.mapM (traverseLabeled k.onType); pure (tok, fields')) b
  | .InstanceChain is => .InstanceChain <$> traverseSeparated (traverseInstance k) is
  | .Derive k_ t h => .Derive k_ t <$> traverseInstanceHead k h
  | .KindSignature k_ l => .KindSignature k_ <$> traverseLabeled k.onType l
  | .Signature l => .Signature <$> traverseLabeled k.onType l
  | .Value fields => .Value <$> traverseValueBindingFieldsF (e := e) (traverseExpr k) k fields
  | .Fixity f => pure (.Fixity f)
  | .Foreign t1 t2 f => .Foreign t1 t2 <$> (match f with
      | .Value l => .Value <$> traverseLabeled k.onType l
      | .Data k_ l => .Data k_ <$> traverseLabeled k.onType l
      | .Kind k_ n => pure (.Kind k_ n))
  | .Role t1 t2 n rs => pure (.Role t1 t2 n rs)
  | .Error d => pure (.Error d)

partial def bottomUpVisitor [Inhabited e] [Inhabited (F (Type_ e))] [Inhabited (F (Expr e))] [Inhabited (F (Binder e))] [Inhabited (F (Declaration e))] [Inhabited (F (TypeF e (Type_ e)))] [Inhabited (F (ExprF e (Expr e)))] [Inhabited (F (BinderF e (Binder e)))] [Inhabited (F (RecordUpdateF e (Expr e)))] [Inhabited (F (CaseOfF e (Expr e)))] [Inhabited (F (LetInF e (Expr e)))] [Inhabited (F (DoBlockF e (Expr e)))] [Inhabited (F (AdoBlockF e (Expr e)))] [Inhabited (F (LetBindingF e (Expr e)))] [Inhabited (F (ValueBindingFieldsF e (Expr e)))] [Inhabited (F (GuardedF e (Expr e)))] [Inhabited (F (GuardedExprF e (Expr e)))] [Inhabited (F (WhereF e (Expr e)))] [Inhabited (F (DoStatementF e (Expr e)))] (fType : Type_ e → F (Type_ e)) (fExpr : Expr e → F (Expr e)) (fBinder : Binder e → F (Binder e)) (fDecl : Declaration e → F (Declaration e)) : Visitor F e where
  onType ty := do
    let ty' ← match ty with | .mk v => .mk <$> traverseTypeF (e := e) (bottomUpVisitor fType fExpr fBinder fDecl).onType (bottomUpVisitor fType fExpr fBinder fDecl) v
    fType ty'
  onExpr e_ := do
    let e' ← match e_ with | .mk v => .mk <$> traverseExprF (e := e) (bottomUpVisitor fType fExpr fBinder fDecl).onExpr (bottomUpVisitor fType fExpr fBinder fDecl) v
    fExpr e'
  onBinder b := do
    let b' ← match b with | .mk v => .mk <$> traverseBinderF (e := e) (bottomUpVisitor fType fExpr fBinder fDecl).onBinder (bottomUpVisitor fType fExpr fBinder fDecl) v
    fBinder b'
  onDeclaration d := do
    let d' ← traverseDeclaration (bottomUpVisitor fType fExpr fBinder fDecl) d
    fDecl d'

partial def topDownVisitor [Inhabited e] [Inhabited (F (Type_ e))] [Inhabited (F (Expr e))] [Inhabited (F (Binder e))] [Inhabited (F (Declaration e))] [Inhabited (F (TypeF e (Type_ e)))] [Inhabited (F (ExprF e (Expr e)))] [Inhabited (F (BinderF e (Binder e)))] [Inhabited (F (RecordUpdateF e (Expr e)))] [Inhabited (F (CaseOfF e (Expr e)))] [Inhabited (F (LetInF e (Expr e)))] [Inhabited (F (DoBlockF e (Expr e)))] [Inhabited (F (AdoBlockF e (Expr e)))] [Inhabited (F (LetBindingF e (Expr e)))] [Inhabited (F (ValueBindingFieldsF e (Expr e)))] [Inhabited (F (GuardedF e (Expr e)))] [Inhabited (F (GuardedExprF e (Expr e)))] [Inhabited (F (WhereF e (Expr e)))] [Inhabited (F (DoStatementF e (Expr e)))] (fType : Type_ e → F (Type_ e)) (fExpr : Expr e → F (Expr e)) (fBinder : Binder e → F (Binder e)) (fDecl : Declaration e → F (Declaration e)) : Visitor F e where
  onType ty := do
    let ty' ← fType ty
    match ty' with | .mk v => .mk <$> traverseTypeF (e := e) (topDownVisitor fType fExpr fBinder fDecl).onType (topDownVisitor fType fExpr fBinder fDecl) v
  onExpr e_ := do
    let e' ← fExpr e_
    match e' with | .mk v => .mk <$> traverseExprF (e := e) (topDownVisitor fType fExpr fBinder fDecl).onExpr (topDownVisitor fType fExpr fBinder fDecl) v
  onBinder b := do
    let b' ← fBinder b
    match b' with | .mk v => .mk <$> traverseBinderF (e := e) (topDownVisitor fType fExpr fBinder fDecl).onBinder (topDownVisitor fType fExpr fBinder fDecl) v
  onDeclaration d := do
    let d' ← fDecl d
    traverseDeclaration (topDownVisitor fType fExpr fBinder fDecl) d'
end

end PureScript.CST.Traversal

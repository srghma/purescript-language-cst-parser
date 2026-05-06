module
import PurescriptLanguageCstParser.PureScript.CST.Types
import NonEmpty.CorrectByConstruction.Array

open NonEmpty.CorrectByConstruction.Array
open PureScript.CST.Types

namespace PureScript.CST.Traversal

--------------------------------------------------------------------
-- Rewrite type aliases (matching PureScript)
--------------------------------------------------------------------

abbrev Rewrite (e : Type) (f g : Type → Type) :=
  g e → f (g e)

abbrev RewriteWithContext (c e : Type) (f g : Type → Type) :=
  c → g e → f (c × g e)

abbrev MonoidalRewrite (e m : Type) (g : Type → Type) :=
  g e → m

abbrev PureRewrite (e : Type) (g : Type → Type) :=
  g e → g e

abbrev PureRewriteWithContext (c e : Type) (g : Type → Type) :=
  c → g e → c × g e

--------------------------------------------------------------------
-- Visitor record
--------------------------------------------------------------------

structure Visitor (e : Type) (f : Type → Type) where
  onBinder : Binder e → f (Binder e)
  onExpr   : Expr e   → f (Expr e)
  onType   : Type_ e  → f (Type_ e)
  onDecl   : Declaration e → f (Declaration e)

def defaultVisitorM [Applicative f] : Visitor e f :=
  { onBinder := pure, onExpr := pure, onType := pure, onDecl := pure }

def defaultVisitor : Visitor e id :=
  { onBinder := id, onExpr := id, onType := id, onDecl := id }

--------------------------------------------------------------------
-- Stateless helpers
--------------------------------------------------------------------

def traverseWrapped [Applicative f] (k : α → f α) (w : Wrapped α) : f (Wrapped α) :=
  (fun v => { w with value := v }) <$> k w.value

def traverseSeparated [Monad m] (k : α → m α) (s : Separated α) : m (Separated α) :=
  (fun head tail => { head, tail })
    <$> k s.head
    <*> s.tail.mapM (fun (tok, a) => (tok, ·) <$> k a)

def traverseDelimited [Monad f] (k : α → f α) : Delimited α → f (Delimited α)
  | .mk w => .mk <$> traverseWrapped (fun opt => opt.mapM (traverseSeparated k)) w

def traverseDelimitedNonEmpty [Monad f] (k : α → f α)
    : DelimitedNonEmpty α → f (DelimitedNonEmpty α)
  | .mk w => .mk <$> traverseWrapped (traverseSeparated k) w

def traverseLabeled [Applicative f] (k : β → f β) (l : Labeled α β) : f (Labeled α β) :=
  (fun v => { l with value := v }) <$> k l.value

def traverseRecordLabeled [Applicative f] (k : α → f α) : RecordLabeled α → f (RecordLabeled α)
  | .Pun n          => pure (.Pun n)
  | .Field l sep v  => .Field l sep <$> k v

def traverseOneOrDelimited [Monad f] (k : α → f α) : OneOrDelimited α → f (OneOrDelimited α)
  | .One a   => .One <$> k a
  | .Many m  => .Many <$> traverseDelimitedNonEmpty k m

--------------------------------------------------------------------
-- Type traversal
--------------------------------------------------------------------

section TypeTraversal
variable {e : Type} {f : Type → Type} [Applicative f]

def traverseRowF (k : Visitor e f) (r : RowF e (Type_ e)) : f (RowF e (Type_ e)) :=
  (fun labels tail => { labels, tail })
    <$> r.labels.mapM (traverseSeparated (traverseLabeled k.onType))
    <*> r.tail.mapM (fun (tok, t) => (tok, ·) <$> k.onType t)

def traverseTypeVarBindingF (k : Visitor e f) {a : Type}
    : TypeVarBindingF a (Type_ e) → f (TypeVarBindingF a (Type_ e))
  | .Kinded w => .Kinded <$> traverseWrapped (traverseLabeled k.onType) w
  | .Name n   => pure (.Name n)

def traverseType (k : Visitor e f) : Type_ e → f (Type_ e)
  | .mk t => .mk <$> go t
  where
    go : TypeF e (Type_ e) → f (TypeF e (Type_ e))
      | .Row w          => .Row    <$> traverseWrapped (traverseRowF k) w
      | .Record w       => .Record <$> traverseWrapped (traverseRowF k) w
      | .Forall o bs c body =>
            .Forall o
              <$> bs.mapM (traverseTypeVarBindingF k)
              <*> pure c
              <*> k.onType body
      | .Kinded t1 sep t2   => .Kinded <$> k.onType t1 <*> pure sep <*> k.onType t2
      | .App t args         => .App    <$> k.onType t  <*> args.mapM k.onType
      | .Op t ops           => .Op     <$> k.onType t
                                       <*> ops.mapM (fun (op, t2) => (op, ·) <$> k.onType t2)
      | .Arrow t1 tok t2    => .Arrow  <$> k.onType t1 <*> pure tok <*> k.onType t2
      | .Constrained t1 tok t2 => .Constrained <$> k.onType t1 <*> pure tok <*> k.onType t2
      | .Parens w           => .Parens <$> traverseWrapped k.onType w
      | t                   => pure t

end TypeTraversal

--------------------------------------------------------------------
-- Binder traversal
--------------------------------------------------------------------

section BinderTraversal
variable {e : Type} {f : Type → Type} [Applicative f]

def traverseRecordUpdateF (k : Visitor e f)
    : RecordUpdateF e (Expr e) → f (RecordUpdateF e (Expr e))
  | .Leaf l tok ex  => .Leaf l tok <$> k.onExpr ex
  | .Branch l upds  => .Branch l   <$> traverseDelimitedNonEmpty (traverseRecordUpdateF k) upds

def traverseBinder (k : Visitor e f) : Binder e → f (Binder e)
  | .mk b => .mk <$> go b
  where
    go : BinderF e (Binder e) → f (BinderF e (Binder e))
      | .Named n tok b    => .Named n tok <$> k.onBinder b
      | .Constructor n bs => .Constructor n <$> bs.mapM k.onBinder
      | .Array items      => .Array  <$> traverseDelimited k.onBinder items
      | .Record fields    => .Record <$> traverseDelimited (traverseRecordLabeled k.onBinder) fields
      | .Parens w         => .Parens <$> traverseWrapped k.onBinder w
      | .Typed b tok t    => .Typed  <$> k.onBinder b <*> pure tok <*> k.onType t
      | .Op first ops     => .Op     <$> k.onBinder first
                                     <*> ops.mapM (fun (op, b) => (op, ·) <$> k.onBinder b)
      | b                 => pure b

end BinderTraversal

--------------------------------------------------------------------
-- Mutually recursive: Expr / LetBinding / Where / Guarded / VBF
--------------------------------------------------------------------

section ExprTraversal
variable {e : Type} {f : Type → Type} [Applicative f]

def traversePatternGuardF (k : Visitor e f)
    (pg : PatternGuardF e (Expr e)) : f (PatternGuardF e (Expr e)) :=
  (fun binder expr => { binder, expr })
    <$> pg.binder.mapM (fun (b, tok) => (·, tok) <$> k.onBinder b)
    <*> k.onExpr pg.expr

def traverseAppSpineF (k : Visitor e f)
    : AppSpineF e (Expr e) → f (AppSpineF e (Expr e))
  | .Type_ tok t => .Type_ tok <$> k.onType t
  | .Term ex     => .Term      <$> k.onExpr ex

def traverseLambdaF (k : Visitor e f) (l : LambdaF e (Expr e)) : f (LambdaF e (Expr e)) :=
  (fun binders body => { l with binders, body })
    <$> l.binders.mapM k.onBinder
    <*> k.onExpr l.body

def traverseIfThenElseF (k : Visitor e f) (i : IfThenElseF (Expr e)) : f (IfThenElseF (Expr e)) :=
  (fun cond true_ false_ => { i with cond, true_, false_ })
    <$> k.onExpr i.cond
    <*> k.onExpr i.true_
    <*> k.onExpr i.false_

def traverseRecordAccessorF (k : Visitor e f)
    (ra : RecordAccessorF (Expr e)) : f (RecordAccessorF (Expr e)) :=
  (fun expr => { ra with expr }) <$> k.onExpr ra.expr

mutual

  -- Expr
  def traverseExpr (k : Visitor e f) : Expr e → f (Expr e)
    | .mk ex => .mk <$> traverseExprF k ex

  def traverseExprF (k : Visitor e f)
      : ExprF e (Expr e) (DoBlockRecursive e) (AdoBlockRecursive e)
               (LetBindingRecursive e) (GuardedRecursive e)
      → f (ExprF e (Expr e) (DoBlockRecursive e) (AdoBlockRecursive e)
                   (LetBindingRecursive e) (GuardedRecursive e))
    | .Array items      => .Array  <$> traverseDelimited k.onExpr items
    | .Record fields    => .Record <$> traverseDelimited (traverseRecordLabeled k.onExpr) fields
    | .Parens w         => .Parens <$> traverseWrapped k.onExpr w
    | .Typed ex tok t   => .Typed  <$> k.onExpr ex <*> pure tok <*> k.onType t
    | .Infix head tail  =>
        .Infix <$> k.onExpr head
               <*> tail.mapM (fun (w, ex) => (·, ·) <$> traverseWrapped k.onExpr w <*> k.onExpr ex)
    | .Op head ops      =>
        .Op <$> k.onExpr head
            <*> ops.mapM (fun (op, ex) => (op, ·) <$> k.onExpr ex)
    | .Negate tok ex    => .Negate tok <$> k.onExpr ex
    | .RecordAccessor ra =>
        .RecordAccessor <$> traverseRecordAccessorF k ra
    | .RecordUpdate ex upds =>
        .RecordUpdate <$> k.onExpr ex
                      <*> traverseDelimitedNonEmpty (traverseRecordUpdateF k) upds
    | .App fn args      =>
        .App <$> k.onExpr fn <*> args.mapM (traverseAppSpineF k)
    | .Lambda l         => .Lambda <$> traverseLambdaF k l
    | .If i             => .If     <$> traverseIfThenElseF k i
    | .Case c           => .Case   <$> traverseCaseOfF k c
    | .Let l            => .Let    <$> traverseLetInF k l
    | .Do db            => .Do     <$> traverseDoBlockRecursive k db
    | .Ado ab           => .Ado    <$> traverseAdoBlockRecursive k ab
    | ex                => pure ex

  -- CaseOf
  def traverseCaseOfF (k : Visitor e f) (c : CaseOfF e (Expr e) (GuardedRecursive e))
      : f (CaseOfF e (Expr e) (GuardedRecursive e)) :=
    (fun head branches => { c with head, branches })
      <$> traverseSeparated k.onExpr c.head
      <*> c.branches.mapM (fun (binders, guarded) =>
            (·, ·) <$> traverseSeparated k.onBinder binders
                   <*> traverseGuarded k guarded)

  -- LetIn
  def traverseLetInF (k : Visitor e f) (l : LetInF e (Expr e) (LetBindingRecursive e))
      : f (LetInF e (Expr e) (LetBindingRecursive e)) :=
    (fun bindings body => { l with bindings, body })
      <$> l.bindings.mapM (traverseLetBinding k)
      <*> k.onExpr l.body

  -- LetBinding
  def traverseLetBinding (k : Visitor e f) : LetBindingRecursive e → f (LetBindingRecursive e)
    | .mk lb => .mk <$> traverseLetBindingF k lb

  def traverseLetBindingF (k : Visitor e f)
      : LetBindingF e (Expr e) (ValueBindingFieldsRecursive e) (WhereRecursive e)
      → f (LetBindingF e (Expr e) (ValueBindingFieldsRecursive e) (WhereRecursive e))
    | .Signature sig        => .Signature <$> traverseLabeled k.onType sig
    | .Name fields          => .Name      <$> traverseValueBindingFields k fields
    | .Pattern b tok w      => .Pattern   <$> k.onBinder b <*> pure tok <*> traverseWhere k w
    | .Error err            => pure (.Error err)

  -- Where
  def traverseWhere (k : Visitor e f) : WhereRecursive e → f (WhereRecursive e)
    | .mk w => .mk <$> traverseWhereF k w

  def traverseWhereF (k : Visitor e f) (w : WhereF e (Expr e) (LetBindingRecursive e))
      : f (WhereF e (Expr e) (LetBindingRecursive e)) :=
    (fun expr bindings => { expr, bindings })
      <$> k.onExpr w.expr
      <*> w.bindings.mapM (fun (tok, lbs) => (tok, ·) <$> lbs.mapM (traverseLetBinding k))

  -- Guarded
  def traverseGuarded (k : Visitor e f) : GuardedRecursive e → f (GuardedRecursive e)
    | .mk g => .mk <$> traverseGuardedF k g

  def traverseGuardedF (k : Visitor e f)
      : GuardedF e (Expr e) (WhereRecursive e) (GuardedRecursive e)
      → f (GuardedF e (Expr e) (WhereRecursive e) (GuardedRecursive e))
    | .Unconditional tok w  => .Unconditional tok <$> traverseWhere k w
    | .Guarded branches     => .Guarded <$> branches.mapM (traverseGuardedExprF k)

  def traverseGuardedExprF (k : Visitor e f) (ge : GuardedExprF e (Expr e) (WhereRecursive e))
      : f (GuardedExprF e (Expr e) (WhereRecursive e)) :=
    (fun patterns where_ => { ge with patterns, where_ })
      <$> traverseSeparated (traversePatternGuardF k) ge.patterns
      <*> traverseWhere k ge.where_

  -- ValueBindingFields
  def traverseValueBindingFields (k : Visitor e f)
      : ValueBindingFieldsRecursive e → f (ValueBindingFieldsRecursive e)
    | .mk vbf => .mk <$> traverseValueBindingFieldsF k vbf

  def traverseValueBindingFieldsF (k : Visitor e f)
      (vbf : ValueBindingFieldsF e (Expr e) (GuardedRecursive e))
      : f (ValueBindingFieldsF e (Expr e) (GuardedRecursive e)) :=
    (fun binders guarded => { vbf with binders, guarded })
      <$> vbf.binders.mapM k.onBinder
      <*> traverseGuarded k vbf.guarded

  -- DoBlock / AdoBlock
  -- Note: DoStatementR = DoStatementF e (Expr e) (LetBindingRecursive e)
  def traverseDoStatement (k : Visitor e f) : DoStatementR e → f (DoStatementR e)
    | .Let tok lbs   => .Let tok <$> lbs.mapM (traverseLetBinding k)
    | .Discard ex    => .Discard  <$> k.onExpr ex
    | .Bind b tok ex => .Bind    <$> k.onBinder b <*> pure tok <*> k.onExpr ex
    | .Error err     => pure (.Error err)

  def traverseDoBlockRecursive (k : Visitor e f) : DoBlockRecursive e → f (DoBlockRecursive e)
    | .mk db => .mk <$>
        (fun statements => { db with statements })
          <$> db.statements.mapM (traverseDoStatement k)

  def traverseAdoBlockRecursive (k : Visitor e f) : AdoBlockRecursive e → f (AdoBlockRecursive e)
    | .mk ab => .mk <$>
        (fun statements result => { ab with statements, result })
          <$> ab.statements.mapM (traverseDoStatement k)
          <*> k.onExpr ab.result

end

end ExprTraversal

--------------------------------------------------------------------
-- Declaration / module traversal
--------------------------------------------------------------------

section DeclTraversal
variable {e : Type} {f : Type → Type} [Applicative f]

def traverseInstanceHead (k : Visitor e f) (ih : InstanceHead e) : f (InstanceHead e) :=
  (fun constraints types => { ih with constraints, types })
    <$> ih.constraints.mapM (fun (c, tok) => (·, tok) <$> traverseOneOrDelimited k.onType c)
    <*> ih.types.mapM k.onType

def traverseInstanceBinding (k : Visitor e f) : InstanceBinding e → f (InstanceBinding e)
  | .Signature sig  => .Signature <$> traverseLabeled k.onType sig
  | .Name fields    => .Name      <$> traverseValueBindingFields k fields

def traverseInstance (k : Visitor e f) (inst : Instance e) : f (Instance e) :=
  (fun head body => { head, body })
    <$> traverseInstanceHead k inst.head
    <*> inst.body.mapM (fun (tok, lbs) =>
          (tok, ·) <$> lbs.mapM (traverseInstanceBinding k))

def traverseClassHead (k : Visitor e f) (ch : ClassHead e) : f (ClassHead e) :=
  (fun typeConstraint parameters => { ch with typeConstraint, parameters })
    <$> ch.typeConstraint.mapM (fun (c, tok) =>
          (·, tok) <$> traverseOneOrDelimited k.onType c)
    <*> ch.parameters.mapM (traverseTypeVarBindingF k)

def traverseDataHead (k : Visitor e f) (dh : DataHead e) : f (DataHead e) :=
  (fun parameters => { dh with parameters })
    <$> dh.parameters.mapM (traverseTypeVarBindingF k)

def traverseDataCtor (k : Visitor e f) (dc : DataCtor e) : f (DataCtor e) :=
  (fun parameters => { dc with parameters })
    <$> dc.parameters.mapM k.onType

def traverseForeign (k : Visitor e f) : Foreign e → f (Foreign e)
  | .Value l       => .Value <$> traverseLabeled k.onType l
  | .Data tok l    => .Data tok <$> traverseLabeled k.onType l
  | .Kind tok n    => pure (.Kind tok n)

def traverseDecl (k : Visitor e f) : Declaration e → f (Declaration e)
  | .Data dh ctors =>
      .Data <$> traverseDataHead k dh
            <*> ctors.mapM (fun (tok, sep) =>
                  (tok, ·) <$> traverseSeparated (traverseDataCtor k) sep)
  | .Type_ dh tok t =>
      .Type_ <$> traverseDataHead k dh <*> pure tok <*> k.onType t
  | .Newtype dh tok n t =>
      .Newtype <$> traverseDataHead k dh <*> pure tok <*> pure n <*> k.onType t
  | .Class ch sigs =>
      .Class <$> traverseClassHead k ch
             <*> sigs.mapM (fun (tok, ls) =>
                   (tok, ·) <$> ls.mapM (traverseLabeled k.onType))
  | .InstanceChain sep =>
      .InstanceChain <$> traverseSeparated (traverseInstance k) sep
  | .Derive tok mbTok ih =>
      .Derive tok mbTok <$> traverseInstanceHead k ih
  | .KindSignature tok l =>
      .KindSignature tok <$> traverseLabeled k.onType l
  | .Signature l =>
      .Signature <$> traverseLabeled k.onType l
  | .Value fields =>
      .Value <$> traverseValueBindingFields k fields
  | .Foreign tok1 tok2 f =>
      .Foreign tok1 tok2 <$> traverseForeign k f
  | decl => pure decl

def traverseModuleBody (k : Visitor e f) (mb : ModuleBody e) : f (ModuleBody e) :=
  (fun decls => { mb with decls })
    <$> mb.decls.mapM k.onDecl

def traverseModule (k : Visitor e f) (m : Module e) : f (Module e) :=
  (fun body => { m with body })
    <$> traverseModuleBody k m.body

end DeclTraversal

--------------------------------------------------------------------
-- Bottom-up and top-down combinators
--------------------------------------------------------------------

section Combinators
variable {e : Type} {m : Type → Type} [Monad m]

def bottomUpTraversal (v : Visitor e m) : Visitor e m :=
  { onBinder := fun a => v.onBinder =<< traverseBinder v' a
  , onExpr   := fun a => v.onExpr   =<< traverseExpr   v' a
  , onType   := fun a => v.onType   =<< traverseType   v' a
  , onDecl   := fun a => v.onDecl   =<< traverseDecl   v' a }
  where v' := bottomUpTraversal v  -- lazy via Monad deferred eval

def topDownTraversal (v : Visitor e m) : Visitor e m :=
  { onBinder := fun a => v.onBinder a >>= traverseBinder v'
  , onExpr   := fun a => v.onExpr   a >>= traverseExpr   v'
  , onType   := fun a => v.onType   a >>= traverseType   v'
  , onDecl   := fun a => v.onDecl   a >>= traverseDecl   v' }
  where v' := topDownTraversal v

-- Concrete rewriters
def rewriteExprBottomUpM  (v : Visitor e m) : Expr e → m (Expr e) :=
  (bottomUpTraversal v).onExpr

def rewriteExprTopDownM   (v : Visitor e m) : Expr e → m (Expr e) :=
  (topDownTraversal v).onExpr

def rewriteDeclBottomUpM  (v : Visitor e m) : Declaration e → m (Declaration e) :=
  (bottomUpTraversal v).onDecl

def rewriteDeclTopDownM   (v : Visitor e m) : Declaration e → m (Declaration e) :=
  (topDownTraversal v).onDecl

def rewriteModuleBottomUpM (v : Visitor e m) : Module e → m (Module e) :=
  traverseModule (bottomUpTraversal v)

def rewriteModuleTopDownM  (v : Visitor e m) : Module e → m (Module e) :=
  traverseModule (topDownTraversal v)

-- Pure (Identity monad) variants
def rewriteExprBottomUp  (v : Visitor e id) : Expr e → Expr e :=
  rewriteExprBottomUpM v

def rewriteExprTopDown   (v : Visitor e id) : Expr e → Expr e :=
  rewriteExprTopDownM v

def rewriteModuleBottomUp (v : Visitor e id) : Module e → Module e :=
  rewriteModuleBottomUpM v

def rewriteModuleTopDown  (v : Visitor e id) : Module e → Module e :=
  rewriteModuleTopDownM v

-- Monoidal fold (foldMap equivalent)
def foldMapExpr [Monoid r] (v : Visitor e (Const r)) : Expr e → r :=
  fun ex => (rewriteExprTopDownM v ex).getConst

def foldMapModule [Monoid r] (v : Visitor e (Const r)) : Module e → r :=
  fun m => (rewriteModuleTopDownM v m).getConst

end Combinators

end PureScript.CST.Traversal

module

import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop
public import PurescriptLanguageCstParser.PureScript.CST.Types.PType


namespace PureScript.CST.Types

@[expose] public section

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String
open PureScript.CST.Types

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

namespace Export

@[always_inline, simp] def map {α β : Type} (f : α → β) (e : Export α) : Export β :=
  match e with
  | .Value n        => .Value n
  | .Op n           => .Op n
  | .Type_ n m      => .Type_ n m
  | .TypeOp t n     => .TypeOp t n
  | .Class t n      => .Class t n
  | .Module t n     => .Module t n
  | .Error d        => .Error (f d)

@[simp] theorem id_map {α : Type} (e : Export α) : (e.map id) = e := by
  cases e <;> rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (e : Export α) : (e.map (g ∘ f)) = (e.map f |>.map g) := by
  cases e <;> rfl

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext e; exact id_map e

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext e; exact comp_map f g e

end Export

@[always_inline] instance : Functor Export where
  map := Export.map

instance : LawfulFunctor Export where
  map_const := rfl
  id_map e := Export.id_map e
  comp_map f g e := Export.comp_map f g e

---------------------------------------------------------------------------------------------------------
structure DataHead (e : Type) where
  keyword : SourceToken
  name : Name Proper
  parameters : Array (TypeVarBindingF (Name Ident) (Type_ e))
  deriving Repr, BEq

namespace DataHead

@[always_inline, simp] def map {α β : Type} (f : α → β) (h : DataHead α) : DataHead β :=
  { h with parameters := h.parameters.map (Functor.map (Functor.map f)) }

@[simp] theorem id_map {α : Type} (h : DataHead α) : (h.map id) = h := by
  cases h; aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (h : DataHead α) : (h.map (g ∘ f)) = (h.map f |>.map g) := by
  cases h; aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext h; exact id_map h

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext h; exact comp_map f g h

instance : Functor DataHead where map := map
instance : LawfulFunctor DataHead where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end DataHead

@[always_inline] instance : Functor DataHead where
  map := DataHead.map

instance : LawfulFunctor DataHead where
  map_const := rfl
  id_map e := DataHead.id_map e
  comp_map f g e := DataHead.comp_map f g e

structure DataCtor (e : Type) where
  name : Name Proper
  parameters : Array (Type_ e)
  deriving Repr, BEq

namespace DataCtor

@[always_inline, simp] def map {α β : Type} (f : α → β) (c : DataCtor α) : DataCtor β :=
  { c with parameters := c.parameters.map (Functor.map f) }

@[simp] theorem id_map {α : Type} (c : DataCtor α) : (c.map id) = c := by
  cases c; aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (c : DataCtor α) : (c.map (g ∘ f)) = (c.map f |>.map g) := by
  cases c; aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext c; exact id_map c

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext c; exact comp_map f g c

instance : Functor DataCtor where map := map
instance : LawfulFunctor DataCtor where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end DataCtor

@[always_inline] instance : Functor DataCtor where
  map := DataCtor.map

instance : LawfulFunctor DataCtor where
  map_const := rfl
  id_map e := DataCtor.id_map e
  comp_map f g e := DataCtor.comp_map f g e

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

namespace ClassHead

@[always_inline, simp] def map {α β : Type} (f : α → β) (h : ClassHead α) : ClassHead β :=
  { h with
    typeConstraint := h.typeConstraint.map (fun (o, t) => (Functor.map (Functor.map f) o, t))
    parameters := h.parameters.map (Functor.map (Functor.map f))
  }

@[simp] theorem id_map {α : Type} (h : ClassHead α) : (h.map id) = h := by
  cases h; aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (h : ClassHead α) : (h.map (g ∘ f)) = (h.map f |>.map g) := by
  cases h; aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext h; exact id_map h

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext h; exact comp_map f g h

instance : Functor ClassHead where map := map
instance : LawfulFunctor ClassHead where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end ClassHead


structure InstanceHead (e : Type) where
  keyword : SourceToken
  name : Option (Name Ident × SourceToken)
  constraints : Option (OneOrDelimited (Type_ e) × SourceToken)
  className : QualifiedName Proper
  types : Array (Type_ e)
  deriving Repr, BEq

namespace InstanceHead

@[always_inline, simp] def map {α β : Type} (f : α → β) (h : InstanceHead α) : InstanceHead β :=
  { h with
    constraints := h.constraints.map (fun (o, t) => (Functor.map (Functor.map f) o, t))
    types := h.types.map (Functor.map f)
  }

@[simp] theorem id_map {α : Type} (h : InstanceHead α) : (h.map id) = h := by
  cases h; aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (h : InstanceHead α) : (h.map (g ∘ f)) = (h.map f |>.map g) := by
  cases h; aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext h; exact id_map h

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext h; exact comp_map f g h

instance : Functor InstanceHead where map := map
instance : LawfulFunctor InstanceHead where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end InstanceHead


inductive RecordLabeled (a : Type)
  | Pun (name : Name Ident)
  | Field (label : Name Label) (separator : SourceToken) (value : a)
  deriving Repr, BEq

namespace RecordLabeled

@[always_inline, simp] def map {α β : Type} (f : α → β) (r : RecordLabeled α) : RecordLabeled β :=
  match r with
  | .Pun n         => .Pun n
  | .Field l sep v => .Field l sep (f v)

@[simp] theorem id_map {α : Type} (r : RecordLabeled α) : (r.map id) = r := by
  cases r <;> rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (r : RecordLabeled α) : (r.map (g ∘ f)) = (r.map f |>.map g) := by
  cases r <;> rfl

@[simp] theorem functor_map_id {α : Type} : map (id : α → α) = id := by funext e; exact id_map e

@[simp] theorem functor_map_comp {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext e; exact comp_map f g e

end RecordLabeled

@[always_inline] instance : Functor RecordLabeled where
  map := RecordLabeled.map

instance : LawfulFunctor RecordLabeled where
  map_const := rfl
  id_map r := RecordLabeled.id_map r
  comp_map f g r := RecordLabeled.comp_map f g r

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
  | Array (items : Delimited binder_e)
  | Record (fields : Delimited (RecordLabeled binder_e))
  | Parens (wrapped : Wrapped binder_e)
  | Typed (binder : binder_e) (token : SourceToken) (type_ : Type_ e)
  | Op (first : binder_e) (ops : NonEmptyArray (QualifiedName Operator × binder_e))
  | Error (data : e)
  deriving Repr, BEq

@[simp] theorem sizeOf_Wildcard {e α : Type} [SizeOf e] [SizeOf α] (t) :
  sizeOf (BinderF.Wildcard (e := e) (binder_e := α) t) = 1 + sizeOf t :=
  BinderF.Wildcard.sizeOf_spec t

@[simp] theorem sizeOf_Var {e α : Type} [SizeOf e] [SizeOf α] (n) :
  sizeOf (BinderF.Var (e := e) (binder_e := α) n) = 1 + sizeOf n :=
  BinderF.Var.sizeOf_spec n

@[simp] theorem sizeOf_Named {e α : Type} [SizeOf e] [SizeOf α] (n t b) :
  sizeOf (BinderF.Named (e := e) (binder_e := α) n t b) = 1 + sizeOf n + sizeOf t + sizeOf b :=
  BinderF.Named.sizeOf_spec n t b

@[simp] theorem sizeOf_Constructor {e α : Type} [SizeOf e] [SizeOf α] (n args) :
  sizeOf (BinderF.Constructor (e := e) (binder_e := α) n args) = 1 + sizeOf n + sizeOf args :=
  BinderF.Constructor.sizeOf_spec n args

@[simp] theorem sizeOf_Array {e α : Type} [SizeOf e] [SizeOf α] (items) :
  sizeOf (BinderF.Array (e := e) (binder_e := α) items) = 1 + sizeOf items :=
  BinderF.Array.sizeOf_spec items

@[simp] theorem sizeOf_Record {e α : Type} [SizeOf e] [SizeOf α] (fields) :
  sizeOf (BinderF.Record (e := e) (binder_e := α) fields) = 1 + sizeOf fields :=
  BinderF.Record.sizeOf_spec fields

@[simp] theorem sizeOf_Parens {e α : Type} [SizeOf e] [SizeOf α] (w) :
  sizeOf (BinderF.Parens (e := e) (binder_e := α) w) = 1 + sizeOf w :=
  BinderF.Parens.sizeOf_spec w

@[simp] theorem sizeOf_Typed {e α : Type} [SizeOf e] [SizeOf α] (b t t_) :
  sizeOf (BinderF.Typed (e := e) (binder_e := α) b t t_) = 1 + sizeOf b + sizeOf t + sizeOf t_ :=
  BinderF.Typed.sizeOf_spec b t t_

@[simp] theorem sizeOf_Op {e α : Type} [SizeOf e] [SizeOf α] (f ops) :
  sizeOf (BinderF.Op (e := e) (binder_e := α) f ops) = 1 + sizeOf f + sizeOf ops :=
  BinderF.Op.sizeOf_spec f ops

@[simp] theorem sizeOf_Error {e α : Type} [SizeOf e] [SizeOf α] (d) :
  sizeOf (BinderF.Error (e := e) (binder_e := α) d) = 1 + sizeOf d :=
  BinderF.Error.sizeOf_spec d

namespace BinderF

@[always_inline, simp] def map_binder_e (f : binder_e → binder_e') (b : BinderF e binder_e) : BinderF e binder_e' :=
  match b with
  | Wildcard t => Wildcard t
  | Var n => Var n
  | Named n t b' => Named n t (f b')
  | Constructor n args => Constructor n (args.map f)
  | Boolean t v => Boolean t v
  | Char t v => Char t v
  | NonEmptyString t v => NonEmptyString t v
  | Int p t v => Int p t v
  | Number p t v => Number p t v
  | Array items => Array (items.map f)
  | Record fields => Record (fields.map (Functor.map f))
  | Parens w => Parens (w.map f)
  | Typed b_e t t_ => Typed (f b_e) t t_
  | Op first ops => Op (f first) (ops.map (fun (o, b) => (o, f b)))
  | Error d => Error d

@[always_inline, simp] def map_e {e e' binder_e : Type} (f : e → e') (b : BinderF e binder_e) : BinderF e' binder_e :=
  match b with
  | Wildcard t => Wildcard t
  | Var n => Var n
  | Named n t b_e => Named n t b_e
  | Constructor n args => Constructor n args
  | Boolean t v => Boolean t v
  | Char t v => Char t v
  | NonEmptyString t v => NonEmptyString t v
  | Int p t v => Int p t v
  | Number p t v => Number p t v
  | Array items => Array items
  | Record fields => Record fields
  | Parens w => Parens w
  | Typed b_e t t_e => Typed b_e t (t_e.map f)
  | Op first ops => Op first ops
  | Error d => Error (f d)

@[simp] theorem map_e_id {e binder_e : Type} (b : BinderF e binder_e) : b.map_e id = b := by
  cases b <;> simp

@[simp] theorem map_e_comp {e1 e2 e3 binder_e : Type} (f : e1 → e2) (g : e2 → e3) (b : BinderF e1 binder_e) : b.map_e (g ∘ f) = (b.map_e f).map_e g := by
  cases b <;> simp

@[simp] theorem map_binder_e_id {e binder_e : Type} (b : BinderF e binder_e) : b.map_binder_e id = b := by
  cases b <;> simp

@[simp] theorem map_binder_e_comp {e binder_e1 binder_e2 binder_e3 : Type} (f : binder_e1 → binder_e2) (g : binder_e2 → binder_e3) (b : BinderF e binder_e1) : b.map_binder_e (g ∘ f) = (b.map_binder_e f).map_binder_e g := by
  cases b <;> simp [Function.comp]

end BinderF

inductive Binder (e : Type)
  | mk : BinderF e (Binder e) → Binder e
  deriving Repr, BEq

namespace Binder

def map {e1 e2 : Type} (f : e1 → e2) : Binder e1 → Binder e2
  | .mk (.Wildcard t) => .mk (.Wildcard t)
  | .mk (.Var n) => .mk (.Var n)
  | .mk (.Named n t b) => .mk (.Named n t (map f b))
  | .mk (.Constructor n args) => .mk (.Constructor n (args.map (map f)))
  | .mk (.Boolean t v) => .mk (.Boolean t v)
  | .mk (.Char t v) => .mk (.Char t v)
  | .mk (.NonEmptyString t v) => .mk (.NonEmptyString t v)
  | .mk (.Int p t v) => .mk (.Int p t v)
  | .mk (.Number p t v) => .mk (.Number p t v)
  | .mk (.Array items) => .mk (.Array (items.map (map f)))
  | .mk (.Record fields) => .mk (.Record (fields.map (Functor.map (map f))))
  | .mk (.Parens w) => .mk (.Parens (w.map (map f)))
  | .mk (.Typed b t t_) => .mk (.Typed (map f b) t (t_.map f))
  | .mk (.Op first ops) => .mk (.Op (map f first) (ops.map (fun x => (x.fst, map f x.snd))))
  | .mk (.Error d) => .mk (.Error (f d))
termination_by b
decreasing_by
  simp_wf
  simp only [sizeOf_mk, sizeOf_Named, sizeOf_Constructor, sizeOf_Array, sizeOf_Record, sizeOf_Parens, sizeOf_Typed, sizeOf_Op, sizeOf_Error]
  -- Use general sizeOf lemmas for containers
  simp [Delimited.sizeOf_spec, Separated.sizeOf_spec, Wrapped.sizeOf_spec]
  try omega

theorem map_id {e : Type} (b : Binder e) : b.map id = b := by
  match b with
  | .mk bf =>
    cases bf <;> simp [map, id_map]
    · exact map_id _
    · funext x; exact map_id x
    · funext x; exact map_id x
    · funext x; simp [Functor.map, map_id x]
    · exact map_id _
    · exact map_id _
    · exact map_id _
    · funext x; exact map_id x.snd
termination_by b
decreasing_by
  simp_wf
  simp only [sizeOf_mk, sizeOf_Named, sizeOf_Constructor, sizeOf_Array, sizeOf_Record, sizeOf_Parens, sizeOf_Typed, sizeOf_Op, sizeOf_Error]
  simp [Delimited.sizeOf_spec, Separated.sizeOf_spec, Wrapped.sizeOf_spec]
  try omega

theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (b : Binder e1) : b.map (g ∘ f) = (b.map f).map g := by
  match b with
  | .mk bf =>
    cases bf <;> simp [map, comp_map]
    · exact map_comp f g _
    · funext x; exact map_comp f g x
    · funext x; exact map_comp f g x
    · funext x; simp [Functor.map, map_comp f g x]
    · exact map_comp f g _
    · exact map_comp f g _
    · exact map_comp f g _
    · funext x; exact map_comp f g x.snd
termination_by b
decreasing_by
  simp_wf
  simp only [sizeOf_mk, sizeOf_Named, sizeOf_Constructor, sizeOf_Array, sizeOf_Record, sizeOf_Parens, sizeOf_Typed, sizeOf_Op, sizeOf_Error]
  simp [Delimited.sizeOf_spec, Separated.sizeOf_spec, Wrapped.sizeOf_spec]
  try omega

instance : Functor Binder where map := map
instance : LawfulFunctor Binder where
  map_const := rfl
  id_map := map_id
  comp_map := map_comp

end Binder

structure AndToken (α : Type) where
  value : α
  token : SourceToken
  deriving Repr, BEq

namespace AndToken

@[always_inline, simp] def map {α β : Type} (f : α → β) (a : AndToken α) : AndToken β :=
  { a with value := f a.value }

@[simp] theorem id_map {α : Type} (a : AndToken α) : (a.map id) = a := rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (a : AndToken α) : (a.map (g ∘ f)) = (a.map f |>.map g) := rfl

@[simp] theorem functor_map_id {α : Type} : map (id : α → α) = id := by funext e; exact id_map e

@[simp] theorem functor_map_comp {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext e; exact comp_map f g e

end AndToken

@[always_inline] instance : Functor AndToken where
  map := AndToken.map

instance : LawfulFunctor AndToken where
  map_const := rfl
  id_map a := AndToken.id_map a
  comp_map f g a := AndToken.comp_map f g a

inductive AppSpineF (e expr_e : Type)
  | Type_ (token : SourceToken) (type_ : Type_ e)
  | Term (expr : expr_e)
  deriving Repr, BEq

namespace AppSpineF

@[always_inline, simp] def map_expr_e {e α β : Type} (f : α → β) (s : AppSpineF e α) : AppSpineF e β :=
  match s with
  | .Type_ t type_ => .Type_ t type_
  | .Term expr     => .Term (f expr)

@[simp] theorem map_expr_e_id {e α : Type} (s : AppSpineF e α) : s.map_expr_e id = s := by
  cases s <;> rfl

@[simp] theorem map_expr_e_comp {e α β γ : Type} (f : α → β) (g : β → γ) (s : AppSpineF e α) : s.map_expr_e (g ∘ f) = map_expr_e g (s.map_expr_e f) := by
  cases s <;> rfl

instance {e : Type} : Functor (AppSpineF e) where map := map_expr_e
instance {e : Type} : LawfulFunctor (AppSpineF e) where
  map_const := rfl
  id_map := map_expr_e_id
  comp_map := map_expr_e_comp

@[always_inline, simp] def map_e {e1 e2 α : Type} (f : e1 → e2) (s : AppSpineF e1 α) : AppSpineF e2 α :=
  match s with
  | .Type_ t type_ => .Type_ t (Functor.map f type_)
  | .Term expr     => .Term expr

@[simp] theorem map_e_id {e α : Type} (s : AppSpineF e α) : s.map_e id = s := by
  cases s <;> simp

@[simp] theorem map_e_comp {e1 e2 e3 α : Type} (f : e1 → e2) (g : e2 → e3) (s : AppSpineF e1 α) : s.map_e (g ∘ f) = (s.map_e f).map_e g := by
  cases s <;> simp

end AppSpineF

inductive RecordUpdateF (e expr_e : Type)
  | Leaf (label : Name Label) (token : SourceToken) (expr : expr_e)
  | Branch (label : Name Label) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
  deriving Repr, BEq

namespace RecordUpdateF

@[simp] theorem sizeOf_Leaf {e α : Type} [SizeOf e] [SizeOf α] (l t expr) :
  sizeOf (RecordUpdateF.Leaf (e := e) (expr_e := α) l t expr) = 1 + sizeOf l + sizeOf t + sizeOf expr :=
  RecordUpdateF.Leaf.sizeOf_spec l t expr

@[simp] theorem sizeOf_Branch {e α : Type} [SizeOf e] [SizeOf α] (l updates) :
  sizeOf (RecordUpdateF.Branch (e := e) (expr_e := α) l updates) = 1 + sizeOf l + sizeOf updates :=
  RecordUpdateF.Branch.sizeOf_spec l updates

@[inline] def map_expr_e {e α β : Type} [SizeOf e] [SizeOf α] (f : α → β) (u : RecordUpdateF e α) : RecordUpdateF e β :=
  match u with
  | .Leaf label token expr => .Leaf label token (f expr)
  | .Branch label updates  => .Branch label (updates.attach.map (fun x => x.val.map_expr_e f))
termination_by sizeOf u
decreasing_by
  simp_wf
  have := DelimitedNonEmpty.sizeOf_attach_elem updates x
  omega

@[simp] theorem map_expr_e_id {e α : Type} (u : RecordUpdateF e α) : map_expr_e id u = u := by
  match u with
  | .Leaf label token expr => simp only [map_expr_e, id_eq]
  | .Branch label updates =>
    simp only [map_expr_e, Branch.injEq, true_and]
    have h : (fun x : { x // x ∈ updates } => x.val.map_expr_e id) = (fun x => x.val) := by
      funext x; exact map_expr_e_id x.val
    rw [h, DelimitedNonEmpty.attach_map_val]
termination_by sizeOf u
decreasing_by
  simp_wf
  have := DelimitedNonEmpty.sizeOf_attach_elem updates x
  omega

@[simp] theorem map_expr_e_comp {e α β γ : Type} (f : α → β) (g : β → γ) (u : RecordUpdateF e α) : map_expr_e (g ∘ f) u = map_expr_e g (map_expr_e f u) := by
  match u with
  | .Leaf label token expr => simp only [map_expr_e, Function.comp_apply]
  | .Branch label updates =>
    simp only [map_expr_e, Branch.injEq, true_and]
    have h : (fun x : { x // x ∈ updates } => x.val.map_expr_e (g ∘ f)) = (fun x => (x.val.map_expr_e f).map_expr_e g) := by
      funext x; exact map_expr_e_comp f g x.val
    rw [h]
    rw [DelimitedNonEmpty.attach_map]
    rw [← DelimitedNonEmpty.comp_map]
    rfl
termination_by sizeOf u
decreasing_by
  simp_wf
  have := DelimitedNonEmpty.sizeOf_attach_elem updates x
  omega

instance : Functor (RecordUpdateF e) where map := map_expr_e
instance : LawfulFunctor (RecordUpdateF e) where
  map_const := rfl
  id_map := map_expr_e_id
  comp_map := map_expr_e_comp

@[inline] def map_e {e1 e2 α : Type} [SizeOf e1] [SizeOf α] (f : e1 → e2) (u : RecordUpdateF e1 α) : RecordUpdateF e2 α :=
  match u with
  | .Leaf label token expr => .Leaf label token expr
  | .Branch label updates  => .Branch label (updates.attach.map (fun x => x.val.map_e f))
termination_by sizeOf u
decreasing_by
  simp_wf
  have := DelimitedNonEmpty.sizeOf_attach_elem updates x
  omega

@[simp] theorem map_e_id {e α : Type} (u : RecordUpdateF e α) : map_e id u = u := by
  match u with
  | .Leaf label token expr => simp only [map_e]
  | .Branch label updates =>
    simp only [map_e, Branch.injEq, true_and]
    have h : (fun x : { x // x ∈ updates } => x.val.map_e id) = (fun x => x.val) := by
      funext x; exact map_e_id x.val
    rw [h, DelimitedNonEmpty.attach_map_val]
termination_by sizeOf u
decreasing_by
  simp_wf
  have := DelimitedNonEmpty.sizeOf_attach_elem updates x
  omega

@[simp] theorem map_e_comp {e1 e2 e3 α : Type} (f : e1 → e2) (g : e2 → e3) (u : RecordUpdateF e1 α) : map_e (g ∘ f) u = map_e g (map_e f u) := by
  match u with
  | .Leaf label token expr => simp only [map_e]
  | .Branch label updates =>
    simp only [map_e, Branch.injEq, true_and]
    have h : (fun x : { x // x ∈ updates } => x.val.map_e (g ∘ f)) = (fun x => (x.val.map_e f).map_e g) := by
      funext x; exact map_e_comp f g x.val
    rw [h]
    rw [DelimitedNonEmpty.attach_map]
    rw [← DelimitedNonEmpty.comp_map]
    rfl
termination_by sizeOf u
decreasing_by
  simp_wf
  have := DelimitedNonEmpty.sizeOf_attach_elem updates x
  omega

end RecordUpdateF

structure RecordAccessorF (expr_e : Type) where
  expr : expr_e
  dot : SourceToken
  path : Separated (Name Label)
  deriving Repr, BEq

namespace RecordAccessorF

@[always_inline, simp] def map {α β : Type} (f : α → β) (a : RecordAccessorF α) : RecordAccessorF β :=
  { a with expr := f a.expr }

@[simp] theorem id_map {α : Type} (a : RecordAccessorF α) : (a.map id) = a := by
  cases a; aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (a : RecordAccessorF α) : (a.map (g ∘ f)) = (a.map f |>.map g) := by
  cases a; aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext a; exact id_map a

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext a; exact comp_map f g a

instance : Functor RecordAccessorF where map := map
instance : LawfulFunctor RecordAccessorF where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end RecordAccessorF

structure LambdaF (e expr_e : Type) where
  symbol : SourceToken
  binders : NonEmptyArray (Binder e)
  arrow : SourceToken
  body : expr_e
  deriving Repr, BEq

namespace LambdaF

@[always_inline, simp] def map_expr_e {e α β : Type} (f : α → β) (l : LambdaF e α) : LambdaF e β :=
  { l with body := f l.body }

@[simp] theorem map_expr_e_id {e α : Type} (l : LambdaF e α) : l.map_expr_e id = l := by
  cases l; rfl

@[simp] theorem map_expr_e_comp {e α β γ : Type} (f : α → β) (g : β → γ) (l : LambdaF e α) : l.map_expr_e (g ∘ f) = map_expr_e g (l.map_expr_e f) := by
  cases l; rfl

instance {e : Type} : Functor (LambdaF e) where map := map_expr_e
instance {e : Type} : LawfulFunctor (LambdaF e) where
  map_const := rfl
  id_map := map_expr_e_id
  comp_map := map_expr_e_comp

@[always_inline, simp] def map_e {e1 e2 α : Type} (f : e1 → e2) (l : LambdaF e1 α) : LambdaF e2 α :=
  { l with binders := l.binders.map (Functor.map f) }

@[simp] theorem map_e_id {e α : Type} (l : LambdaF e α) : l.map_e id = l := by
  cases l; simp [id_map]

@[simp] theorem map_e_comp {e1 e2 e3 α : Type} (f : e1 → e2) (g : e2 → e3) (l : LambdaF e1 α) : l.map_e (g ∘ f) = (l.map_e f).map_e g := by
  cases l; simp [comp_map]

end LambdaF

structure IfThenElseF (expr_e : Type) where
  keyword : SourceToken
  cond : expr_e
  then_ : SourceToken
  true_ : expr_e
  else_ : SourceToken
  false_ : expr_e
  deriving Repr, BEq

namespace IfThenElseF

@[always_inline, simp] def map {α β : Type} (f : α → β) (i : IfThenElseF α) : IfThenElseF β :=
  { i with cond := f i.cond, true_ := f i.true_, false_ := f i.false_ }

@[simp] theorem id_map {α : Type} (i : IfThenElseF α) : (i.map id) = i := by
  cases i; aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (i : IfThenElseF α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
  cases i; aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext i; exact id_map i

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i

instance : Functor IfThenElseF where map := map
instance : LawfulFunctor IfThenElseF where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end IfThenElseF

structure PatternGuardF (e expr_e : Type) where
  binder : Option (Binder e × SourceToken)
  expr : expr_e
  deriving Repr, BEq

namespace PatternGuardF

@[always_inline, simp] def map_expr_e {e α β : Type} (f : α → β) (p : PatternGuardF e α) : PatternGuardF e β :=
  { p with expr := f p.expr }

@[simp] theorem map_expr_e_id {e α : Type} (p : PatternGuardF e α) : p.map_expr_e id = p := by
  cases p; rfl

@[simp] theorem map_expr_e_comp {e α β γ : Type} (f : α → β) (g : β → γ) (p : PatternGuardF e α) : p.map_expr_e (g ∘ f) = map_expr_e g (p.map_expr_e f) := by
  cases p; rfl

instance {e : Type} : Functor (PatternGuardF e) where map := map_expr_e
instance : LawfulFunctor (PatternGuardF e) where
  map_const := rfl
  id_map := map_expr_e_id
  comp_map := map_expr_e_comp

@[always_inline, simp] def map_e {e1 e2 α : Type} (f : e1 → e2) (p : PatternGuardF e1 α) : PatternGuardF e2 α :=
  { p with binder := p.binder.map (fun (b, t) => (Functor.map f b, t)) }

@[simp] theorem map_e_id {e α : Type} (p : PatternGuardF e α) : p.map_e id = p := by
  cases p; simp [map_e, id_map]

@[simp] theorem map_e_comp {e1 e2 e3 α : Type} (f : e1 → e2) (g : e2 → e3) (p : PatternGuardF e1 α) : p.map_e (g ∘ f) = (p.map_e f).map_e g := by
  cases p; simp [map_e, comp_map]
  apply congr_arg; funext x; simp [comp_map]

end PatternGuardF

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

-- 1. GuardExpr depends only on Where
structure GuardedExprF (e expr_e where_e : Type) where
  bar        : SourceToken
  patterns   : Separated (PatternGuardF e expr_e)
  separator  : SourceToken
  where_     : where_e
  deriving Repr, BEq

-- 2. Guarded depends on Where and GuardExpr
inductive GuardedF (e expr_e where_e guardedExpr_e : Type) where
  | Unconditional (token : SourceToken) (where_ : where_e)
  | Guarded (branches : NonEmptyArray guardedExpr_e)
  deriving Repr, BEq

-- 3. ValueBindingFields depends on Guarded
structure ValueBindingFieldsF (e expr_e guardedExpr_e : Type) where
  name    : Name Ident
  binders : Array (Binder e)
  guarded : guardedExpr_e
  deriving Repr, BEq
-- 4. Where depends on the list of Bindings
structure WhereF (e expr_e letBinding_e : Type) where
  expr     : expr_e
  bindings : Option (SourceToken × NonEmptyArray letBinding_e)
  deriving Repr, BEq

-- 5. LetBinding is the "Sum" of the complex
inductive LetBindingF (e expr_e valueBindingFields_e where_e : Type) where
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Name (fields : valueBindingFields_e)
  | Pattern (binder : Binder e) (token : SourceToken) (where_ : where_e)
  | Error (data : e)
  deriving Repr, BEq

structure CaseOfF (e expr_e guardedRecursive_e : Type) where
  keyword : SourceToken
  head : Separated expr_e
  of : SourceToken
  branches : NonEmptyArray (Separated (Binder e) × guardedRecursive_e)
  deriving Repr, BEq

structure LetInF (e expr_e letBindingRecursive_e : Type) where
  keyword : SourceToken
  bindings : NonEmptyArray letBindingRecursive_e
  in_ : SourceToken
  body : expr_e
  deriving Repr, BEq

inductive DoStatementF (e expr_e letBindingRecursive_e : Type)
  | Let (token : SourceToken) (bindings : NonEmptyArray letBindingRecursive_e)
  | Discard (expr : expr_e)
  | Bind (binder : Binder e) (token : SourceToken) (expr : expr_e)
  | Error (data : e)
  deriving Repr, BEq

structure DoBlockF (e expr_e doStatement_e : Type) where
  keyword : SourceToken
  statements : NonEmptyArray doStatement_e
  deriving Repr, BEq

structure AdoBlockF (e expr_e doStatement_e : Type) where
  keyword : SourceToken
  statements : Array doStatement_e
  in_ : SourceToken
  result : expr_e
  deriving Repr, BEq

inductive ExprF (e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e : Type)
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
  | Case (data : CaseOfF e expr_e guardedRecursive_e)
  | Let (data : LetInF e expr_e letBindingRecursive_e)
  | Do (data : doBlock)
  | Ado (data : adoBlock)
  | Error (data : e)
  deriving Repr, BEq

-- https://github.com/leanprover/lean4/issues/13465#issuecomment-4349653768
-- mutual

-- inductive LetBindingRecursive (e : Type) where
--   | mk : LetBindingF e (Expr e)
--       (ValueBindingFieldsRecursive e)
--       (WhereRecursive e)
--     → LetBindingRecursive e
--   deriving Repr, BEq

-- inductive WhereRecursive (e : Type) where
--   | mk : WhereF e (Expr e) (LetBindingRecursive e) → WhereRecursive e
--   deriving Repr, BEq

-- inductive GuardedRecursive (e : Type) where
--   | mk : GuardedF e (Expr e)
--       (WhereRecursive e)
--       (GuardedRecursive e)
--     → GuardedRecursive e
--   deriving Repr, BEq

-- inductive ValueBindingFieldsRecursive (e : Type) where
--   | mk : ValueBindingFieldsF e (Expr e) (GuardedRecursive e)
--     → ValueBindingFieldsRecursive e
--   deriving Repr, BEq

-- inductive DoStatementRecursive (e : Type)
--   | mk : DoStatementF e (Expr e) (LetBindingRecursive e) → DoStatementRecursive e
--   deriving Repr, BEq

-- inductive DoBlockRecursive (e : Type)
--   | mk : DoBlockF e (Expr e) (DoStatementRecursive e) → DoBlockRecursive e
--   deriving Repr, BEq

-- inductive AdoBlockRecursive (e : Type)
--   | mk : AdoBlockF e (Expr e) (DoStatementRecursive e) → AdoBlockRecursive e
--   deriving Repr, BEq

-- inductive Expr (e : Type)
--   | mk : ExprF e (Expr e) (DoBlockRecursive e) (AdoBlockRecursive e) (LetBindingRecursive e) (GuardedRecursive e) → Expr e
--   deriving Repr, BEq
-- end
-----------------------------------------------------------------------------------------------------------

-- inductive InstanceBinding (e : Type)
--   | Signature (labeled : Labeled (Name Ident) (Type_ e))
--   | Name (fields : ValueBindingFieldsRecursive e)
--   deriving Repr, BEq

-- structure Instance (e : Type) where
--   head : InstanceHead e
--   body : Option (SourceToken × NonEmptyArray (InstanceBinding e))
--   deriving Repr, BEq

inductive Foreign (e : Type)
  | Value (labeled : Labeled (Name Ident) (Type_ e))
  | Data (keyword : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
  | Kind (keyword : SourceToken) (name : Name Proper)
  deriving Repr, BEq

namespace Foreign

@[always_inline, simp] def map {α β : Type} (f : α → β) (o : Foreign α) : Foreign β :=
  match o with
  | .Value l => .Value (Functor.map (Functor.map f) l)
  | .Data k l => .Data k (Functor.map (Functor.map f) l)
  | .Kind k n => .Kind k n

@[simp] theorem id_map {α : Type} (o : Foreign α) : (o.map id) = o := by
  cases o <;> aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (o : Foreign α) : (o.map (g ∘ f)) = (o.map f |>.map g) := by
  cases o <;> aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext o; exact id_map o

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext o; exact comp_map f g o

instance : Functor Foreign where map := map
instance : LawfulFunctor Foreign where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end Foreign

@[always_inline] instance : Functor Foreign where
  map := Foreign.map

instance : LawfulFunctor Foreign where
  map_const := rfl
  id_map o := Foreign.id_map o
  comp_map f g o := Foreign.comp_map f g o

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

-- inductive Declaration (e : Type)
--   | Data (head : DataHead e) (optionSeparator : Option (SourceToken × (Separated (DataCtor e))))
--   | Type_ (head : DataHead e) (token : SourceToken) (type_ : Type_ e)
--   | Newtype (head : DataHead e) (token : SourceToken) (name : Name Proper) (type_ : Type_ e)
--   | Class (head : ClassHead e) (optionSeparator : Option (SourceToken × NonEmptyArray (Labeled (Name Ident) (Type_ e))))
--   | InstanceChain (separated : Separated (Instance e))
--   | Derive (keyword : SourceToken) (optionToken : Option SourceToken) (head : InstanceHead e)
--   | KindSignature (token1 : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
--   | Signature (labeled : Labeled (Name Ident) (Type_ e))
--   | Value (fields : ValueBindingFieldsRecursive e)
--   | Fixity (fields : FixityFields)
--   | Foreign (token1 : SourceToken) (token2 : SourceToken) (foreign : Foreign e)
--   | Role (token1 : SourceToken) (token2 : SourceToken) (name : Name Proper) (roles : NonEmptyArray (SourceToken × Role))
--   | Error (data : e)
--   deriving Repr, BEq

-----------------------------------------------------------------------------------------------------------

inductive Import (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Error (data : e)
  deriving Repr, BEq

namespace Import

@[always_inline, simp] def map {α β : Type} (f : α → β) (i : Import α) : Import β :=
  match i with
  | .Value n        => .Value n
  | .Op n           => .Op n
  | .Type_ n m      => .Type_ n m
  | .TypeOp t n     => .TypeOp t n
  | .Class t n      => .Class t n
  | .Error d        => .Error (f d)

@[simp] theorem id_map {α : Type} (i : Import α) : (i.map id) = i := by
  cases i <;> rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (i : Import α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
  cases i <;> rfl

@[simp] theorem functor_map_id {α : Type} : map (id : α → α) = id := by funext i; exact id_map i

@[simp] theorem functor_map_comp {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i

end Import

@[always_inline] instance : Functor Import where
  map := Import.map

instance : LawfulFunctor Import where
  map_const := rfl
  id_map i := Import.id_map i
  comp_map f g i := Import.comp_map f g i

structure ImportDecl (e : Type) where
  keyword : SourceToken
  module_ : Name ModuleName
  importList : Option (Option SourceToken × DelimitedNonEmpty (Import e))
  qualified : Option (SourceToken × Name ModuleName)
  deriving Repr, BEq

namespace ImportDecl

@[always_inline, simp] def map {α β : Type} (f : α → β) (i : ImportDecl α) : ImportDecl β :=
  { i with importList := i.importList.map (fun (o, d) => (o, Functor.map (Functor.map f) d)) }

@[simp] theorem id_map {α : Type} (i : ImportDecl α) : (i.map id) = i := by
  cases i; aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (i : ImportDecl α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
  cases i; aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext i; exact id_map i

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i

instance : Functor ImportDecl where map := map
instance : LawfulFunctor ImportDecl where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end ImportDecl

@[always_inline] instance : Functor ImportDecl where
  map := ImportDecl.map

instance : LawfulFunctor ImportDecl where
  map_const := rfl
  id_map i := ImportDecl.id_map i
  comp_map f g i := ImportDecl.comp_map f g i
-----------------------------------------------------------------------------------------------------------

structure ModuleHeader (e : Type) where
  keyword : SourceToken
  name : Name ModuleName
  exports : Option (DelimitedNonEmpty (Export e))
  where_ : SourceToken
  imports : Array (ImportDecl e)
  deriving Repr, BEq

namespace ModuleHeader

@[always_inline, simp] def map {α β : Type} (f : α → β) (m : ModuleHeader α) : ModuleHeader β :=
  { m with
    exports := m.exports.map (Functor.map (Functor.map f))
    imports := m.imports.map (Functor.map f)
  }

@[simp] theorem id_map {α : Type} (m : ModuleHeader α) : (m.map id) = m := by
  cases m; aesop

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (m : ModuleHeader α) : (m.map (g ∘ f)) = (m.map f |>.map g) := by
  cases m; aesop

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext m; exact id_map m

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext m; exact comp_map f g m

instance : Functor ModuleHeader where map := map
instance : LawfulFunctor ModuleHeader where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

end ModuleHeader


-- structure ModuleBody (e : Type) where
--   decls : Array (Declaration e)
--   trailingComments : Array (Comment LineFeed)
--   end_ : SourcePos
--   deriving Repr, BEq

-- structure Module (e : Type) where
--   header : ModuleHeader e
--   body : ModuleBody e
--   deriving Repr, BEq
end
end PureScript.CST.Types

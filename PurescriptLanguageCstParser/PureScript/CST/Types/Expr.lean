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

-- #print RecordLabeled._sizeOf_1
-- #print RecordLabeled.Pun.sizeOf_spec
-- #print RecordLabeled.Field.sizeOf_spec

namespace RecordLabeled

@[always_inline, simp] def map {α β : Type} (f : α → β) (r : RecordLabeled α) : RecordLabeled β :=
  match r with
  | .Pun n         => .Pun n
  | .Field l sep v => .Field l sep (f v)

@[simp] theorem id_map {α : Type} (r : RecordLabeled α) : (r.map id) = r := by
  cases r <;> rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (r : RecordLabeled α) : (r.map (g ∘ f)) = (r.map f |>.map g) := by
  cases r <;> rfl

theorem map_id' {α : Type} (r : RecordLabeled α) (f : α → α) (hf : ∀ x, f x = x) : r.map f = r := by
  cases r <;> simp [map, hf]

theorem map_comp' {α β γ : Type} (r : RecordLabeled α) (f : α → β) (g : β → γ) (h : α → γ) (hh : ∀ x, h x = g (f x)) :
  r.map h = (r.map f).map g := by
  cases r <;> simp [map, hh]

@[simp] theorem functor_map_id {α : Type} : map (id : α → α) = id := by funext e; exact id_map e

@[simp] theorem functor_map_comp {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext e; exact comp_map f g e

theorem sizeOf_field_value {α : Type} [SizeOf α]
    (l : Name Label) (sep : SourceToken) (v : α) :
    sizeOf v < sizeOf (RecordLabeled.Field l sep v) := by
  rw [RecordLabeled.Field.sizeOf_spec]; omega

-- The real issue is that `field.map (fun b_in => map f b_in)` passes `b_in` as a lambda argument, and Lean generates a termination goal for every possible `b_in` — including the impossible `Pun` case where the function is never actually called.
-- The solution: add a `Membership` instance for `RecordLabeled` and a `sizeOf_attach_elem` lemma
instance {α : Type} : Membership α (RecordLabeled α) where
  mem r a := match r with
    | .Pun _     => False
    | .Field _ _ v => a = v

@[simp] theorem mem_def {α : Type} (a : α) (r : RecordLabeled α) :
    a ∈ r ↔ match r with | .Pun _ => False | .Field _ _ v => a = v := Iff.rfl

@[simp] theorem sizeOf_attach_elem {α : Type} [SizeOf α] (r : RecordLabeled α)
    (x : { x // x ∈ r }) : sizeOf x.val < sizeOf r := by
  obtain ⟨val, property⟩ := x
  cases r with
  | Pun n => exact absurd property (by simp [mem_def])
  | Field l sep v =>
    simp only [mem_def] at property
    subst property
    rw [RecordLabeled.Field.sizeOf_spec]
    grind only

def attach {α : Type} (r : RecordLabeled α) : RecordLabeled { x // x ∈ r } :=
  match r with
  | .Pun n     => .Pun n
  | .Field l sep v => .Field l sep ⟨v, by simp [mem_def]⟩

@[simp] theorem attach_map {α β : Type} (r : RecordLabeled α) (f : α → β) :
    r.attach.map (fun x => f x.val) = r.map f := by
  cases r <;> rfl

@[simp] theorem attach_map_val {α : Type} (r : RecordLabeled α) :
    r.attach.map (fun x => x.val) = r := by
  cases r <;> rfl


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
  cases b <;> simp only [map_binder_e, Function.comp_apply, Array.map_map]
  · simp_all only [Delimited.map, Separated.map_comp_fun, Option.map_eq_map, Option.map_map]
  · simp_all only [Delimited.map, functor_map_comp, Separated.map_comp_fun, Option.map_eq_map, Option.map_map]
  · simp_all only [Wrapped.map, Function.comp_apply]
  · simp_all only [NonEmptyArray.map, Array.map_map, Op.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left,
    Function.comp_apply, implies_true, and_self]

end BinderF

inductive Binder (e : Type)
  | mk : BinderF e (Binder e) → Binder e
  deriving Repr, BEq

@[simp] theorem sizeOf_mk {e : Type} [SizeOf e] (bf : BinderF e (Binder e)) :
  sizeOf (Binder.mk bf) = 1 + sizeOf bf :=
  Binder.mk.sizeOf_spec bf

namespace Binder

def map {e1 e2 : Type} (f : e1 → e2) (b : Binder e1) : Binder e2 :=
  match b with
  | .mk (.Wildcard t)         => .mk (.Wildcard t)
  | .mk (.Var n)              => .mk (.Var n)
  | .mk (.Named n t b)        => .mk (.Named n t (map f b))
  | .mk (.Constructor n args) => .mk (.Constructor n (args.map (map f)))
  | .mk (.Boolean t v)        => .mk (.Boolean t v)
  | .mk (.Char t v)           => .mk (.Char t v)
  | .mk (.NonEmptyString t v) => .mk (.NonEmptyString t v)
  | .mk (.Int p t v) => .mk (.Int p t v)
  | .mk (.Number p t v) => .mk (.Number p t v)
  | .mk (.Array items) => .mk (.Array (items.attach.map (fun ⟨b, _⟩ => map f b)))
  | .mk (.Record fields) => .mk (.Record (fields.attach.map (fun ⟨field, _h_field⟩ =>
      field.attach.map (fun ⟨b_in, _h_b_in⟩ => map f b_in))))
  | .mk (.Parens w) => .mk (.Parens (w.attach.map (fun ⟨b, _⟩ => map f b)))
  | .mk (.Typed b t t_) => .mk (.Typed (map f b) t (t_.map f))
  | .mk (.Op first ops) => .mk (.Op (map f first) (ops.attach.map (fun ⟨pair, _h_pair_mem⟩ => (pair.1, map f pair.2))))
  | .mk (.Error d) => .mk (.Error (f d))
termination_by b
decreasing_by
  all_goals simp_wf
  all_goals simp +arith only
  -- Constructor element
  · rename_i x hmem
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hmem
    have h1 : sizeOf (args[i]'hi) < sizeOf args := Array.sizeOf_getElem args i hi
    have h2 : sizeOf (Binder.mk (BinderF.Constructor n args)) = 1 + 1 + sizeOf n + sizeOf args := by
      rw [Binder.mk.sizeOf_spec, BinderF.Constructor.sizeOf_spec]
      simp_all only [Array.getElem_mem, Array.sizeOf_getElem, Nat.reduceAdd]
      grind only
    omega
  -- Array element
  · rename_i hmem
    have h1 : sizeOf b < sizeOf items := Delimited.sizeOf_attach_elem items ⟨b, hmem⟩
    have h2 : sizeOf (Binder.mk (BinderF.Array items)) = 1 + 1 + sizeOf items := by
      rw [Binder.mk.sizeOf_spec, BinderF.Array.sizeOf_spec]
      grind only
    omega
  -- Record element
  · -- b_in ∈ field, field ∈ fields
    have h1 : sizeOf field < sizeOf fields :=
      Delimited.sizeOf_attach_elem fields ⟨field, _h_field⟩
    have h2 : sizeOf b_in < sizeOf field :=
      RecordLabeled.sizeOf_attach_elem field ⟨b_in, _h_b_in⟩
    omega
  -- Parens
  · have hmem : b ∈ w := by assumption
    have h1 : sizeOf b < sizeOf w := Wrapped.sizeOf_attach_elem w ⟨b, hmem⟩
    have h2 : sizeOf (Binder.mk (BinderF.Parens w)) = 1 + 1 + sizeOf w := by
      rw [Binder.mk.sizeOf_spec, BinderF.Parens.sizeOf_spec]
      simp_all only [Wrapped.mem_def, Wrapped.sizeOf_value, Nat.reduceAdd]
      subst hmem
      grind only
    omega
  -- Op element
  · have h1 : sizeOf pair < sizeOf ops := NonEmptyArray.sizeOf_lt_of_mem _h_pair_mem
    have h2 : sizeOf pair.2 < sizeOf pair := by
      match pair with | (op, binder) => simp [Prod.mk.sizeOf_spec]; omega
    omega

@[simp] theorem map_id {e : Type} (b : Binder e) : b.map id = b := by
  match b with
  | .mk bf =>
    match bf with
    | .Wildcard t => aesop?
    | .Var n => rfl
    | .Named n t b =>
        simp only [map]
        exact congrArg (Binder.mk ∘ BinderF.Named n t) (map_id b)
    | .Constructor n args =>
        simp only [map, Binder.mk.injEq, BinderF.Constructor.injEq, true_and]
        apply Array.ext; simp
        intro i h1 _; simp [Array.getElem_map, map_id (args[i]'h1)]
    | .Boolean t v => rfl
    | .Char t v => rfl
    | .NonEmptyString t v => rfl
    | .Int p t v => rfl
    | .Number p t v => rfl
    | .Array items =>
        simp only [map, Binder.mk.injEq]
        rw [← Delimited.attach_map items (map id), Delimited.attach_map_val]
        congr 1; ext ⟨x, _⟩; exact map_id x
    | .Record fields =>
        simp only [map, Binder.mk.injEq]
        rw [← Delimited.attach_map fields (RecordLabeled.map (map id)), Delimited.attach_map_val]
        congr 1; ext ⟨field, _⟩
        cases field with
        | Pun n => rfl
        | Field l sep v =>
            simp only [RecordLabeled.attach, RecordLabeled.map]
            rw [← RecordLabeled.attach_map (RecordLabeled.Field l sep v) (map id)]
            simp [RecordLabeled.attach, RecordLabeled.attach_map, map_id v]
    | .Parens w =>
        simp only [map, Binder.mk.injEq]
        rw [← Wrapped.attach_map w (map id), Wrapped.attach_map_val]
        congr 1; ext ⟨x, _⟩; exact map_id x
    | .Typed b t t_ =>
        simp only [map, Binder.mk.injEq, BinderF.Typed.injEq, true_and, and_true]
        exact map_id b
    | .Op first ops =>
        simp only [map, Binder.mk.injEq, BinderF.Op.injEq]
        refine ⟨map_id first, ?_⟩
        rw [← NonEmptyArray.attach_map ops (fun p => (p.1, map id p.2))]
        · simp [NonEmptyArray.attach_map_val]
          apply NonEmptyArray.ext; apply Array.ext; simp
          intro i h1 _
          simp [Array.getElem_map, map_id]
        · intro ⟨op, b⟩ _; exact (op, map id b)
    | .Error d => rfl
termination_by b
-- @[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (b : Binder e1) :
--     b.map (g ∘ f) = (b.map f).map g := by
--   match b with
--   | .mk bf =>
--     cases bf with
--     | Wildcard t => rfl
--     | Var n => rfl
--     | Named n t b =>
--         simp only [map]
--         exact congrArg (Binder.mk ∘ BinderF.Named n t) (map_comp f g b)
--     | Constructor n args =>
--         simp only [map, Binder.mk.injEq, BinderF.Constructor.injEq, true_and, Array.map_map]
--         congr 1; ext i; exact map_comp f g _
--     | Boolean t v => rfl
--     | Char t v => rfl
--     | NonEmptyString t v => rfl
--     | Int p t v => rfl
--     | Number p t v => rfl
--     | Array items =>
--         simp only [map, Binder.mk.injEq]
--         conv_lhs => rw [show items.map (map (g ∘ f)) = (items.map (map f)).map (map g) from ?_]
--         · rfl
--         · apply Delimited.comp_map' items
--           intro x; exact map_comp f g x
--     | Record fields =>
--         simp only [map, Binder.mk.injEq]
--         conv_lhs => rw [show fields.map (RecordLabeled.map (map (g ∘ f))) =
--             (fields.map (RecordLabeled.map (map f))).map (RecordLabeled.map (map g)) from ?_]
--         · rfl
--         · rw [← Delimited.comp_map]
--           apply Delimited.map_congr
--           intro rl
--           cases rl with
--           | Pun n => rfl
--           | Field l sep v => simp [RecordLabeled.map, map_comp f g v]
--     | Parens w =>
--         simp only [map, Binder.mk.injEq]
--         cases w; simp [Wrapped.map, map_comp f g]
--     | Typed b t t_ =>
--         simp only [map, Binder.mk.injEq, BinderF.Typed.injEq, true_and, and_true]
--         constructor
--         · exact map_comp f g b
--         · exact Type_.map_comp f g t_
--     | Op first ops =>
--         simp only [map, Binder.mk.injEq, BinderF.Op.injEq]
--         constructor
--         · exact map_comp f g first
--         · apply NonEmptyArray.ext
--           apply Array.ext; simp [Array.size_map, Array.map_map]
--           intro i h1 h2
--           simp [Array.getElem_map, map_comp f g]
--     | Error d => simp [map, Function.comp]
-- termination_by b
-- Helper: attach then map f is the same as map f on array elements
@[simp] theorem mapArray_eq {e f : Type} (g : e → f) (arr : Array (Binder e)) :
    arr.map (map g) = arr.attach.map (fun ⟨b, _⟩ => map g b) := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [Array.getElem_map]

-- @[simp] theorem map_id {e : Type} (b : Binder e) : b.map id = b := by
--   induction b using Binder.rec with -- won't work directly, use match
--   match b with
--   | .mk bf => cases bf <;> simp [map, LawfulFunctor.id_map, Array.map_id_fun,
--       RecordLabeled.functor_map_id, Delimited.id_map, Wrapped.id_map]
--     all_goals (
--       try (apply Array.ext; simp; intro i h1 _; simp [Array.getElem_map]; apply map_id))

-- @[simp] theorem map_id {e : Type} (b : Binder e) : b.map id = b := by
--   match b with
--   | .mk bf =>
--     cases bf <;> simp_all [map]
--     · rename_i args
--       have ih := fun a (h : a ∈ args) => map_id a
--       apply Array.ext
--       · simp
--       · intro i h1 h2
--         simp only [Array.getElem_map]
--         exact ih (args[i]'h1) (Array.getElem_mem args i h1)
--     · rename_i items
--       have ih := fun a (h : a ∈ items) => map_id a
--       rw [Delimited.attach_map_val]
--       cases items with | mk v =>
--       simp only [map, Delimited.map, Option.map_eq_map]
--       split <;> simp_all
--       rename_i w
--       apply Separated.ext
--       · exact ih w.head (by simp_all [Delimited.mem_def])
--       · apply Array.ext
--         · simp
--         · intro i h1 h2
--           simp only [Array.getElem_map]
--           exact ih (w.tail[i]'h1).2 (by simp_all [Delimited.mem_def]; exact Or.inr ⟨(w.tail[i]).1, Array.getElem_mem _ _ _⟩)
--     · rename_i fields
--       have ih := fun a (h : a ∈ fields) => match a with
--         | .Field l t v => map_id v = v
--         | .Pun n => rfl
--       rw [Delimited.attach_map_val]
--       cases fields with | mk v =>
--       simp only [map, Delimited.map, Option.map_eq_map]
--       split <;> simp_all
--       rename_i w
--       apply Separated.ext
--       · cases w.head <;> simp_all
--         exact ih _ (by simp_all [Delimited.mem_def])
--       · apply Array.ext
--         · simp
--         · intro i h1 h2
--           simp only [Array.getElem_map]
--           cases (w.tail[i]'h1).2 <;> simp_all
--           exact ih _ (by simp_all [Delimited.mem_def]; exact Or.inr ⟨(w.tail[i]).1, Array.getElem_mem _ _ _⟩)
--     · rename_i w
--       have ih := fun a (h : a ∈ w) => map_id a
--       rw [Wrapped.attach_map_val]
--       cases w; simp_all
--       exact ih _ (by simp)
--     · rename_i first ops
--       simp_all
--       apply NonEmptyArray.ext
--       simp only [map, NonEmptyArray.toArr_map, Array.map_map, Function.comp_def]
--       apply Array.ext
--       · simp
--       · intro i h1 h2
--         simp only [Array.getElem_map]
--         split <;> simp_all
--         exact map_id _

-- @[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (b : Binder e1) : b.map (g ∘ f) = (b.map f).map g := by
--   match b with
--   | .mk bf =>
--     cases bf <;> simp_all [map]
--     · aesop?
--     ·
--       intro a a_1
--       aesop?
--     ·
--       apply And.intro
--       · rfl
--       · apply And.intro
--         · aesop?
--         · rfl
--     · rename_i items
--       rw [Delimited.attach_map]
--       cases items with | mk v =>
--       simp only [map, Delimited.map, Option.map_eq_map]
--       split <;> simp_all
--       rename_i w
--       apply Separated.ext
--       · exact map_comp f g _
--       · apply Array.ext
--         · simp
--         · intro i h1 h2
--           simp only [Array.getElem_map]
--           exact map_comp f g _
--     · rename_i fields
--       try rw [Delimited.attach_map]
--       cases fields with | mk v =>
--       apply And.intro
--       · rfl
--       · apply And.intro
--         · exact map_comp f g _
--         · rfl
--     · rename_i w
--       try rw [Wrapped.attach_map]
--       cases w
--       exact map_comp f g _
--     · rename_i first ops
--       try apply NonEmptyArray.ext
--       apply And.intro
--       · exact map_comp f g _
--       · apply And.intro
--         · apply And.intro
--           · sorry
--           · sorry
--         · sorry
--       simp only [map, NonEmptyArray.toArr_map, Array.map_map, Function.comp_def]
--       apply Array.ext
--       · simp
--       · intro i h1 h2
--         simp only [Array.getElem_map]
--         split <;> simp_all
--         exact map_comp f g _

-- instance : Functor Binder where map := map
-- instance : LawfulFunctor Binder where
--   map_const := rfl
--   id_map := map_id
--   comp_map := map_comp

end Binder

-- structure AndToken (α : Type) where
--   value : α
--   token : SourceToken
--   deriving Repr, BEq
--
-- namespace AndToken
--
-- @[always_inline, simp] def map {α β : Type} (f : α → β) (a : AndToken α) : AndToken β :=
--   { a with value := f a.value }
--
-- @[simp] theorem id_map {α : Type} (a : AndToken α) : (a.map id) = a := rfl
--
-- @[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (a : AndToken α) : (a.map (g ∘ f)) = (a.map f |>.map g) := rfl
--
-- @[simp] theorem functor_map_id {α : Type} : map (id : α → α) = id := by funext e; exact id_map e
--
-- @[simp] theorem functor_map_comp {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext e; exact comp_map f g e
--
-- end AndToken
--
-- @[always_inline] instance : Functor AndToken where
--   map := AndToken.map
--
-- instance : LawfulFunctor AndToken where
--   map_const := rfl
--   id_map a := AndToken.id_map a
--   comp_map f g a := AndToken.comp_map f g a
--
-- inductive AppSpineF (e expr_e : Type)
--   | Type_ (token : SourceToken) (type_ : Type_ e)
--   | Term (expr : expr_e)
--   deriving Repr, BEq
--
-- namespace AppSpineF
--
-- @[always_inline, simp] def map_all {e1 e2 α β : Type} (f : e1 → e2) (f_expr : α → β) (s : AppSpineF e1 α) : AppSpineF e2 β :=
--   match s with
--   | .Term e => .Term (f_expr e)
--   | .Type_ t ty => .Type_ t (ty.map f)
--
-- @[simp] theorem map_all_id {e α : Type} (s : AppSpineF e α) : s.map_all id id = s := by
--   match s with
--   | .Term e => simp only [map_all, id_eq]
--   | .Type_ t ty => simp only [map_all, Type_.map_id]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 α β γ : Type} (f : e1 → e2) (g : e2 → e3) (f_expr : α → β) (g_expr : β → γ) (s : AppSpineF e1 α) :
--   s.map_all (g ∘ f) (g_expr ∘ f_expr) = (s.map_all f f_expr).map_all g g_expr := by
--   match s with
--   | .Term e => simp only [map_all, Function.comp_apply]
--   | .Type_ t ty => simp only [map_all, Type_.map_comp]
--
-- @[always_inline, simp] def map_expr_e {e α β : Type} (f : α → β) (s : AppSpineF e α) : AppSpineF e β :=
--   s.map_all id f
--
-- @[always_inline, simp] def map_e {e1 e2 α : Type} (f : e1 → e2) (s : AppSpineF e1 α) : AppSpineF e2 α :=
--   s.map_all f id
--
-- instance {e : Type} : Functor (AppSpineF e) where map := map_expr_e
-- instance {e : Type} : LawfulFunctor (AppSpineF e) where
--   map_const := rfl
--   id_map := map_all_id
--   comp_map f g x := map_all_comp id id f g x
--
-- end AppSpineF
--
-- inductive RecordUpdateF (e expr_e : Type)
--   | Leaf (label : Name Label) (token : SourceToken) (expr : expr_e)
--   | Branch (label : Name Label) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
--   deriving Repr, BEq
--
-- namespace RecordUpdateF
--
-- @[simp] theorem sizeOf_Leaf {e α : Type} [SizeOf e] [SizeOf α] (l t expr) :
--   sizeOf (RecordUpdateF.Leaf (e := e) (expr_e := α) l t expr) = 1 + sizeOf l + sizeOf t + sizeOf expr :=
--   RecordUpdateF.Leaf.sizeOf_spec l t expr
--
-- @[simp] theorem sizeOf_Branch {e α : Type} [SizeOf e] [SizeOf α] (l updates) :
--   sizeOf (RecordUpdateF.Branch (e := e) (expr_e := α) l updates) = 1 + sizeOf l + sizeOf updates :=
--   RecordUpdateF.Branch.sizeOf_spec l updates
--
-- @[inline] def map_all {e1 e2 α β : Type} [SizeOf e1] [SizeOf α] (f : e1 → e2) (f_expr : α → β) (u : RecordUpdateF e1 α) : RecordUpdateF e2 β :=
--   match u with
--   | .Leaf label token expr => .Leaf label token (f_expr expr)
--   | .Branch label updates  => .Branch label (updates.attach.map (fun x => x.val.map_all f f_expr))
-- termination_by sizeOf u
-- decreasing_by
--   simp_wf
--   have := DelimitedNonEmpty.sizeOf_attach_elem updates x
--   omega
--
-- @[simp] theorem map_all_id {e α : Type} (u : RecordUpdateF e α) : map_all id id u = u := by
--   match u with
--   | .Leaf label token expr => simp only [map_all, id_eq]
--   | .Branch label updates =>
--     simp only [map_all, Branch.injEq, true_and]
--     have h : (fun x : { x // x ∈ updates } => x.val.map_all id id) = (fun x => x.val) := by
--       funext x; exact map_all_id x.val
--     rw [h, DelimitedNonEmpty.attach_map_val]
-- termination_by sizeOf u
-- decreasing_by
--   simp_wf
--   have := DelimitedNonEmpty.sizeOf_attach_elem updates x
--   omega
--
-- @[simp] theorem map_all_comp {e1 e2 e3 α β γ : Type} (f : e1 → e2) (g : e2 → e3) (f_expr : α → β) (g_expr : β → γ) (u : RecordUpdateF e1 α) :
--   map_all (g ∘ f) (g_expr ∘ f_expr) u = map_all g g_expr (map_all f f_expr u) := by
--   match u with
--   | .Leaf label token expr => simp only [map_all, Function.comp_apply]
--   | .Branch label updates =>
--     simp only [map_all, Branch.injEq, true_and]
--     have h : (fun x : { x // x ∈ updates } => x.val.map_all (g ∘ f) (g_expr ∘ f_expr)) = (fun x => (x.val.map_all f f_expr).map_all g g_expr) := by
--       funext x; exact map_all_comp f g f_expr g_expr x.val
--     rw [h]
--     rw [DelimitedNonEmpty.attach_map]
--     rw [← DelimitedNonEmpty.comp_map]
--     rfl
-- termination_by sizeOf u
-- decreasing_by
--   simp_wf
--   have := DelimitedNonEmpty.sizeOf_attach_elem updates x
--   omega
--
-- @[always_inline, inline] def map_expr_e {e α β : Type} [SizeOf e] [SizeOf α] (f : α → β) (u : RecordUpdateF e α) : RecordUpdateF e β :=
--   u.map_all id f
--
-- @[always_inline, inline] def map_e {e1 e2 α : Type} [SizeOf e1] [SizeOf α] (f : e1 → e2) (u : RecordUpdateF e1 α) : RecordUpdateF e2 α :=
--   u.map_all f id
--
-- @[simp] theorem map_expr_e_id {e α : Type} (u : RecordUpdateF e α) : map_expr_e id u = u := map_all_id u
-- @[simp] theorem map_expr_e_comp {e α β γ : Type} (f : α → β) (g : β → γ) (u : RecordUpdateF e α) : map_expr_e (g ∘ f) u = map_expr_e g (map_expr_e f u) := map_all_comp id id f g u
-- @[simp] theorem map_e_id {e α : Type} (u : RecordUpdateF e α) : map_e id u = u := map_all_id u
-- @[simp] theorem map_e_comp {e1 e2 e3 α : Type} (f : e1 → e2) (g : e2 → e3) (u : RecordUpdateF e1 α) : map_e (g ∘ f) u = map_e g (map_e f u) := map_all_comp f g id id u
--
-- instance : Functor (RecordUpdateF e) where map := map_expr_e
-- instance : LawfulFunctor (RecordUpdateF e) where
--   map_const := rfl
--   id_map := map_expr_e_id
--   comp_map := map_expr_e_comp
--
-- end RecordUpdateF
--
-- structure RecordAccessorF (expr_e : Type) where
--   expr : expr_e
--   dot : SourceToken
--   path : Separated (Name Label)
--   deriving Repr, BEq
--
-- namespace RecordAccessorF
--
-- @[always_inline, simp] def map {α β : Type} (f : α → β) (a : RecordAccessorF α) : RecordAccessorF β :=
--   { a with expr := f a.expr }
--
-- @[simp] theorem id_map {α : Type} (a : RecordAccessorF α) : (a.map id) = a := by
--   cases a; aesop
--
-- @[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (a : RecordAccessorF α) : (a.map (g ∘ f)) = (a.map f |>.map g) := by
--   cases a; aesop
--
-- @[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext a; exact id_map a
--
-- @[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext a; exact comp_map f g a
--
-- instance : Functor RecordAccessorF where map := map
-- instance : LawfulFunctor RecordAccessorF where
--   map_const := rfl
--   id_map := id_map
--   comp_map := comp_map
--
-- end RecordAccessorF
--
-- structure LambdaF (e expr_e : Type) where
--   symbol : SourceToken
--   binders : NonEmptyArray (Binder e)
--   arrow : SourceToken
--   body : expr_e
--   deriving Repr, BEq
--
-- namespace LambdaF
--
-- @[always_inline, simp] def map_all {e1 e2 α β : Type} (f : e1 → e2) (f_expr : α → β) (l : LambdaF e1 α) : LambdaF e2 β :=
--   { symbol := l.symbol
--     binders := l.binders.map (fun b => b.map f)
--     arrow := l.arrow
--     body := f_expr l.body
--   }
--
-- @[simp] theorem map_all_id {e α : Type} (l : LambdaF e α) : l.map_all id id = l := by
--   cases l; simp only [map_all, NonEmptyArray.map, Binder.map_id, Array.map_id_fun', id_eq]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 α β γ : Type} (f : e1 → e2) (g : e2 → e3) (f_expr : α → β) (g_expr : β → γ) (l : LambdaF e1 α) :
--   l.map_all (g ∘ f) (g_expr ∘ f_expr) = (l.map_all f f_expr).map_all g g_expr := by
--   cases l; simp only [map_all, NonEmptyArray.map, Binder.map_comp, Function.comp_apply,
--     Array.map_map, mk.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self]
--
-- @[always_inline, simp] def map_expr_e {e α β : Type} (f : α → β) (l : LambdaF e α) : LambdaF e β :=
--   l.map_all id f
--
-- @[always_inline, simp] def map_e {e1 e2 α : Type} (f : e1 → e2) (l : LambdaF e1 α) : LambdaF e2 α :=
--   l.map_all f id
--
-- end LambdaF
--
-- structure IfThenElseF (expr_e : Type) where
--   keyword : SourceToken
--   cond : expr_e
--   then_ : SourceToken
--   true_ : expr_e
--   else_ : SourceToken
--   false_ : expr_e
--   deriving Repr, BEq
--
-- namespace IfThenElseF
--
-- @[always_inline, simp] def map {α β : Type} (f : α → β) (i : IfThenElseF α) : IfThenElseF β :=
--   { i with cond := f i.cond, true_ := f i.true_, false_ := f i.false_ }
--
-- @[simp] theorem id_map {α : Type} (i : IfThenElseF α) : (i.map id) = i := by
--   cases i; aesop
--
-- @[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (i : IfThenElseF α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
--   cases i; aesop
--
-- @[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext i; exact id_map i
--
-- @[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i
--
-- instance : Functor IfThenElseF where map := map
-- instance : LawfulFunctor IfThenElseF where
--   map_const := rfl
--   id_map := id_map
--   comp_map := comp_map
--
-- end IfThenElseF
--
-- structure PatternGuardF (e expr_e : Type) where
--   binder : Option (Binder e × SourceToken)
--   expr : expr_e
--   deriving Repr, BEq
--
-- namespace PatternGuardF
--
-- @[always_inline, simp] def map_all {e1 e2 α β : Type} (f : e1 → e2) (f_expr : α → β) (p : PatternGuardF e1 α) : PatternGuardF e2 β :=
--   { binder := p.binder.map (fun (b, t) => (b.map f, t))
--     expr := f_expr p.expr
--   }
--
-- @[simp] theorem map_all_id {e α : Type} (p : PatternGuardF e α) : p.map_all id id = p := by
--   match p with
--   | { binder, expr } => simp only [map_all, Binder.map_id, Option.map_id_fun', id_eq]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 α β γ : Type} (f : e1 → e2) (g : e2 → e3) (f_expr : α → β) (g_expr : β → γ) (p : PatternGuardF e1 α) :
--   p.map_all (g ∘ f) (g_expr ∘ f_expr) = (p.map_all f f_expr).map_all g g_expr := by
--   match p with
--   | { binder, expr } =>
--     simp only [map_all, Binder.map_comp, Function.comp_apply, Option.map_map, mk.injEq, and_true]
--     apply congrArg (Option.map · binder); funext x; simp only [Function.comp_apply]
--
-- @[always_inline, simp] def map_expr_e {e α β : Type} (f : α → β) (p : PatternGuardF e α) : PatternGuardF e β :=
--   p.map_all id f
--
-- @[always_inline, simp] def map_e {e1 e2 α : Type} (f : e1 → e2) (p : PatternGuardF e1 α) : PatternGuardF e2 α :=
--   p.map_all f id
--
-- instance {e : Type} : Functor (PatternGuardF e) where map := map_expr_e
-- instance : LawfulFunctor (PatternGuardF e) where
--   map_const := rfl
--   id_map := map_all_id
--   comp_map f g x := map_all_comp id id f g x
--
-- end PatternGuardF
--
-- -- ```mermaid
-- -- graph TD
-- --     LB[LetBindingF] -->|Pattern| W[WhereF]
-- --     LB -->|Name| VBF[ValueBindingFieldsF]
-- --
-- --     VBF -->|guarded| G[GuardedF]
-- --
-- --     G -->|Unconditional| W
-- --     G -->|Guarded| GE[GuardedExprF]
-- --
-- --     GE -->|where_| W
-- --
-- --     W -->|bindings| LB
-- --
-- --     subgraph "The Mutual Cycle"
-- --     LB
-- --     VBF
-- --     G
-- --     GE
-- --     W
-- --     end
-- -- ```
--
-- -- 1. GuardExpr depends only on Where
-- structure GuardedExprF (e expr_e where_e : Type) where
--   bar        : SourceToken
--   patterns   : Separated (PatternGuardF e expr_e)
--   separator  : SourceToken
--   where_     : where_e
--   deriving Repr, BEq
--
-- namespace GuardedExprF
--
-- @[always_inline, simp] def map_all {e e' expr_e expr_e' where_e where_e' : Type}
--   (f : e → e') (f_expr : expr_e → expr_e') (f_where : where_e → where_e')
--   (g : GuardedExprF e expr_e where_e) : GuardedExprF e' expr_e' where_e' :=
--   { bar := g.bar
--     patterns := g.patterns.map (fun p => p.map_all f f_expr)
--     separator := g.separator
--     where_ := f_where g.where_
--   }
--
-- @[simp] theorem map_all_id {e expr_e where_e : Type} (g : GuardedExprF e expr_e where_e) : g.map_all id id id = g := by
--   match g with
--   | { bar, patterns, separator, where_ } => simp only [map_all, Separated.map,
--     PatternGuardF.map_all, Binder.map_id, Option.map_id_fun', id_eq, Array.map_id_fun']
--
-- @[simp] theorem map_all_comp {e1 e2 e3 expr_e1 expr_e2 expr_e3 where_e1 where_e2 where_e3 : Type}
--   (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
--   (f_where : where_e1 → where_e2) (g_where : where_e2 → where_e3)
--   (ge : GuardedExprF e1 expr_e1 where_e1) :
--   ge.map_all (g ∘ f) (g_expr ∘ f_expr) (g_where ∘ f_where) = (ge.map_all f f_expr f_where).map_all g g_expr g_where := by
--   match ge with
--   | { bar, patterns, separator, where_ } =>
--     simp only [map_all, Separated.map,
--       PatternGuardF.map_all, Binder.map_comp, Function.comp_apply, Option.map_map, Array.map_map,
--     mk.injEq, Separated.mk.injEq, PatternGuardF.mk.injEq, and_true, Array.map_inj_left,
--     Prod.mk.injEq, true_and, Prod.forall, and_self]
--     apply And.intro
--     · rfl
--     · intro a b a_1
--       rfl
--
-- end GuardedExprF
--
-- -- 2. Guarded depends on Where and GuardExpr
-- inductive GuardedF (where_e guardedExpr_e : Type) where
--   | Unconditional (token : SourceToken) (where_ : where_e)
--   | Guarded (branches : NonEmptyArray guardedExpr_e)
--   deriving Repr, BEq
--
-- namespace GuardedF
--
-- @[always_inline, simp] def map_all {where_e where_e' guardedExpr_e guardedExpr_e' : Type}
--   (f_where : where_e → where_e') (f_guardedExpr : guardedExpr_e → guardedExpr_e')
--   (g : GuardedF where_e guardedExpr_e) : GuardedF where_e' guardedExpr_e' :=
--   match g with
--   | Unconditional t w => Unconditional t (f_where w)
--   | Guarded b => Guarded (b.map f_guardedExpr)
--
-- @[simp] theorem map_all_id {where_e guardedExpr_e : Type} (g : GuardedF where_e guardedExpr_e) : g.map_all id id = g := by
--   match g with
--   | Unconditional t w => simp only [map_all, id_eq]
--   | Guarded b => simp only [map_all, NonEmptyArray.map, id_eq, Array.map_id_fun]
--
-- @[simp] theorem map_all_comp {where_e1 where_e2 where_e3 guardedExpr_e1 guardedExpr_e2 guardedExpr_e3 : Type}
--   (f_where : where_e1 → where_e2) (g_where : where_e2 → where_e3)
--   (f_guardedExpr : guardedExpr_e1 → guardedExpr_e2) (g_guardedExpr : guardedExpr_e2 → guardedExpr_e3)
--   (gr : GuardedF where_e1 guardedExpr_e1) :
--   gr.map_all (g_where ∘ f_where) (g_guardedExpr ∘ f_guardedExpr) = (gr.map_all f_where f_guardedExpr).map_all g_where g_guardedExpr := by
--   match gr with
--   | Unconditional t w => simp only [map_all, Function.comp_apply]
--   | Guarded b => simp only [map_all, NonEmptyArray.map, Function.comp_apply, Array.map_map]
--
-- end GuardedF
--
-- -- 3. ValueBindingFields depends on Guarded
-- structure ValueBindingFieldsF (e guardedExpr_e : Type) where
--   name    : Name Ident
--   binders : Array (Binder e)
--   guarded : guardedExpr_e
--   deriving Repr, BEq
--
-- namespace ValueBindingFieldsF
--
-- @[always_inline, simp] def map_all {e e' guardedExpr_e guardedExpr_e' : Type}
--   (f : e → e') (f_guardedExpr : guardedExpr_e → guardedExpr_e')
--   (v : ValueBindingFieldsF e guardedExpr_e) : ValueBindingFieldsF e' guardedExpr_e' :=
--   { name := v.name
--     binders := v.binders.map (fun b => b.map f)
--     guarded := f_guardedExpr v.guarded
--   }
--
-- @[simp] theorem map_all_id {e guardedExpr_e : Type} (v : ValueBindingFieldsF e guardedExpr_e) : v.map_all id id = v := by
--   match v with
--   | { name, binders, guarded } => simp only [map_all, Binder.map_id, Array.map_id_fun', id_eq]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 guardedExpr_e1 guardedExpr_e2 guardedExpr_e3 : Type}
--   (f : e1 → e2) (g : e2 → e3) (f_guardedExpr : guardedExpr_e1 → guardedExpr_e2) (g_guardedExpr : guardedExpr_e2 → guardedExpr_e3)
--   (v : ValueBindingFieldsF e1 guardedExpr_e1) :
--   v.map_all (g ∘ f) (g_guardedExpr ∘ f_guardedExpr) = (v.map_all f f_guardedExpr).map_all g g_guardedExpr := by
--   match v with
--   | { name, binders, guarded } => simp only [map_all, Binder.map_comp, Function.comp_apply,
--     Array.map_map, mk.injEq, Array.map_inj_left, implies_true, and_self]
--
-- end ValueBindingFieldsF
-- -- 4. Where depends on the list of Bindings
-- structure WhereF (e expr_e letBinding_e : Type) where
--   expr     : expr_e
--   bindings : Option (SourceToken × NonEmptyArray letBinding_e)
--   deriving Repr, BEq
--
-- namespace WhereF
--
-- @[always_inline, simp] def map_all {e e' expr_e expr_e' letBinding_e letBinding_e' : Type}
--   (f : e → e') (f_expr : expr_e → expr_e') (f_letBinding : letBinding_e → letBinding_e')
--   (w : WhereF e expr_e letBinding_e) : WhereF e' expr_e' letBinding_e' :=
--   { expr := f_expr w.expr
--     bindings := w.bindings.map (fun (t, b) => (t, b.map f_letBinding))
--   }
--
-- @[simp] theorem map_all_id {e expr_e letBinding_e : Type} (w : WhereF e expr_e letBinding_e) : w.map_all id id id = w := by
--   match w with
--   | { expr, bindings } => simp only [map_all, id_eq, NonEmptyArray.map, Array.map_id_fun,
--     Option.map_id_fun']
--
-- @[simp] theorem map_all_comp {e1 e2 e3 expr_e1 expr_e2 expr_e3 letBinding_e1 letBinding_e2 letBinding_e3 : Type}
--   (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
--   (f_letBinding : letBinding_e1 → letBinding_e2) (g_letBinding : letBinding_e2 → letBinding_e3)
--   (w : WhereF e1 expr_e1 letBinding_e1) :
--   w.map_all (g ∘ f) (g_expr ∘ f_expr) (g_letBinding ∘ f_letBinding) = (w.map_all f f_expr f_letBinding).map_all g g_expr g_letBinding := by
--   match w with
--   | { expr, bindings } =>
--     simp_all only [map_all, Function.comp_apply, NonEmptyArray.map, Option.map_map, mk.injEq, true_and]
--     ext a : 1
--     simp_all only [Option.map_eq_some_iff, Prod.exists, Function.comp_apply, Array.map_map]
--
-- end WhereF
--
-- -- 5. LetBinding is the "Sum" of the complex
-- inductive LetBindingF (e expr_e valueBindingFields_e where_e : Type) where
--   | Signature (labeled : Labeled (Name Ident) (Type_ e))
--   | Name (fields : valueBindingFields_e)
--   | Pattern (binder : Binder e) (token : SourceToken) (where_ : where_e)
--   | Error (data : e)
--   deriving Repr, BEq
--
-- namespace LetBindingF
--
-- @[always_inline, simp] def map_all {e e' expr_e expr_e' valueBindingFields_e valueBindingFields_e' where_e where_e' : Type}
--   (f : e → e') (f_expr : expr_e → expr_e') (f_valueBindingFields : valueBindingFields_e → valueBindingFields_e') (f_where : where_e → where_e')
--   (b : LetBindingF e expr_e valueBindingFields_e where_e) : LetBindingF e' expr_e' valueBindingFields_e' where_e' :=
--   match b with
--   | Signature l => Signature (l.map (fun t => t.map f))
--   | Name fields => Name (f_valueBindingFields fields)
--   | Pattern b' t w => Pattern (b'.map f) t (f_where w)
--   | Error d => Error (f d)
--
-- @[simp] theorem map_all_id {e expr_e valueBindingFields_e where_e : Type} (b : LetBindingF e expr_e valueBindingFields_e where_e) : b.map_all id id id id = b := by
--   match b with
--   | Signature l =>
--     simp_all only [map_all, Function.const_apply, Signature.injEq]
--     aesop?
--   | Name fields => simp only [map_all, id_eq]
--   | Pattern b' t w => simp only [map_all, Binder.map_id, id_eq]
--   | Error d => simp only [map_all, id_eq]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 expr_e1 expr_e2 expr_e3 valueBindingFields_e1 valueBindingFields_e2 valueBindingFields_e3 where_e1 where_e2 where_e3 : Type}
--   (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
--   (f_valueBindingFields : valueBindingFields_e1 → valueBindingFields_e2) (g_valueBindingFields : valueBindingFields_e2 → valueBindingFields_e3)
--   (f_where : where_e1 → where_e2) (g_where : where_e2 → where_e3)
--   (lb : LetBindingF e1 expr_e1 valueBindingFields_e1 where_e1) :
--   lb.map_all (g ∘ f) (g_expr ∘ f_expr) (g_valueBindingFields ∘ f_valueBindingFields) (g_where ∘ f_where) = (lb.map_all f f_expr f_valueBindingFields f_where).map_all g g_expr g_valueBindingFields g_where := by
--   match lb with
--   | Signature l => simp only [map_all, Function.const_apply]
--   | Name fields => simp only [map_all, Function.comp_apply]
--   | Pattern b' t w => simp only [map_all, Binder.map_comp, Function.comp_apply]
--   | Error d => simp only [map_all, Function.comp_apply]
--
-- end LetBindingF
--
-- structure CaseOfF (e expr_e guardedRecursive_e : Type) where
--   keyword : SourceToken
--   head : Separated expr_e
--   of : SourceToken
--   branches : NonEmptyArray (Separated (Binder e) × guardedRecursive_e)
--   deriving Repr, BEq
--
-- namespace CaseOfF
--
-- @[always_inline, simp] def map_all {e e' expr_e expr_e' guardedRecursive_e guardedRecursive_e' : Type}
--   (f : e → e') (f_expr : expr_e → expr_e') (f_guardedRecursive : guardedRecursive_e → guardedRecursive_e')
--   (c : CaseOfF e expr_e guardedRecursive_e) : CaseOfF e' expr_e' guardedRecursive_e' :=
--   { keyword := c.keyword
--     head := c.head.map f_expr
--     of := c.of
--     branches := c.branches.map (fun (b, g) => (b.map (fun b' => b'.map f), f_guardedRecursive g))
--   }
--
-- @[simp] theorem map_all_id {e expr_e guardedRecursive_e : Type} (c : CaseOfF e expr_e guardedRecursive_e) : c.map_all id id id = c := by
--   match c with
--   | { keyword, head, of, branches } => simp only [map_all, Separated.map, id_eq, Array.map_id_fun',
--     NonEmptyArray.map, Binder.map_id]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 expr_e1 expr_e2 expr_e3 guardedRecursive_e1 guardedRecursive_e2 guardedRecursive_e3 : Type}
--   (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
--   (f_guardedRecursive : guardedRecursive_e1 → guardedRecursive_e2) (g_guardedRecursive : guardedRecursive_e2 → guardedRecursive_e3)
--   (c : CaseOfF e1 expr_e1 guardedRecursive_e1) :
--   c.map_all (g ∘ f) (g_expr ∘ f_expr) (g_guardedRecursive ∘ f_guardedRecursive) = (c.map_all f f_expr f_guardedRecursive).map_all g g_expr g_guardedRecursive := by
--   match c with
--   | { keyword, head, of, branches } => simp only [map_all, Separated.map, Function.comp_apply,
--     NonEmptyArray.map, Binder.map_comp, Array.map_map, mk.injEq, Separated.mk.injEq,
--     Array.map_inj_left, implies_true, and_self, NonEmptyArray.mk.injEq, Prod.mk.injEq]
--
-- end CaseOfF
--
-- structure LetInF (e expr_e letBindingRecursive_e : Type) where
--   keyword : SourceToken
--   bindings : NonEmptyArray letBindingRecursive_e
--   in_ : SourceToken
--   body : expr_e
--   deriving Repr, BEq
--
-- namespace LetInF
--
-- @[always_inline, simp] def map_all {e e' expr_e expr_e' letBindingRecursive_e letBindingRecursive_e' : Type}
--   (f : e → e') (f_expr : expr_e → expr_e') (f_letBindingRecursive : letBindingRecursive_e → letBindingRecursive_e')
--   (l : LetInF e expr_e letBindingRecursive_e) : LetInF e' expr_e' letBindingRecursive_e' :=
--   { keyword := l.keyword
--     bindings := l.bindings.map f_letBindingRecursive
--     in_ := l.in_
--     body := f_expr l.body
--   }
--
-- @[simp] theorem map_all_id {e expr_e letBindingRecursive_e : Type} (l : LetInF e expr_e letBindingRecursive_e) : l.map_all id id id = l := by
--   match l with
--   | { keyword, bindings, in_, body } => simp only [map_all, NonEmptyArray.map, id_eq,
--     Array.map_id_fun]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 expr_e1 expr_e2 expr_e3 letBindingRecursive_e1 letBindingRecursive_e2 letBindingRecursive_e3 : Type}
--   (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
--   (f_letBindingRecursive : letBindingRecursive_e1 → letBindingRecursive_e2) (g_letBindingRecursive : letBindingRecursive_e2 → letBindingRecursive_e3)
--   (l : LetInF e1 expr_e1 letBindingRecursive_e1) :
--   l.map_all (g ∘ f) (g_expr ∘ f_expr) (g_letBindingRecursive ∘ f_letBindingRecursive) = (l.map_all f f_expr f_letBindingRecursive).map_all g g_expr g_letBindingRecursive := by
--   match l with
--   | { keyword, bindings, in_, body } => simp only [map_all, NonEmptyArray.map, Function.comp_apply,
--     Array.map_map]
--
-- end LetInF
--
-- inductive DoStatementF (e expr_e letBindingRecursive_e : Type)
--   | Let (token : SourceToken) (bindings : NonEmptyArray letBindingRecursive_e)
--   | Discard (expr : expr_e)
--   | Bind (binder : Binder e) (token : SourceToken) (expr : expr_e)
--   | Error (data : e)
--   deriving Repr, BEq
--
-- namespace DoStatementF
--
-- @[always_inline, simp] def map_all {e e' expr_e expr_e' letBindingRecursive_e letBindingRecursive_e' : Type}
--   (f : e → e') (f_expr : expr_e → expr_e') (f_letBindingRecursive : letBindingRecursive_e → letBindingRecursive_e')
--   (s : DoStatementF e expr_e letBindingRecursive_e) : DoStatementF e' expr_e' letBindingRecursive_e' :=
--   match s with
--   | Let t b => Let t (b.map f_letBindingRecursive)
--   | Discard expr => Discard (f_expr expr)
--   | Bind b t expr => Bind (b.map f) t (f_expr expr)
--   | Error d => Error (f d)
--
-- @[simp] theorem map_all_id {e expr_e letBindingRecursive_e : Type} (s : DoStatementF e expr_e letBindingRecursive_e) : s.map_all id id id = s := by
--   match s with
--   | Let t b => simp only [map_all, NonEmptyArray.map, id_eq, Array.map_id_fun]
--   | Discard expr => simp only [map_all, id_eq]
--   | Bind b' t expr => simp only [map_all, Binder.map_id, id_eq]
--   | Error d => simp only [map_all, id_eq]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 expr_e1 expr_e2 expr_e3 letBindingRecursive_e1 letBindingRecursive_e2 letBindingRecursive_e3 : Type}
--   (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
--   (f_letBindingRecursive : letBindingRecursive_e1 → letBindingRecursive_e2) (g_letBindingRecursive : letBindingRecursive_e2 → letBindingRecursive_e3)
--   (s : DoStatementF e1 expr_e1 letBindingRecursive_e1) :
--   s.map_all (g ∘ f) (g_expr ∘ f_expr) (g_letBindingRecursive ∘ f_letBindingRecursive) = (s.map_all f f_expr f_letBindingRecursive).map_all g g_expr g_letBindingRecursive := by
--   match s with
--   | Let t b => simp only [map_all, NonEmptyArray.map, Function.comp_apply, Array.map_map]
--   | Discard expr => simp only [map_all, Function.comp_apply]
--   | Bind b' t expr => simp only [map_all, Binder.map_comp, Function.comp_apply]
--   | Error d => simp only [map_all, Function.comp_apply]
--
-- end DoStatementF
--
-- structure DoBlockF (doStatement_e : Type) where
--   keyword : SourceToken
--   statements : NonEmptyArray doStatement_e
--   deriving Repr, BEq
--
-- namespace DoBlockF
--
-- @[always_inline, simp] def map_all {doStatement_e doStatement_e' : Type}
--   (f_doStatement : doStatement_e → doStatement_e')
--   (b : DoBlockF doStatement_e) : DoBlockF doStatement_e' :=
--   { keyword := b.keyword
--     statements := b.statements.map f_doStatement
--   }
--
-- @[simp] theorem map_all_id {doStatement_e : Type} (b : DoBlockF doStatement_e) : b.map_all id = b := by
--   match b with
--   | { keyword, statements } => simp only [map_all, NonEmptyArray.map, id_eq, Array.map_id_fun]
--
-- @[simp] theorem map_all_comp {doStatement_e1 doStatement_e2 doStatement_e3 : Type}
--   (f_doStatement : doStatement_e1 → doStatement_e2) (g_doStatement : doStatement_e2 → doStatement_e3)
--   (b : DoBlockF doStatement_e1) :
--   b.map_all (g_doStatement ∘ f_doStatement) = (b.map_all f_doStatement).map_all g_doStatement := by
--   match b with
--   | { keyword, statements } => simp only [map_all, NonEmptyArray.map, Function.comp_apply,
--     Array.map_map]
--
-- end DoBlockF
--
-- structure AdoBlockF (expr_e doStatement_e : Type) where
--   keyword : SourceToken
--   statements : Array doStatement_e
--   in_ : SourceToken
--   result : expr_e
--   deriving Repr, BEq
--
-- namespace AdoBlockF
--
-- @[always_inline, simp] def map_all {expr_e expr_e' doStatement_e doStatement_e' : Type}
--   (f_expr : expr_e → expr_e') (f_doStatement : doStatement_e → doStatement_e')
--   (b : AdoBlockF expr_e doStatement_e) : AdoBlockF expr_e' doStatement_e' :=
--   { keyword := b.keyword
--     statements := b.statements.map f_doStatement
--     in_ := b.in_
--     result := f_expr b.result
--   }
--
-- @[simp] theorem map_all_id {expr_e doStatement_e : Type} (b : AdoBlockF expr_e doStatement_e) : b.map_all id id = b := by
--   match b with
--   | { keyword, statements, in_, result } => simp only [map_all, Array.map_id_fun, id_eq]
--
-- @[simp] theorem map_all_comp {expr_e1 expr_e2 expr_e3 doStatement_e1 doStatement_e2 doStatement_e3 : Type}
--   (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
--   (f_doStatement : doStatement_e1 → doStatement_e2) (g_doStatement : doStatement_e2 → doStatement_e3)
--   (b : AdoBlockF expr_e1 doStatement_e1) :
--   b.map_all (g_expr ∘ f_expr) (g_doStatement ∘ f_doStatement) = (b.map_all f_expr f_doStatement).map_all g_expr g_doStatement := by
--   match b with
--   | { keyword, statements, in_, result } => simp only [map_all, Function.comp_apply, Array.map_map]
--
-- end AdoBlockF
--
-- inductive ExprF (e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e : Type)
--   | Hole (name : Name Ident)
--   | Section (token : SourceToken)
--   | Ident (name : QualifiedName Ident)
--   | Constructor (name : QualifiedName Proper)
--   | Boolean (token : SourceToken) (val : Bool)
--   | Char (token : SourceToken) (val : Char)
--   | NonEmptyString (token : SourceToken) (val : NonEmptyString)
--   | Int (token : SourceToken) (val : IntValue)
--   | Number (token : SourceToken) (val : Float)
--   | Array (items : Delimited expr_e)
--   | Record (fields : Delimited (RecordLabeled expr_e))
--   | Parens (wrapped : Wrapped expr_e)
--   | Typed (expr : expr_e) (token : SourceToken) (type_ : Type_ e)
--   | Infix (head : expr_e) (tail : NonEmptyArray (Wrapped expr_e × expr_e))
--   | Op (head : expr_e) (ops : NonEmptyArray (QualifiedName Operator × expr_e))
--   | OpName (name : QualifiedName Operator)
--   | Negate (token : SourceToken) (expr : expr_e)
--   | RecordAccessor (data : RecordAccessorF expr_e)
--   | RecordUpdate (expr : expr_e) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
--   | App (fn : expr_e) (args : NonEmptyArray (AppSpineF e expr_e))
--   | Lambda (data : LambdaF e expr_e)
--   | If (data : IfThenElseF expr_e)
--   | Case (data : CaseOfF e expr_e guardedRecursive_e)
--   | Let (data : LetInF e expr_e letBindingRecursive_e)
--   | Do (data : doBlock)
--   | Ado (data : adoBlock)
--   | Error (data : e)
--   deriving Repr, BEq
--
-- namespace ExprF
--
-- @[always_inline, simp] def map_all {e e' expr_e expr_e' doBlock doBlock' adoBlock adoBlock' guardedRecursive_e guardedRecursive_e' letBindingRecursive_e letBindingRecursive_e' : Type}
--   (f : e → e') (f_expr : expr_e → expr_e') (f_doBlock : doBlock → doBlock') (f_adoBlock : adoBlock → adoBlock')
--   (f_guardedRecursive : guardedRecursive_e → guardedRecursive_e') (f_letBindingRecursive : letBindingRecursive_e → letBindingRecursive_e')
--   (expr : ExprF e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e) : ExprF e' expr_e' doBlock' adoBlock' guardedRecursive_e' letBindingRecursive_e' :=
--   match expr with
--   | Hole n => Hole n
--   | Section t => Section t
--   | Ident n => Ident n
--   | Constructor n => Constructor n
--   | Boolean t v => Boolean t v
--   | Char t v => Char t v
--   | NonEmptyString t v => NonEmptyString t v
--   | Int t v => Int t v
--   | Number t v => Number t v
--   | Array items => Array (items.map f_expr)
--   | Record fields => Record (fields.map (fun r => r.map f_expr))
--   | Parens wrapped => Parens (wrapped.map f_expr)
--   | Typed e' t ty => Typed (f_expr e') t (ty.map f)
--   | Infix h t => Infix (f_expr h) (t.map (fun (w, e') => (w.map_expr_e f_expr, f_expr e')))
--   | Op h o => Op (f_expr h) (o.map (fun (n, e') => (n, f_expr e')))
--   | OpName n => OpName n
--   | Negate t e' => Negate t (f_expr e')
--   | RecordAccessor data => RecordAccessor (data.map f_expr)
--   | RecordUpdate e' updates => RecordUpdate (f_expr e') (updates.map (fun u => u.map_all f f_expr))
--   | App fn args => App (f_expr fn) (args.map (fun a => a.map_all f f_expr))
--   | Lambda data => Lambda (data.map_all f f_expr)
--   | If data => If (data.map f_expr)
--   | Case data => Case (data.map_all f f_expr f_guardedRecursive)
--   | Let data => Let (data.map_all f f_expr f_letBindingRecursive)
--   | Do data => Do (f_doBlock data)
--   | Ado data => Ado (f_adoBlock data)
--   | Error d => Error (f d)
--
-- @[simp] theorem map_all_id {e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e : Type}
--   (expr : ExprF e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e) :
--   expr.map_all id id id id id id = expr := by
--   match expr with
--   | Hole n => simp only [map_all]
--   | Section t => simp only [map_all]
--   | Ident n => simp only [map_all]
--   | Constructor n => simp only [map_all]
--   | Boolean t v => simp only [map_all]
--   | Char t v => simp only [map_all]
--   | NonEmptyString t v => simp only [map_all]
--   | Int t v => simp only [map_all]
--   | Number t v => simp only [map_all]
--   | Array items => simp only [map_all, Delimited.map, Separated.map_id_fun, id_map]
--   | Record fields =>
--     simp only [map_all, Delimited.map, RecordLabeled.map, id_eq, Option.map_eq_map,
--     Record.injEq]
--     aesop?
--   | Parens wrapped => simp only [map_all, Wrapped.map, id_eq]
--   | Typed e' t ty => simp only [map_all, id_eq, Type_.map_id]
--   | Infix h t =>
--     simp only [map_all, id_eq, NonEmptyArray.map, Function.const_apply, Infix.injEq,
--     true_and]
--     aesop?
--   | Op h o => simp only [map_all, id_eq, NonEmptyArray.map, Array.map_id_fun']
--   | OpName n => simp only [map_all]
--   | Negate t e' => simp only [map_all, id_eq]
--   | RecordAccessor data => simp only [map_all, RecordAccessorF.map, id_eq]
--   | RecordUpdate e' updates => simp only [map_all, id_eq, DelimitedNonEmpty.map, Separated.map,
--     RecordUpdateF.map_all_id, Array.map_id_fun']
--   | App fn args =>
--     simp only [map_all, id_eq, NonEmptyArray.map, AppSpineF.map_all, Type_.map_id,
--     App.injEq, true_and]
--     split
--     next s e_1 heq =>
--       ext : 1
--       · simp_all only
--       · ext i hi₁ hi₂ : 1
--         · simp_all only [Array.size_map]
--         · simp_all only [Array.getElem_map]
--           split
--           next s_1 e_2 heq_1 => simp_all only
--           next s_1 t ty heq_1 => simp_all only
--     next s t ty heq =>
--       ext : 1
--       · simp_all only
--       · ext i hi₁ hi₂ : 1
--         · simp_all only [Array.size_map]
--         · simp_all only [Array.getElem_map]
--           split
--           next s_1 e_1 heq_1 => simp_all only
--           next s_1 t_1 ty_1 heq_1 => simp_all only
--   | Lambda data => simp only [map_all, LambdaF.map_all, NonEmptyArray.map, Binder.map_id,
--     Array.map_id_fun', id_eq]
--   | If data => simp only [map_all, IfThenElseF.map, id_eq]
--   | Case data => simp only [map_all, CaseOfF.map_all, Separated.map, id_eq, Array.map_id_fun',
--     NonEmptyArray.map, Binder.map_id]
--   | Let data => simp only [map_all, LetInF.map_all, NonEmptyArray.map, id_eq, Array.map_id_fun]
--   | Do data => simp only [map_all, id_eq]
--   | Ado data => simp only [map_all, id_eq]
--   | Error d => simp only [map_all, id_eq]
--
-- @[simp] theorem map_all_comp {e1 e2 e3 expr_e1 expr_e2 expr_e3 doBlock1 doBlock2 doBlock3 adoBlock1 adoBlock2 adoBlock3 guardedRecursive_e1 guardedRecursive_e2 guardedRecursive_e3 letBindingRecursive_e1 letBindingRecursive_e2 letBindingRecursive_e3 : Type}
--   (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
--   (f_doBlock : doBlock1 → doBlock2) (g_doBlock : doBlock2 → doBlock3)
--   (f_adoBlock : adoBlock1 → adoBlock2) (g_adoBlock : adoBlock2 → adoBlock3)
--   (f_guardedRecursive : guardedRecursive_e1 → guardedRecursive_e2) (g_guardedRecursive : guardedRecursive_e2 → guardedRecursive_e3)
--   (f_letBindingRecursive : letBindingRecursive_e1 → letBindingRecursive_e2) (g_letBindingRecursive : letBindingRecursive_e2 → letBindingRecursive_e3)
--   (expr : ExprF e1 expr_e1 doBlock1 adoBlock1 guardedRecursive_e1 letBindingRecursive_e1) :
--   expr.map_all (g ∘ f) (g_expr ∘ f_expr) (g_doBlock ∘ f_doBlock) (g_adoBlock ∘ f_adoBlock) (g_guardedRecursive ∘ f_guardedRecursive) (g_letBindingRecursive ∘ f_letBindingRecursive) =
--   (expr.map_all f f_expr f_doBlock f_adoBlock f_guardedRecursive f_letBindingRecursive).map_all g g_expr g_doBlock g_adoBlock g_guardedRecursive g_letBindingRecursive := by
--   match expr with
--   | Hole n => simp only [map_all]
--   | Section t => simp only [map_all]
--   | Ident n => simp only [map_all]
--   | Constructor n => simp only [map_all]
--   | Boolean t v => simp only [map_all]
--   | Char t v => simp only [map_all]
--   | NonEmptyString t v => simp only [map_all]
--   | Int t v => simp only [map_all]
--   | Number t v => simp only [map_all]
--   | Array items => simp only [map_all, Delimited.map, Separated.map_comp_fun, comp_map,
--     Option.map_eq_map, Option.map_map]
--   | Record fields =>
--     simp only [map_all, Delimited.map, RecordLabeled.map, Function.comp_apply,
--     Option.map_eq_map, Option.map_map, Record.injEq, Delimited.mk.injEq, Wrapped.mk.injEq, and_true,
--     true_and]
--     ext a : 1
--     simp_all only [Option.map_eq_some_iff, Separated.map, Function.comp_apply, Array.map_map]
--     apply Iff.intro
--     · intro a_1
--       obtain ⟨w, h⟩ := a_1
--       obtain ⟨left, right⟩ := h
--       subst right
--       simp_all only [Option.some.injEq, Separated.mk.injEq, exists_eq_left', Array.map_inj_left, Function.comp_apply,
--         Prod.mk.injEq, true_and, Prod.forall]
--       split
--       next r n heq =>
--         split
--         next r_1 n_1 heq_1 =>
--           simp_all only [RecordLabeled.Pun.injEq, true_and]
--           intro a b a_1
--           subst heq
--           split
--           next r_2 n heq =>
--             split
--             next r_3 n_2 => simp_all only [RecordLabeled.Pun.injEq]
--             next r_3 l sep v => simp_all only [reduceCtorEq]
--           next r_2 l sep v heq =>
--             split
--             next r_3 n => simp_all only [reduceCtorEq]
--             next r_3 l_1 sep_1 v_1 => simp_all only [RecordLabeled.Field.injEq]
--         next r_1 l sep v heq_1 => simp_all only [reduceCtorEq]
--       next r l sep v heq =>
--         split
--         next r_1 n heq_1 => simp_all only [reduceCtorEq]
--         next r_1 l_1 sep_1 v_1 heq_1 =>
--           simp_all only [RecordLabeled.Field.injEq, true_and]
--           intro a b a_1
--           obtain ⟨left_1, right⟩ := heq
--           obtain ⟨left_2, right⟩ := right
--           subst left_1 left_2 right
--           split
--           next r_2 n heq =>
--             split
--             next r_3 n_1 => simp_all only [RecordLabeled.Pun.injEq]
--             next r_3 l sep v => simp_all only [reduceCtorEq]
--           next r_2 l sep v heq =>
--             split
--             next r_3 n => simp_all only [reduceCtorEq]
--             next r_3 l_2 sep_2 v_2 => simp_all only [RecordLabeled.Field.injEq]
--     · intro a_1
--       obtain ⟨w, h⟩ := a_1
--       obtain ⟨left, right⟩ := h
--       subst right
--       simp_all only [Option.some.injEq, Separated.mk.injEq, exists_eq_left', Array.map_inj_left, Function.comp_apply,
--         Prod.mk.injEq, true_and, Prod.forall]
--       split
--       next r n heq =>
--         simp_all only [true_and]
--         intro a b a_1
--         split
--         next r_1 n_1 => simp_all only
--         next r_1 l sep v => simp_all only
--       next r l sep v heq =>
--         simp_all only [true_and]
--         intro a b a_1
--         split
--         next r_1 n => simp_all only
--         next r_1 l_1 sep_1 v_1 => simp_all only
--   | Parens wrapped => simp only [map_all, Wrapped.map, Function.comp_apply]
--   | Typed e' t ty => simp only [map_all, Function.comp_apply, Type_.map_comp]
--   | Infix h t => simp only [map_all, Function.comp_apply, NonEmptyArray.map, Function.const_apply,
--     Array.map_map, Infix.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self]
--   | Op h o => simp only [map_all, Function.comp_apply, NonEmptyArray.map, Array.map_map, Op.injEq,
--     NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self]
--   | OpName n => simp only [map_all]
--   | Negate t e' => simp only [map_all, Function.comp_apply]
--   | RecordAccessor data => simp only [map_all, RecordAccessorF.map, Function.comp_apply]
--   | RecordUpdate e' updates => simp only [map_all, Function.comp_apply, DelimitedNonEmpty.map,
--     Separated.map, RecordUpdateF.map_all_comp, Array.map_map, RecordUpdate.injEq,
--     DelimitedNonEmpty.mk.injEq, Wrapped.mk.injEq, Separated.mk.injEq, Array.map_inj_left,
--     implies_true, and_self]
--   | App fn args =>
--     simp only [map_all, Function.comp_apply, NonEmptyArray.map, AppSpineF.map_all,
--     Type_.map_comp, Array.map_map, App.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, true_and]
--     split
--     next s e heq =>
--       simp_all only [true_and]
--       intro a a_1
--       split
--       next s_1 e_1 => simp_all only
--       next s_1 t ty => simp_all only
--     next s t ty heq =>
--       simp_all only [true_and]
--       intro a a_1
--       split
--       next s_1 e => simp_all only
--       next s_1 t_1 ty_1 => simp_all only
--   | Lambda data => simp only [map_all, LambdaF.map_all, NonEmptyArray.map, Binder.map_comp,
--     Function.comp_apply, Array.map_map, Lambda.injEq, LambdaF.mk.injEq, NonEmptyArray.mk.injEq,
--     Array.map_inj_left, implies_true, and_self]
--   | If data => simp only [map_all, IfThenElseF.map, Function.comp_apply]
--   | Case data => simp only [map_all, CaseOfF.map_all, Separated.map, Function.comp_apply,
--     NonEmptyArray.map, Binder.map_comp, Array.map_map, Case.injEq, CaseOfF.mk.injEq,
--     Separated.mk.injEq, Array.map_inj_left, implies_true, and_self, NonEmptyArray.mk.injEq,
--     Prod.mk.injEq]
--   | Let data => simp only [map_all, LetInF.map_all, NonEmptyArray.map, Function.comp_apply,
--     Array.map_map]
--   | Do data => simp only [map_all, Function.comp_apply]
--   | Ado data => simp only [map_all, Function.comp_apply]
--   | Error d => simp only [map_all, Function.comp_apply]
--
-- end ExprF
--
-- -- https://github.com/leanprover/lean4/issues/13465#issuecomment-4349653768
-- -- mutual
--
-- -- inductive LetBindingRecursive (e : Type) where
-- --   | mk : LetBindingF e (Expr e)
-- --       (ValueBindingFieldsRecursive e)
-- --       (WhereRecursive e)
-- --     → LetBindingRecursive e
-- --   deriving Repr, BEq
--
-- -- inductive WhereRecursive (e : Type) where
-- --   | mk : WhereF e (Expr e) (LetBindingRecursive e) → WhereRecursive e
-- --   deriving Repr, BEq
--
-- -- inductive GuardedRecursive (e : Type) where
-- --   | mk : GuardedF e (Expr e)
-- --       (WhereRecursive e)
-- --       (GuardedRecursive e)
-- --     → GuardedRecursive e
-- --   deriving Repr, BEq
--
-- -- inductive ValueBindingFieldsRecursive (e : Type) where
-- --   | mk : ValueBindingFieldsF e (Expr e) (GuardedRecursive e)
-- --     → ValueBindingFieldsRecursive e
-- --   deriving Repr, BEq
--
-- -- inductive DoStatementRecursive (e : Type)
-- --   | mk : DoStatementF e (Expr e) (LetBindingRecursive e) → DoStatementRecursive e
-- --   deriving Repr, BEq
--
-- -- inductive DoBlockRecursive (e : Type)
-- --   | mk : DoBlockF e (Expr e) (DoStatementRecursive e) → DoBlockRecursive e
-- --   deriving Repr, BEq
--
-- -- inductive AdoBlockRecursive (e : Type)
-- --   | mk : AdoBlockF e (Expr e) (DoStatementRecursive e) → AdoBlockRecursive e
-- --   deriving Repr, BEq
--
-- -- inductive Expr (e : Type)
-- --   | mk : ExprF e (Expr e) (DoBlockRecursive e) (AdoBlockRecursive e) (LetBindingRecursive e) (GuardedRecursive e) → Expr e
-- --   deriving Repr, BEq
-- -- end
-- -----------------------------------------------------------------------------------------------------------
--
-- -- inductive InstanceBinding (e : Type)
-- --   | Signature (labeled : Labeled (Name Ident) (Type_ e))
-- --   | Name (fields : ValueBindingFieldsRecursive e)
-- --   deriving Repr, BEq
--
-- -- namespace InstanceBinding
--
-- -- @[always_inline, simp] def map {α β : Type} (f : α → β) (i : InstanceBinding α) : InstanceBinding β :=
-- --   match i with
-- --   | Signature l => Signature (l.map (fun t => t.map f))
-- --   | Name fields => Name (fields.map f)
--
-- -- @[simp] theorem map_id {e : Type} (i : InstanceBinding e) : i.map id = i := by
-- --   cases i <;> simp? [map, id_map, ValueBindingFields.map_id]
--
-- -- @[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (i : InstanceBinding e1) : i.map (g ∘ f) = (i.map f).map g := by
-- --   cases i <;> simp? [map, comp_map, ValueBindingFields.map_comp]
--
-- -- instance : Functor InstanceBinding where map := map
-- -- instance : LawfulFunctor InstanceBinding where
-- --   map_const := rfl
-- --   id_map := map_id
-- --   comp_map := map_comp
--
-- -- end InstanceBinding
--
-- -- structure Instance (e : Type) where
-- --   head : InstanceHead e
-- --   body : Option (SourceToken × NonEmptyArray (InstanceBinding e))
-- --   deriving Repr, BEq
--
-- -- namespace Instance
--
-- -- @[always_inline, simp] def map {α β : Type} (f : α → β) (i : Instance α) : Instance β :=
-- --   { head := i.head.map f
-- --     body := i.body.map (fun (t, b) => (t, b.map (fun b' => b'.map f)))
-- --   }
--
-- -- @[simp] theorem map_id {e : Type} (i : Instance e) : i.map id = i := by
-- --   cases i; simp? [map, id_map]
--
-- -- @[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (i : Instance e1) : i.map (g ∘ f) = (i.map f).map g := by
-- --   cases i; simp? [map, comp_map]
--
-- -- instance : Functor Instance where map := map
-- -- instance : LawfulFunctor Instance where
-- --   map_const := rfl
-- --   id_map := map_id
-- --   comp_map := map_comp
--
-- -- end Instance
--
-- inductive Foreign (e : Type)
--   | Value (labeled : Labeled (Name Ident) (Type_ e))
--   | Data (keyword : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
--   | Kind (keyword : SourceToken) (name : Name Proper)
--   deriving Repr, BEq
--
-- namespace Foreign
--
-- @[always_inline, simp] def map {α β : Type} (f : α → β) (o : Foreign α) : Foreign β :=
--   match o with
--   | .Value l => .Value (Functor.map (Functor.map f) l)
--   | .Data k l => .Data k (Functor.map (Functor.map f) l)
--   | .Kind k n => .Kind k n
--
-- @[simp] theorem id_map {α : Type} (o : Foreign α) : (o.map id) = o := by
--   cases o <;> aesop
--
-- @[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (o : Foreign α) : (o.map (g ∘ f)) = (o.map f |>.map g) := by
--   cases o <;> aesop
--
-- @[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext o; exact id_map o
--
-- @[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext o; exact comp_map f g o
--
-- -- mutual
-- --   def LetBinding.map {e1 e2 : Type} (f : e1 → e2) : LetBinding e1 → LetBinding e2
-- --     | .mk bf => .mk (bf.map_all f (Expr.map f) (ValueBindingFields.map f) (Where.map f))
--
-- --   def Where.map {e1 e2 : Type} (f : e1 → e2) : Where e1 → Where e2
-- --     | .mk wf => .mk (wf.map_all f (Expr.map f) (LetBinding.map f))
--
-- --   def Guarded.map {e1 e2 : Type} (f : e1 → e2) : Guarded e1 → Guarded e2
-- --     | .mk gf => .mk (gf.map_all (Where.map f) (Guarded.map f))
--
-- --   def ValueBindingFields.map {e1 e2 : Type} (f : e1 → e2) : ValueBindingFields e1 → ValueBindingFields e2
-- --     | .mk vf => .mk (vf.map_all f (Expr.map f) (Guarded.map f))
--
-- --   def DoStatement.map {e1 e2 : Type} (f : e1 → e2) : DoStatement e1 → DoStatement e2
-- --     | .mk sf => .mk (sf.map_all f (Expr.map f) (LetBinding.map f))
--
-- --   def DoBlock.map {e1 e2 : Type} (f : e1 → e2) : DoBlock e1 → DoBlock e2
-- --     | .mk bf => .mk (bf.map_all f (Expr.map f) (DoStatement.map f))
--
-- --   def AdoBlock.map {e1 e2 : Type} (f : e1 → e2) : AdoBlock e1 → AdoBlock e2
-- --     | .mk af => .mk (af.map_all f (Expr.map f) (DoStatement.map f))
--
-- --   def Expr.map {e1 e2 : Type} (f : e1 → e2) : Expr e1 → Expr e2
-- --     | .mk ef => .mk (ef.map_all f (Expr.map f) (DoBlock.map f) (AdoBlock.map f) (Guarded.map f) (LetBinding.map f))
-- -- end
--
-- -- mutual
-- --   theorem LetBinding.map_id {e : Type} : (lb : LetBinding e) → lb.map id = lb
-- --     | .mk bf => by simp? [map, LetBindingF.map_all_id, Expr.map_id, ValueBindingFields.map_id, Where.map_id]
--
-- --   theorem Where.map_id {e : Type} : (w : Where e) → w.map id = w
-- --     | .mk wf => by simp? [map, WhereF.map_all_id, Expr.map_id, LetBinding.map_id]
--
-- --   theorem Guarded.map_id {e : Type} : (g : Guarded e) → g.map id = g
-- --     | .mk gf => by simp? [map, GuardedF.map_all_id, Where.map_id, Guarded.map_id]
--
-- --   theorem ValueBindingFields.map_id {e : Type} : (v : ValueBindingFields e) → v.map id = v
-- --     | .mk vf => by simp? [map, ValueBindingFieldsF.map_all_id, Expr.map_id, Guarded.map_id]
--
-- --   theorem DoStatement.map_id {e : Type} : (s : DoStatement e) → s.map id = s
-- --     | .mk sf => by simp? [map, DoStatementF.map_all_id, Expr.map_id, LetBinding.map_id]
--
-- --   theorem DoBlock.map_id {e : Type} : (b : DoBlock e) → b.map id = b
-- --     | .mk bf => by simp? [map, DoBlockF.map_all_id, Expr.map_id, DoStatement.map_id]
--
-- --   theorem AdoBlock.map_id {e : Type} : (b : AdoBlock e) → b.map id = b
-- --     | .mk af => by simp? [map, AdoBlockF.map_all_id, Expr.map_id, DoStatement.map_id]
--
-- --   theorem Expr.map_id {e : Type} : (ex : Expr e) → ex.map id = ex
-- --     | .mk ef => by simp? [map, ExprF.map_all_id, Expr.map_id, DoBlock.map_id, AdoBlock.map_id, Guarded.map_id, LetBinding.map_id]
-- -- end
--
-- -- mutual
-- --   theorem LetBinding.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (lb : LetBinding e1) → lb.map (g ∘ f) = (lb.map f).map g
-- --     | .mk bf => by simp? [map, LetBindingF.map_all_comp, Expr.map_comp, ValueBindingFields.map_comp, Where.map_comp]
--
-- --   theorem Where.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (w : Where e1) → w.map (g ∘ f) = (w.map f).map g
-- --     | .mk wf => by simp? [map, WhereF.map_all_comp, Expr.map_comp, LetBinding.map_comp]
--
-- --   theorem Guarded.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (gr : Guarded e1) → gr.map (g ∘ f) = (gr.map f).map g
-- --     | .mk gf => by simp? [map, GuardedF.map_all_comp, Where.map_comp, Guarded.map_comp]
--
-- --   theorem ValueBindingFields.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (v : ValueBindingFields e1) → v.map (g ∘ f) = (v.map f).map g
-- --     | .mk vf => by simp? [map, ValueBindingFieldsF.map_all_comp, Expr.map_comp, Guarded.map_comp]
--
-- --   theorem DoStatement.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (s : DoStatement e1) → s.map (g ∘ f) = (s.map f).map g
-- --     | .mk sf => by simp? [map, DoStatementF.map_all_comp, Expr.map_comp, LetBinding.map_comp]
--
-- --   theorem DoBlock.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (b : DoBlock e1) → b.map (g ∘ f) = (b.map f).map g
-- --     | .mk bf => by simp? [map, DoBlockF.map_all_comp, Expr.map_comp, DoStatement.map_comp]
--
-- --   theorem AdoBlock.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (b : AdoBlock e1) → b.map (g ∘ f) = (b.map f).map g
-- --     | .mk af => by simp? [map, AdoBlockF.map_all_comp, Expr.map_comp, DoStatement.map_comp]
--
-- --   theorem Expr.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (ex : Expr e1) → ex.map (g ∘ f) = (ex.map f).map g
-- --     | .mk ef => by simp? [map, ExprF.map_all_comp, Expr.map_comp, DoBlock.map_comp, AdoBlock.map_comp, Guarded.map_comp, LetBinding.map_comp]
-- -- end
--
-- instance : Functor Foreign where map := map
-- instance : LawfulFunctor Foreign where
--   map_const := rfl
--   id_map := id_map
--   comp_map := comp_map
--
-- end Foreign
--
-- @[always_inline] instance : Functor Foreign where
--   map := Foreign.map
--
-- instance : LawfulFunctor Foreign where
--   map_const := rfl
--   id_map o := Foreign.id_map o
--   comp_map f g o := Foreign.comp_map f g o
--
-- inductive Fixity
--   | Infix
--   | Infixl
--   | Infixr
--   deriving Repr, BEq, Ord
--
-- inductive FixityOp
--   | Value (name : QualifiedName (Ident ⊕ Proper)) (token : SourceToken) (op : Name Operator)
--   | Type_ (token1 : SourceToken) (name : QualifiedName Proper) (token2 : SourceToken) (op : Name Operator)
--   deriving Repr, BEq
--
-- structure FixityFields where
--   keyword : SourceToken × Fixity
--   prec : SourceToken × USize
--   operator : FixityOp
--   deriving Repr, BEq
--
-- inductive Role
--   | Nominal
--   | Representational
--   | Phantom
--   deriving Repr, BEq, Ord
--
-- -- inductive Declaration (e : Type)
-- --   | Data (head : DataHead e) (optionSeparator : Option (SourceToken × (Separated (DataCtor e))))
-- --   | Type_ (head : DataHead e) (token : SourceToken) (type_ : Type_ e)
-- --   | Newtype (head : DataHead e) (token : SourceToken) (name : Name Proper) (type_ : Type_ e)
-- --   | Class (head : ClassHead e) (optionSeparator : Option (SourceToken × NonEmptyArray (Labeled (Name Ident) (Type_ e))))
-- --   | InstanceChain (separated : Separated (Instance e))
-- --   | Derive (keyword : SourceToken) (optionToken : Option SourceToken) (head : InstanceHead e)
-- --   | KindSignature (token1 : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
-- --   | Signature (labeled : Labeled (Name Ident) (Type_ e))
-- --   | Value (fields : ValueBindingFieldsRecursive e)
-- --   | Fixity (fields : FixityFields)
-- --   | Foreign (token1 : SourceToken) (token2 : SourceToken) (foreign : Foreign e)
-- --   | Role (token1 : SourceToken) (token2 : SourceToken) (name : Name Proper) (roles : NonEmptyArray (SourceToken × Role))
-- --   | Error (data : e)
-- --   deriving Repr, BEq
--
-- -- namespace Declaration
--
-- -- @[always_inline, simp] def map {α β : Type} (f : α → β) (d : Declaration α) : Declaration β :=
-- --   match d with
-- --   | Data h s => Data (h.map f) (s.map (fun (t, sep) => (t, sep.map (fun c => c.map f))))
-- --   | Type_ h t ty => Type_ (h.map f) t (ty.map f)
-- --   | Newtype h t n ty => Newtype (h.map f) t n (ty.map f)
-- --   | Class h s => Class (h.map f) (s.map (fun (t, b) => (t, b.map (fun l => l.map (fun t' => t'.map f)))))
-- --   | InstanceChain s => InstanceChain (s.map (fun i => i.map f))
-- --   | Derive k o h => Derive k o (h.map f)
-- --   | KindSignature t l => KindSignature t (l.map (fun t' => t'.map f))
-- --   | Signature l => Signature (l.map (fun t => t.map f))
-- --   | Value fields => Value (fields.map f)
-- --   | Fixity fields => Fixity fields
-- --   | Foreign t1 t2 fr => Foreign t1 t2 (fr.map f)
-- --   | Role t1 t2 n r => Role t1 t2 n r
-- --   | Error d' => Error (f d')
--
-- -- @[simp] theorem map_id {e : Type} (d : Declaration e) : d.map id = d := by
-- --   cases d <;> simp? [map, id_map, ValueBindingFields.map_id, Foreign.id_map]
--
-- -- @[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (d : Declaration e1) : d.map (g ∘ f) = (d.map f).map g := by
-- --   cases d <;> simp? [map, comp_map, ValueBindingFields.map_comp, Foreign.comp_map]
--
-- -- instance : Functor Declaration where map := map
-- -- instance : LawfulFunctor Declaration where
-- --   map_const := rfl
-- --   id_map := map_id
-- --   comp_map := map_comp
--
-- -- end Declaration
--
-- -----------------------------------------------------------------------------------------------------------
--
-- inductive Import (e : Type)
--   | Value (name : Name Ident)
--   | Op (name : Name Operator)
--   | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
--   | TypeOp (token : SourceToken) (name : Name Operator)
--   | Class (token : SourceToken) (name : Name Proper)
--   | Error (data : e)
--   deriving Repr, BEq
--
-- namespace Import
--
-- @[always_inline, simp] def map {α β : Type} (f : α → β) (i : Import α) : Import β :=
--   match i with
--   | .Value n        => .Value n
--   | .Op n           => .Op n
--   | .Type_ n m      => .Type_ n m
--   | .TypeOp t n     => .TypeOp t n
--   | .Class t n      => .Class t n
--   | .Error d        => .Error (f d)
--
-- @[simp] theorem id_map {α : Type} (i : Import α) : (i.map id) = i := by
--   cases i <;> rfl
--
-- @[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (i : Import α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
--   cases i <;> rfl
--
-- @[simp] theorem functor_map_id {α : Type} : map (id : α → α) = id := by funext i; exact id_map i
--
-- @[simp] theorem functor_map_comp {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i
--
-- end Import
--
-- @[always_inline] instance : Functor Import where
--   map := Import.map
--
-- instance : LawfulFunctor Import where
--   map_const := rfl
--   id_map i := Import.id_map i
--   comp_map f g i := Import.comp_map f g i
--
-- structure ImportDecl (e : Type) where
--   keyword : SourceToken
--   module_ : Name ModuleName
--   importList : Option (Option SourceToken × DelimitedNonEmpty (Import e))
--   qualified : Option (SourceToken × Name ModuleName)
--   deriving Repr, BEq
--
-- namespace ImportDecl
--
-- @[always_inline, simp] def map {α β : Type} (f : α → β) (i : ImportDecl α) : ImportDecl β :=
--   { i with importList := i.importList.map (fun (o, d) => (o, Functor.map (Functor.map f) d)) }
--
-- @[simp] theorem id_map {α : Type} (i : ImportDecl α) : (i.map id) = i := by
--   cases i; aesop
--
-- @[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (i : ImportDecl α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
--   cases i; aesop
--
-- @[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext i; exact id_map i
--
-- @[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i
--
-- instance : Functor ImportDecl where map := map
-- instance : LawfulFunctor ImportDecl where
--   map_const := rfl
--   id_map := id_map
--   comp_map := comp_map
--
-- end ImportDecl
--
-- @[always_inline] instance : Functor ImportDecl where
--   map := ImportDecl.map
--
-- instance : LawfulFunctor ImportDecl where
--   map_const := rfl
--   id_map i := ImportDecl.id_map i
--   comp_map f g i := ImportDecl.comp_map f g i
-- -----------------------------------------------------------------------------------------------------------
--
-- structure ModuleHeader (e : Type) where
--   keyword : SourceToken
--   name : Name ModuleName
--   exports : Option (DelimitedNonEmpty (Export e))
--   where_ : SourceToken
--   imports : Array (ImportDecl e)
--   deriving Repr, BEq
--
-- namespace ModuleHeader
--
-- @[always_inline, simp] def map {α β : Type} (f : α → β) (m : ModuleHeader α) : ModuleHeader β :=
--   { m with
--     exports := m.exports.map (Functor.map (Functor.map f))
--     imports := m.imports.map (Functor.map f)
--   }
--
-- @[simp] theorem id_map {α : Type} (m : ModuleHeader α) : (m.map id) = m := by
--   cases m; aesop
--
-- @[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (m : ModuleHeader α) : (m.map (g ∘ f)) = (m.map f |>.map g) := by
--   cases m; aesop
--
-- @[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext m; exact id_map m
--
-- @[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext m; exact comp_map f g m
--
-- instance : Functor ModuleHeader where map := map
-- instance : LawfulFunctor ModuleHeader where
--   map_const := rfl
--   id_map := id_map
--   comp_map := comp_map
--
-- end ModuleHeader


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

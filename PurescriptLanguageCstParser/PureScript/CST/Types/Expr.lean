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

@[always_inline, simp] def map {e α β : Type} (f : α → β) (s : AppSpineF e α) : AppSpineF e β :=
  match s with
  | .Type_ t type_ => .Type_ t type_
  | .Term expr     => .Term (f expr)

@[simp] theorem id_map {e α : Type} (s : AppSpineF e α) : (s.map id) = s := by
  cases s <;> aesop

@[simp] theorem comp_map {e α β γ : Type} (f : α → β) (g : β → γ) (s : AppSpineF e α) : (s.map (g ∘ f)) = (s.map f |>.map g) := by
  cases s <;> aesop

@[simp] theorem map_id_fun {e α : Type} : map (e := e) (id : α → α) = id := by funext s; exact id_map s

@[simp] theorem map_comp_fun {e α β γ : Type} (f : α → β) (g : β → γ) : map (e := e) (g ∘ f) = map g ∘ map f := by funext s; exact comp_map f g s

instance {e : Type} : Functor (AppSpineF e) where map := map
instance {e : Type} : LawfulFunctor (AppSpineF e) where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

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

-- @[always_inline] def map {e α β : Type} [SizeOf e] [SizeOf α] (f : α → β) (u : RecordUpdateF e α) : RecordUpdateF e β :=
--   match u with
--   | .Leaf label token expr   => .Leaf label token (f expr)
--   | .Branch label updates    => .Branch label (map f <$> updates)
-- termination_by u
-- decreasing_by
--   simp_wf
--   simp [Functor.map, DelimitedNonEmpty.map, Wrapped.map, Separated.map, sizeOf]
--   simp [Wrapped.sizeOf_value, Separated.sizeOf_head, Separated.sizeOf_tail_get]
--   omega

mutual
  @[simp] def mapArrayElem {e α β : Type} (g : α → β) (entry : SourceToken × RecordUpdateF e α) : SourceToken × RecordUpdateF e β :=
    (entry.1, map g entry.2)
  termination_by sizeOf entry
  decreasing_by
    cases entry
    simp_wf
    omega

  @[simp] def mapArray {e α β : Type} (g : α → β) (arr : Array (SourceToken × RecordUpdateF e α)) : Array (SourceToken × RecordUpdateF e β) :=
    arr.map (mapArrayElem g)
  termination_by sizeOf arr
  decreasing_by decreasing_trivial

  @[simp] def mapSeparated {e α β : Type} (g : α → β) (s : Separated (RecordUpdateF e α)) : Separated (RecordUpdateF e β) :=
    { head := map g s.head, tail := mapArray g s.tail }
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf

  @[simp] def mapDelimitedNonEmpty {e α β : Type} (g : α → β) (d : DelimitedNonEmpty (RecordUpdateF e α)) : DelimitedNonEmpty (RecordUpdateF e β) :=
    match d with
    | .mk w => .mk { w with value := mapSeparated g w.value }
  termination_by sizeOf d
  decreasing_by
    simp_wf
    have h1 := Wrapped.sizeOf_value w
    omega

  @[simp] def map {e α β : Type} (g : α → β) (u : RecordUpdateF e α) : RecordUpdateF e β :=
    match u with
    | .Leaf label token expr   => .Leaf label token (g expr)
    | .Branch label updates    => .Branch label (mapDelimitedNonEmpty g updates)
  termination_by sizeOf u
  decreasing_by
    all_goals simp_wf
    omega
end

-- @[simp] theorem map_id {e α : Type} [SizeOf e] [SizeOf α] (u : RecordUpdateF e α) : map id u = u := by
--   match u with
--   | .Leaf .. => simp [RecordUpdateF.map]
--   | .Branch l updates =>
--     simp [RecordUpdateF.map, LawfulFunctor.id_map]
--     rw [show updates.map (map id) = updates from by
--           cases updates; simp [Functor.map, _root_.PureScript.CST.Types.DelimitedNonEmpty.map, _root_.PureScript.CST.Types.Wrapped.map, _root_.PureScript.CST.Types.Separated.map]
--           congr; funext x; exact map_id x]
-- termination_by u
-- decreasing_by
--   simp_wf
--   simp [sizeOf, Functor.map]
--   simp [_root_.PureScript.CST.Types.DelimitedNonEmpty.sizeOf_v, _root_.PureScript.CST.Types.Wrapped.sizeOf_value, _root_.PureScript.CST.Types.Separated.sizeOf_head, _root_.PureScript.CST.Types.Separated.sizeOf_tail_get]
--   omega

mutual
  @[simp] theorem mapArrayElem_id {e α : Type} (entry : SourceToken × RecordUpdateF e α) : mapArrayElem id entry = entry := by
    cases entry
    simp only [mapArrayElem, Prod.mk.injEq, true_and]
    apply map_id

  @[simp] theorem mapArray_id {e α : Type} (arr : Array (SourceToken × RecordUpdateF e α)) : mapArray id arr = arr := by
    simp only [mapArray]
    apply Array.ext
    · simp only [Array.size_map]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map]
      apply mapArrayElem_id

  @[simp] theorem mapSeparated_id {e α : Type} (s : Separated (RecordUpdateF e α)) : mapSeparated id s = s := by
    cases s
    simp only [mapSeparated, Separated.mk.injEq]
    apply And.intro
    · apply map_id
    · apply mapArray_id

  @[simp] theorem mapDelimitedNonEmpty_id {e α : Type} (d : DelimitedNonEmpty (RecordUpdateF e α)) : mapDelimitedNonEmpty id d = d := by
    cases d
    rename_i w
    cases w
    simp only [mapDelimitedNonEmpty, DelimitedNonEmpty.mk.injEq, Wrapped.mk.injEq, true_and, and_true]
    apply mapSeparated_id

  @[simp] theorem map_id {e α : Type} (u : RecordUpdateF e α) : map id u = u := by
    cases u
    · simp only [map, id_eq]
    · simp only [map, RecordUpdateF.Branch.injEq, true_and]
      apply mapDelimitedNonEmpty_id
end

-- @[simp] theorem map_comp {e α β γ : Type} [SizeOf e] [SizeOf α] [SizeOf β] (f : α → β) (g : β → γ) (u : RecordUpdateF e α) : map (g ∘ f) u = map g (map f u) := by
--   match u with
--   | .Leaf .. => simp [RecordUpdateF.map]
--   | .Branch l updates =>
--     simp [RecordUpdateF.map]
--     rw [show updates.map (map (g ∘ f)) = updates.map (map f) |>.map (map g) from by
--           cases updates; simp [Functor.map, _root_.PureScript.CST.Types.DelimitedNonEmpty.map, _root_.PureScript.CST.Types.Wrapped.map, _root_.PureScript.CST.Types.Separated.map]
--           congr; funext x; exact map_comp f g x]
-- termination_by u
-- decreasing_by
--   simp_wf
--   simp [sizeOf, Functor.map]
--   simp [_root_.PureScript.CST.Types.DelimitedNonEmpty.sizeOf_v, _root_.PureScript.CST.Types.Wrapped.sizeOf_value, _root_.PureScript.CST.Types.Separated.sizeOf_head, _root_.PureScript.CST.Types.Separated.sizeOf_tail_get]
--   omega

mutual
  @[simp] theorem mapArrayElem_comp {e α β γ : Type} (gf : α → β) (hg : β → γ) (entry : SourceToken × RecordUpdateF e α) :
      mapArrayElem (hg ∘ gf) entry = mapArrayElem hg (mapArrayElem gf entry) := by
    cases entry
    simp only [mapArrayElem, Prod.mk.injEq, true_and]
    apply map_comp

  @[simp] theorem mapArray_comp {e α β γ : Type} (gf : α → β) (hg : β → γ) (arr : Array (SourceToken × RecordUpdateF e α)) :
      mapArray (hg ∘ gf) arr = mapArray hg (mapArray gf arr) := by
    simp only [mapArray]
    apply Array.ext
    · simp only [Array.size_map]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map]
      apply mapArrayElem_comp

  @[simp] theorem mapSeparated_comp {e α β γ : Type} (gf : α → β) (hg : β → γ) (s : Separated (RecordUpdateF e α)) :
      mapSeparated (hg ∘ gf) s = mapSeparated hg (mapSeparated gf s) := by
    cases s
    simp only [mapSeparated, Separated.mk.injEq]
    apply And.intro
    · apply map_comp
    · apply mapArray_comp

  @[simp] theorem mapDelimitedNonEmpty_comp {e α β γ : Type} (gf : α → β) (hg : β → γ) (d : DelimitedNonEmpty (RecordUpdateF e α)) :
      mapDelimitedNonEmpty (hg ∘ gf) d = mapDelimitedNonEmpty hg (mapDelimitedNonEmpty gf d) := by
    cases d
    rename_i w
    cases w
    simp only [mapDelimitedNonEmpty, DelimitedNonEmpty.mk.injEq, Wrapped.mk.injEq, true_and, and_true]
    apply mapSeparated_comp

  @[simp] theorem map_comp {e α β γ : Type} (gf : α → β) (hg : β → γ) (u : RecordUpdateF e α) :
      map (hg ∘ gf) u = map hg (map gf u) := by
    cases u
    · simp only [map, Function.comp_apply]
    · simp only [map, RecordUpdateF.Branch.injEq, true_and]
      apply mapDelimitedNonEmpty_comp
end

instance {e : Type} : Functor (RecordUpdateF e) where map := map
instance {e : Type} : LawfulFunctor (RecordUpdateF e) where
  map_const := rfl
  id_map := map_id
  comp_map := map_comp

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

@[always_inline, simp] def map {e α β : Type} (f : α → β) (l : LambdaF e α) : LambdaF e β :=
  { l with body := f l.body }

@[simp] theorem id_map {e α : Type} (l : LambdaF e α) : (l.map id) = l := by
  cases l; aesop

@[simp] theorem comp_map {e α β γ : Type} (f : α → β) (g : β → γ) (l : LambdaF e α) : (l.map (g ∘ f)) = (l.map f |>.map g) := by
  cases l; aesop

@[simp] theorem map_id_fun {e α : Type} : map (e := e) (id : α → α) = id := by funext l; exact id_map l

@[simp] theorem map_comp_fun {e α β γ : Type} (f : α → β) (g : β → γ) : map (e := e) (g ∘ f) = map g ∘ map f := by funext l; exact comp_map f g l

instance {e : Type} : Functor (LambdaF e) where map := map
instance {e : Type} : LawfulFunctor (LambdaF e) where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

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

@[always_inline, simp] def map {e α β : Type} (f : α → β) (p : PatternGuardF e α) : PatternGuardF e β :=
  { p with expr := f p.expr }

@[simp] theorem id_map {e α : Type} (p : PatternGuardF e α) : (p.map id) = p := by
  cases p; aesop

@[simp] theorem comp_map {e α β γ : Type} (f : α → β) (g : β → γ) (p : PatternGuardF e α) : (p.map (g ∘ f)) = (p.map f |>.map g) := by
  cases p; aesop

@[simp] theorem map_id_fun {e α : Type} : map (e := e) (id : α → α) = id := by funext p; exact id_map p

@[simp] theorem map_comp_fun {e α β γ : Type} (f : α → β) (g : β → γ) : map (e := e) (g ∘ f) = map g ∘ map f := by funext p; exact comp_map f g p

instance {e : Type} : Functor (PatternGuardF e) where map := map
instance {e : Type} : LawfulFunctor (PatternGuardF e) where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

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

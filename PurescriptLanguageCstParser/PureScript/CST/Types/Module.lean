module

import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop
public import PurescriptLanguageCstParser.PureScript.CST.Types.PType
public import PurescriptLanguageCstParser.PureScript.CST.Types.Expr.Leafs
public import PurescriptLanguageCstParser.PureScript.CST.Types.Expr.Rec.Basic
public import PurescriptLanguageCstParser.PureScript.CST.Types.Expr.Rec.LawfulFunctorMapId
meta import PurescriptLanguageCstParser.GenerateFixed

@[expose] public section

namespace PureScript.CST.Types

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String
open PureScript.CST.Types

-----------------------------------------------------------------------------------------------------------

inductive InstanceBinding (e : Type)
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Name (fields : ValueBindingFieldsRecursive e)
  deriving Repr, BEq

namespace InstanceBinding

@[always_inline, simp] def map {α β : Type} (f : α → β) (i : InstanceBinding α) : InstanceBinding β :=
  match i with
  | Signature l => Signature (l.map_value (fun t => t.map f))
  | Name fields => Name (fields.map f)

@[simp] theorem map_id {e : Type} (i : InstanceBinding e) : i.map id = i := by
  cases i
  simp only [map, Type_.map_id, Signature.injEq]
  rfl
  simp_all only [map, ValueBindingFieldsRecursive.map.eq_1, Binder.map_id, Array.map_subtype, Array.unattach_attach,
    Array.map_id_fun', id_eq, Name.injEq]
  sorry

@[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (i : InstanceBinding e1) : i.map (g ∘ f) = (i.map f).map g := by
  cases i <;> simp only [map, Type_.map_comp, Signature.injEq]
  rfl
  sorry

instance : Functor InstanceBinding where map := map
instance : LawfulFunctor InstanceBinding where
  map_const := rfl
  id_map := map_id
  comp_map := map_comp

end InstanceBinding

structure Instance (e : Type) where
  head : InstanceHead e
  body : Option (SourceToken × NonEmptyArray (InstanceBinding e))
  deriving Repr, BEq

namespace Instance

@[always_inline, simp] def map {α β : Type} (f : α → β) (i : Instance α) : Instance β :=
  { head := i.head.map f
    body := i.body.map (fun (t, b) => (t, b.map (fun b' => b'.map f)))
  }

@[simp] theorem map_id {e : Type} (i : Instance e) : i.map id = i := by
  cases i
  simp only [map, InstanceHead.map, functor_map_id, id_map, Option.map_id_fun', id_eq,
    Array.map_id_fun, NonEmptyArray.map, InstanceBinding.map, Type_.map_id,
    ValueBindingFieldsRecursive.map.eq_1, Binder.map_id, Array.map_subtype, Array.unattach_attach,
    Array.map_id_fun', mk.injEq, true_and]
  sorry

@[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (i : Instance e1) : i.map (g ∘ f) = (i.map f).map g := by
  cases i
  sorry

instance : Functor Instance where map := map
instance : LawfulFunctor Instance where
  map_const := rfl
  id_map := map_id
  comp_map := map_comp

end Instance

inductive Declaration (e : Type)
  | Data (head : DataHead e) (optionSeparator : Option (SourceToken × (Separated (DataCtor e))))
  | Type_ (head : DataHead e) (token : SourceToken) (type_ : Type_ e)
  | Newtype (head : DataHead e) (token : SourceToken) (name : Name Proper) (type_ : Type_ e)
  | Class (head : ClassHead e) (optionSeparator : Option (SourceToken × NonEmptyArray (Labeled (Name Ident) (Type_ e))))
  | InstanceChain (separated : Separated (Instance e))
  | Derive (keyword : SourceToken) (optionToken : Option SourceToken) (head : InstanceHead e)
  | KindSignature (token1 : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Value (fields : ValueBindingFieldsRecursive e)
  | Fixity (fields : FixityFields)
  | Foreign (token1 : SourceToken) (token2 : SourceToken) (foreign : Foreign e)
  | Role (token1 : SourceToken) (token2 : SourceToken) (name : Name Proper) (roles : NonEmptyArray (SourceToken × Role))
  | Error (data : e)
  deriving Repr, BEq

namespace Declaration

@[always_inline, simp] def map {α β : Type} (f : α → β) (d : Declaration α) : Declaration β :=
  match d with
  | Data h s => Data (h.map f) (s.map (fun (t, sep) => (t, sep.map (fun c => c.map f))))
  | Type_ h t ty => Type_ (h.map f) t (ty.map f)
  | Newtype h t n ty => Newtype (h.map f) t n (ty.map f)
  | Class h s => Class (h.map f) (s.map (fun (t, b) => (t, b.map (fun l => l.map_value (fun t' => t'.map f)))))
  | InstanceChain s => InstanceChain (s.map (fun i => i.map f))
  | Derive k o h => Derive k o (h.map f)
  | KindSignature t l => KindSignature t (l.map_value (fun t' => t'.map f))
  | Signature l => Signature (l.map_value (fun t => t.map f))
  | Value fields => Value (fields.map f)
  | Fixity fields => Fixity fields
  | Foreign t1 t2 fr => Foreign t1 t2 (fr.map f)
  | Role t1 t2 n r => Role t1 t2 n r
  | Error d' => Error (f d')

@[simp] theorem map_id {e : Type} (d : Declaration e) : d.map id = d := by
  cases d
  · simp_all only [map, DataHead.map, functor_map_id, Array.map_id_fun, id_eq, Separated.map, DataCtor.map,
    Array.map_id_fun', Option.map_id_fun']
  · simp_all only [map, DataHead.map, functor_map_id, Array.map_id_fun, id_eq, Type_.map_id]
  · simp_all only [map, DataHead.map, functor_map_id, Array.map_id_fun, id_eq, Type_.map_id]
  ·
    simp_all only [map, ClassHead.map, functor_map_id, id_map, Option.map_id_fun', id_eq, Array.map_id_fun,
      NonEmptyArray.map, Type_.map_id, Class.injEq, true_and]
    ext a : 1
    simp_all only [Option.map_eq_some_iff, Prod.exists]
    obtain ⟨fst, snd⟩ := a
    simp_all only [Prod.mk.injEq]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨w_1, h⟩ := h
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      subst left left_1 right
      simp_all only [Option.some.injEq, Prod.mk.injEq, true_and]
      ext : 1
      · simp_all only
        rfl
      · ext i hi₁ hi₂ : 1
        · simp_all only [Array.size_map]
        · simp_all only [Array.getElem_map]
          rfl
    · intro a
      subst a
      simp_all only [Option.some.injEq, Prod.mk.injEq]
      apply Exists.intro
      · apply Exists.intro
        · apply And.intro
          on_goal 2 => apply And.intro
          on_goal 3 => ext : 1
          on_goal 4 => ext i hi₁ hi₂ : 1
          on_goal 4 => {
            simp_all only [Array.size_map]
            rfl
          }
          · simp_all only [and_true]
            rfl
          · simp_all only
          · simp_all only
            rfl
          · simp_all only [Array.getElem_map]
            rfl
  ·
    simp_all only [map, Separated.map, Instance.map, InstanceHead.map, functor_map_id, id_map, Option.map_id_fun',
      id_eq, Array.map_id_fun, NonEmptyArray.map, InstanceBinding.map, Type_.map_id,
      ValueBindingFieldsRecursive.map.eq_1, Binder.map_id, Array.map_subtype, Array.unattach_attach, Array.map_id_fun',
      InstanceChain.injEq]
    sorry
  · simp_all only [map, InstanceHead.map, functor_map_id, id_map, Option.map_id_fun', id_eq, Array.map_id_fun]
  ·
    simp_all only [map, Type_.map_id, KindSignature.injEq, true_and]
    rfl
  ·
    simp_all only [map, Type_.map_id, Signature.injEq]
    rfl
  ·
    simp_all only [map, ValueBindingFieldsRecursive.map.eq_1, Binder.map_id, Array.map_subtype, Array.unattach_attach,
      Array.map_id_fun', id_eq, Value.injEq]
    sorry
  · simp_all only [map]
  ·
    simp_all only [map, Foreign.map, functor_map_id, id_map, Foreign.injEq, true_and]
    split
    next o l => simp_all only
    next o k l => simp_all only
    next o k n => simp_all only
  · simp_all only [map]
  · simp_all only [map, id_eq]

@[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (d : Declaration e1) : d.map (g ∘ f) = (d.map f).map g := by
  cases d
  simp_all only [map, DataHead.map, functor_map_comp, Separated.map, DataCtor.map, Array.map_map, Option.map_map,
    Data.injEq, true_and]
  ext a : 1
  simp_all only [Option.map_eq_some_iff, Prod.exists, Function.comp_apply, Array.map_map]
  obtain ⟨fst, snd⟩ := a
  simp_all only [Prod.mk.injEq]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    subst left left_1 right
    simp_all only [Option.some.injEq, Prod.mk.injEq, Separated.mk.injEq, DataCtor.mk.injEq]
    apply Exists.intro
    · apply Exists.intro
      · apply And.intro
        apply And.intro
        on_goal 2 => { rfl
        }
        on_goal 2 =>
          {
          simp_all only [and_self, Array.map_inj_left, Function.comp_apply, Array.map_map, implies_true, and_true]
          rfl
        }
        · simp_all only
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    subst left left_1 right
    simp_all only [Option.some.injEq, Prod.mk.injEq, Separated.mk.injEq, DataCtor.mk.injEq]
    apply Exists.intro
    · apply Exists.intro
      · apply And.intro
        on_goal 2 => apply And.intro
        on_goal 3 => apply And.intro
        on_goal 3 => apply And.intro
        on_goal 3 => { rfl
        }
        · simp_all only [and_true]
          rfl
        · simp_all only
        · simp_all only
        · simp_all only [Array.map_inj_left, Function.comp_apply, Array.map_map, implies_true]
  · simp_all only [map, DataHead.map, functor_map_comp, Type_.map_comp, Array.map_map]
  · simp_all only [map, DataHead.map, functor_map_comp, Type_.map_comp, Array.map_map]
  ·
    simp_all only [map, ClassHead.map, functor_map_comp, Function.comp_apply, Functor.map_map, NonEmptyArray.map,
      Type_.map_comp, Option.map_map, Array.map_map, Class.injEq, ClassHead.mk.injEq, and_self, and_true, true_and]
    apply And.intro
    · ext a : 1
      simp_all only [Option.map_eq_some_iff, Prod.exists, Function.comp_apply, Functor.map_map]
    · ext a : 1
      simp_all only [Option.map_eq_some_iff, Prod.exists, Function.comp_apply, Array.map_map]
      obtain ⟨fst, snd⟩ := a
      simp_all only [Prod.mk.injEq]
      rfl
  · sorry
  ·
    simp_all only [map, InstanceHead.map, functor_map_comp, Function.comp_apply, Functor.map_map, Option.map_map,
      Array.map_map, Derive.injEq, InstanceHead.mk.injEq, and_self, and_true, true_and]
    ext a : 1
    simp_all only [Option.map_eq_some_iff, Prod.exists, Function.comp_apply, Functor.map_map]
  ·
    simp_all only [map, Type_.map_comp, KindSignature.injEq, true_and]
    rfl
  ·
    simp_all only [map, Type_.map_comp, Signature.injEq]
    rfl
  · sorry
  · simp_all only [map]
  ·
    simp_all only [map, Foreign.map, functor_map_comp, Function.comp_apply, Functor.map_map, Foreign.injEq, true_and]
    split
    next o l => simp_all only [Functor.map_map]
    next o k l => simp_all only [Functor.map_map]
    next o k n => simp_all only
  · simp_all only [map]
  · simp_all only [map, Function.comp_apply]

instance : Functor Declaration where map := map
instance : LawfulFunctor Declaration where
  map_const := rfl
  id_map := map_id
  comp_map := map_comp

end Declaration

---------------------------------------------------------------------------------------------------------

structure ModuleBody (e : Type) where
  decls : Array (Declaration e)
  trailingComments : Array (Comment LineFeed)
  end_ : SourcePos
  deriving Repr, BEq

structure Module (e : Type) where
  header : ModuleHeader e
  body : ModuleBody e
  deriving Repr, BEq

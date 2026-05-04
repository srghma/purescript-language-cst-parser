module

import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop
public import PurescriptLanguageCstParser.PureScript.CST.Types.PType
public import PurescriptLanguageCstParser.PureScript.CST.Types.ExprLeafs
meta import PurescriptLanguageCstParser.GenerateFixed

@[expose] public section

namespace PureScript.CST.Types

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String
open PureScript.CST.Types

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

-- namespace InstanceBinding

-- @[always_inline, simp] def map {α β : Type} (f : α → β) (i : InstanceBinding α) : InstanceBinding β :=
--   match i with
--   | Signature l => Signature (l.map (fun t => t.map f))
--   | Name fields => Name (fields.map f)

-- @[simp] theorem map_id {e : Type} (i : InstanceBinding e) : i.map id = i := by
--   cases i <;> simp? [map, id_map, ValueBindingFields.map_id]

-- @[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (i : InstanceBinding e1) : i.map (g ∘ f) = (i.map f).map g := by
--   cases i <;> simp? [map, comp_map, ValueBindingFields.map_comp]

-- instance : Functor InstanceBinding where map := map
-- instance : LawfulFunctor InstanceBinding where
--   map_const := rfl
--   id_map := map_id
--   comp_map := map_comp

-- end InstanceBinding

-- structure Instance (e : Type) where
--   head : InstanceHead e
--   body : Option (SourceToken × NonEmptyArray (InstanceBinding e))
--   deriving Repr, BEq

-- namespace Instance

-- @[always_inline, simp] def map {α β : Type} (f : α → β) (i : Instance α) : Instance β :=
--   { head := i.head.map f
--     body := i.body.map (fun (t, b) => (t, b.map (fun b' => b'.map f)))
--   }

-- @[simp] theorem map_id {e : Type} (i : Instance e) : i.map id = i := by
--   cases i; simp? [map, id_map]

-- @[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (i : Instance e1) : i.map (g ∘ f) = (i.map f).map g := by
--   cases i; simp? [map, comp_map]

-- instance : Functor Instance where map := map
-- instance : LawfulFunctor Instance where
--   map_const := rfl
--   id_map := map_id
--   comp_map := map_comp

-- end Instance

-- mutual
--   def LetBinding.map {e1 e2 : Type} (f : e1 → e2) : LetBinding e1 → LetBinding e2
--     | .mk bf => .mk (bf.map_all f (Expr.map f) (ValueBindingFields.map f) (Where.map f))

--   def Where.map {e1 e2 : Type} (f : e1 → e2) : Where e1 → Where e2
--     | .mk wf => .mk (wf.map_all f (Expr.map f) (LetBinding.map f))

--   def Guarded.map {e1 e2 : Type} (f : e1 → e2) : Guarded e1 → Guarded e2
--     | .mk gf => .mk (gf.map_all (Where.map f) (Guarded.map f))

--   def ValueBindingFields.map {e1 e2 : Type} (f : e1 → e2) : ValueBindingFields e1 → ValueBindingFields e2
--     | .mk vf => .mk (vf.map_all f (Expr.map f) (Guarded.map f))

--   def DoStatement.map {e1 e2 : Type} (f : e1 → e2) : DoStatement e1 → DoStatement e2
--     | .mk sf => .mk (sf.map_all f (Expr.map f) (LetBinding.map f))

--   def DoBlock.map {e1 e2 : Type} (f : e1 → e2) : DoBlock e1 → DoBlock e2
--     | .mk bf => .mk (bf.map_all f (Expr.map f) (DoStatement.map f))

--   def AdoBlock.map {e1 e2 : Type} (f : e1 → e2) : AdoBlock e1 → AdoBlock e2
--     | .mk af => .mk (af.map_all f (Expr.map f) (DoStatement.map f))

--   def Expr.map {e1 e2 : Type} (f : e1 → e2) : Expr e1 → Expr e2
--     | .mk ef => .mk (ef.map_all f (Expr.map f) (DoBlock.map f) (AdoBlock.map f) (Guarded.map f) (LetBinding.map f))
-- end

-- mutual
--   theorem LetBinding.map_id {e : Type} : (lb : LetBinding e) → lb.map id = lb
--     | .mk bf => by simp? [map, LetBindingF.map_all_id, Expr.map_id, ValueBindingFields.map_id, Where.map_id]

--   theorem Where.map_id {e : Type} : (w : Where e) → w.map id = w
--     | .mk wf => by simp? [map, WhereF.map_all_id, Expr.map_id, LetBinding.map_id]

--   theorem Guarded.map_id {e : Type} : (g : Guarded e) → g.map id = g
--     | .mk gf => by simp? [map, GuardedF.map_all_id, Where.map_id, Guarded.map_id]

--   theorem ValueBindingFields.map_id {e : Type} : (v : ValueBindingFields e) → v.map id = v
--     | .mk vf => by simp? [map, ValueBindingFieldsF.map_all_id, Expr.map_id, Guarded.map_id]

--   theorem DoStatement.map_id {e : Type} : (s : DoStatement e) → s.map id = s
--     | .mk sf => by simp? [map, DoStatementF.map_all_id, Expr.map_id, LetBinding.map_id]

--   theorem DoBlock.map_id {e : Type} : (b : DoBlock e) → b.map id = b
--     | .mk bf => by simp? [map, DoBlockF.map_all_id, Expr.map_id, DoStatement.map_id]

--   theorem AdoBlock.map_id {e : Type} : (b : AdoBlock e) → b.map id = b
--     | .mk af => by simp? [map, AdoBlockF.map_all_id, Expr.map_id, DoStatement.map_id]

--   theorem Expr.map_id {e : Type} : (ex : Expr e) → ex.map id = ex
--     | .mk ef => by simp? [map, ExprF.map_all_id, Expr.map_id, DoBlock.map_id, AdoBlock.map_id, Guarded.map_id, LetBinding.map_id]
-- end

-- mutual
--   theorem LetBinding.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (lb : LetBinding e1) → lb.map (g ∘ f) = (lb.map f).map g
--     | .mk bf => by simp? [map, LetBindingF.map_all_comp, Expr.map_comp, ValueBindingFields.map_comp, Where.map_comp]

--   theorem Where.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (w : Where e1) → w.map (g ∘ f) = (w.map f).map g
--     | .mk wf => by simp? [map, WhereF.map_all_comp, Expr.map_comp, LetBinding.map_comp]

--   theorem Guarded.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (gr : Guarded e1) → gr.map (g ∘ f) = (gr.map f).map g
--     | .mk gf => by simp? [map, GuardedF.map_all_comp, Where.map_comp, Guarded.map_comp]

--   theorem ValueBindingFields.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (v : ValueBindingFields e1) → v.map (g ∘ f) = (v.map f).map g
--     | .mk vf => by simp? [map, ValueBindingFieldsF.map_all_comp, Expr.map_comp, Guarded.map_comp]

--   theorem DoStatement.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (s : DoStatement e1) → s.map (g ∘ f) = (s.map f).map g
--     | .mk sf => by simp? [map, DoStatementF.map_all_comp, Expr.map_comp, LetBinding.map_comp]

--   theorem DoBlock.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (b : DoBlock e1) → b.map (g ∘ f) = (b.map f).map g
--     | .mk bf => by simp? [map, DoBlockF.map_all_comp, Expr.map_comp, DoStatement.map_comp]

--   theorem AdoBlock.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (b : AdoBlock e1) → b.map (g ∘ f) = (b.map f).map g
--     | .mk af => by simp? [map, AdoBlockF.map_all_comp, Expr.map_comp, DoStatement.map_comp]

--   theorem Expr.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) : (ex : Expr e1) → ex.map (g ∘ f) = (ex.map f).map g
--     | .mk ef => by simp? [map, ExprF.map_all_comp, Expr.map_comp, DoBlock.map_comp, AdoBlock.map_comp, Guarded.map_comp, LetBinding.map_comp]
-- end

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

-- namespace Declaration

-- @[always_inline, simp] def map {α β : Type} (f : α → β) (d : Declaration α) : Declaration β :=
--   match d with
--   | Data h s => Data (h.map f) (s.map (fun (t, sep) => (t, sep.map (fun c => c.map f))))
--   | Type_ h t ty => Type_ (h.map f) t (ty.map f)
--   | Newtype h t n ty => Newtype (h.map f) t n (ty.map f)
--   | Class h s => Class (h.map f) (s.map (fun (t, b) => (t, b.map (fun l => l.map (fun t' => t'.map f)))))
--   | InstanceChain s => InstanceChain (s.map (fun i => i.map f))
--   | Derive k o h => Derive k o (h.map f)
--   | KindSignature t l => KindSignature t (l.map (fun t' => t'.map f))
--   | Signature l => Signature (l.map (fun t => t.map f))
--   | Value fields => Value (fields.map f)
--   | Fixity fields => Fixity fields
--   | Foreign t1 t2 fr => Foreign t1 t2 (fr.map f)
--   | Role t1 t2 n r => Role t1 t2 n r
--   | Error d' => Error (f d')

-- @[simp] theorem map_id {e : Type} (d : Declaration e) : d.map id = d := by
--   cases d <;> simp? [map, id_map, ValueBindingFields.map_id, Foreign.id_map]

-- @[simp] theorem map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (d : Declaration e1) : d.map (g ∘ f) = (d.map f).map g := by
--   cases d <;> simp? [map, comp_map, ValueBindingFields.map_comp, Foreign.comp_map]

-- instance : Functor Declaration where map := map
-- instance : LawfulFunctor Declaration where
--   map_const := rfl
--   id_map := map_id
--   comp_map := map_comp

-- end Declaration

-----------------------------------------------------------------------------------------------------------

-- structure ModuleBody (e : Type) where
--   decls : Array (Declaration e)
--   trailingComments : Array (Comment LineFeed)
--   end_ : SourcePos
--   deriving Repr, BEq

-- structure Module (e : Type) where
--   header : ModuleHeader e
--   body : ModuleBody e
--   deriving Repr, BEq
end PureScript.CST.Types

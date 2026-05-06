module

import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop
import PurescriptLanguageCstParser.PureScript.CST.Types.PType
public import PurescriptLanguageCstParser.PureScript.CST.Types.Expr.Leafs
public import PurescriptLanguageCstParser.PureScript.CST.Types.Expr.Rec.Basic
public import PurescriptLanguageCstParser.PureScript.CST.Types.Expr.Rec.Simp
public import PurescriptLanguageCstParser.PureScript.CST.Types.Expr.Rec.Functor
@[expose] public section
namespace PureScript.CST.Types

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String
open PureScript.CST.Types

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  map_comp theorems                                               ║
-- ╚══════════════════════════════════════════════════════════════════╝

-- mutual
--   theorem Expr.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (expr : Expr e1) : (Expr.map (g ∘ f) expr) = (Expr.map g (Expr.map f expr)) := by
--     cases expr
--     · rfl -- Hole
--     · rfl -- Section
--     · rfl -- Ident
--     · rfl -- Constructor
--     · rfl -- Boolean
--     · rfl -- Char
--     · rfl -- NonEmptyString
--     · rfl -- Int
--     · rfl -- Number
--     · rename_i items; dsimp [Expr.map]; rw [Expr.mapDelimited_comp]
--     · rename_i fields; dsimp [Expr.map]; rw [Expr.mapDelimitedRL_comp]
--     · rename_i w; dsimp [Expr.map]; congr 1; exact Expr.map_comp f g w.value
--     · rename_i expr t ty; dsimp [Expr.map]; simp only [Type_.map_comp]; congr 1; exact Expr.map_comp f g expr
--     · rename_i head tail; dsimp [Expr.map]; simp only [NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]; congr 1
--       · exact Expr.map_comp f g head
--       · congr; funext ⟨⟨w, e'⟩, hw_e⟩; simp only [Function.comp_apply]; congr 1
--         · congr 1; exact Expr.map_comp f g w.value
--         · exact Expr.map_comp f g e'
--     · rename_i head ops; dsimp [Expr.map]; simp only [NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]; congr 1
--       · exact Expr.map_comp f g head
--       · congr; funext ⟨⟨n, e'⟩, hn_e⟩; simp only [Function.comp_apply]; congr 1; exact Expr.map_comp f g e'
--     · rfl -- OpName
--     · rename_i t e'; dsimp [Expr.map]; congr 1; exact Expr.map_comp f g e'
--     · rename_i data; dsimp [Expr.map]; congr 1; exact RecordAccessorRecursive.map_comp f g data
--     · rename_i expr updates; dsimp [Expr.map]; simp only [DelimitedNonEmpty.attach_map, ← DelimitedNonEmpty.comp_map]; congr 1
--       · exact Expr.map_comp f g expr
--       · congr; funext ⟨u, hu⟩; exact RecordUpdateRecursive.map_comp f g u.val
--     · rename_i fn args; dsimp [Expr.map]; simp only [NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]; congr 1
--       · exact Expr.map_comp f g fn
--       · congr; funext ⟨x, hx⟩; exact AppSpineRecursive.map_comp f g x.val
--     · rename_i data; dsimp [Expr.map]; congr 1; exact LambdaRecursive.map_comp f g data
--     · rename_i data; dsimp [Expr.map]; congr 1; exact IfThenElseRecursive.map_comp f g data
--     · rename_i data; dsimp [Expr.map]; congr 1; exact CaseOfRecursive.map_comp f g data
--     · rename_i data; dsimp [Expr.map]; congr 1; exact LetInRecursive.map_comp f g data
--     · rename_i data; dsimp [Expr.map]; congr 1; exact DoBlockRecursive.map_comp f g data
--     · rename_i data; dsimp [Expr.map]; congr 1; exact AdoBlockRecursive.map_comp f g data
--     · rename_i d; dsimp [Expr.map]; rfl

--   theorem Expr.mapDelimited_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (d : Delimited (Expr e1)) : Expr.mapDelimited (g ∘ f) d = Expr.mapDelimited g (Expr.mapDelimited f d) := by
--     cases d; rename_i w
--     cases w.value
--     · dsimp [Expr.mapDelimited]; rfl
--     · rename_i s; dsimp [Expr.mapDelimited]; congr 2; exact Expr.mapSep_comp f g s

--   theorem Expr.mapSep_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (s : Separated (Expr e1)) : Expr.mapSep (g ∘ f) s = Expr.mapSep g (Expr.mapSep f s) := by
--     cases s; dsimp [Expr.mapSep]
--     simp only [Array.attach_map, ← Array.comp_map]
--     congr 1
--     · exact Expr.map_comp f g _
--     · congr; funext ⟨⟨tok, e'⟩, he⟩; simp only [Function.comp_apply]; congr 1; exact Expr.map_comp f g e'

--   theorem Expr.mapDelimitedRL_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (d : Delimited (RecordLabeled (Expr e1))) : Expr.mapDelimitedRL (g ∘ f) d = Expr.mapDelimitedRL g (Expr.mapDelimitedRL f d) := by
--     cases d; rename_i w
--     cases w.value
--     · dsimp [Expr.mapDelimitedRL]; rfl
--     · rename_i s; dsimp [Expr.mapDelimitedRL]; congr 2; exact Expr.mapSepRL_comp f g s

--   theorem Expr.mapSepRL_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (s : Separated (RecordLabeled (Expr e1))) : Expr.mapSepRL (g ∘ f) s = Expr.mapSepRL g (Expr.mapSepRL f s) := by
--     cases s; dsimp [Expr.mapSepRL]
--     simp only [Array.attach_map, ← Array.comp_map]
--     congr 1
--     · exact Expr.mapRL_comp f g _
--     · congr; funext ⟨⟨tok, rl⟩, _hmem⟩; simp only [Function.comp_apply]; congr 1; exact Expr.mapRL_comp f g rl

--   theorem Expr.mapRL_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (rl : RecordLabeled (Expr e1)) : Expr.mapRL (g ∘ f) rl = Expr.mapRL g (Expr.mapRL f rl) := by
--     cases rl
--     · dsimp [Expr.mapRL]
--     · dsimp [Expr.mapRL]; congr 2; exact Expr.map_comp f g _

--   theorem RecordAccessorRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : RecordAccessorRecursive e1) : (RecordAccessorRecursive.map (g ∘ f) data) = (RecordAccessorRecursive.map g (RecordAccessorRecursive.map f data)) := by
--     cases data; dsimp [RecordAccessorRecursive.map]; congr 1; exact Expr.map_comp f g _

--   theorem RecordUpdateRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (u : RecordUpdateRecursive e1) : (RecordUpdateRecursive.map (g ∘ f) u) = (RecordUpdateRecursive.map g (RecordUpdateRecursive.map f u)) := by
--     cases u
--     · dsimp [RecordUpdateRecursive.map]; congr 2; exact Expr.map_comp f g _
--     · dsimp [RecordUpdateRecursive.map]
--       simp only [DelimitedNonEmpty.attach_map, ← DelimitedNonEmpty.comp_map]
--       congr 2; funext ⟨x, hx⟩; exact RecordUpdateRecursive.map_comp f g x.val

--   theorem AppSpineRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (s : AppSpineRecursive e1) : (AppSpineRecursive.map (g ∘ f) s) = (AppSpineRecursive.map g (AppSpineRecursive.map f s)) := by
--     cases s
--     · dsimp [AppSpineRecursive.map]; simp only [Type_.map_comp]
--     · dsimp [AppSpineRecursive.map]; congr 1; exact Expr.map_comp f g _

--   theorem LambdaRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : LambdaRecursive e1) : (LambdaRecursive.map (g ∘ f) data) = (LambdaRecursive.map g (LambdaRecursive.map f data)) := by
--     cases data; dsimp [LambdaRecursive.map]
--     simp only [Binder.map_comp, NonEmptyArray.map_map, Function.comp_apply]
--     congr 1; exact Expr.map_comp f g _

--   theorem IfThenElseRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : IfThenElseRecursive e1) : (IfThenElseRecursive.map (g ∘ f) data) = (IfThenElseRecursive.map g (IfThenElseRecursive.map f data)) := by
--     cases data; dsimp [IfThenElseRecursive.map]
--     congr 1
--     · exact Expr.map_comp f g _
--     · congr 1
--       · exact Expr.map_comp f g _
--       · congr 1; exact Expr.map_comp f g _

--   theorem CaseOfRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : CaseOfRecursive e1) : (CaseOfRecursive.map (g ∘ f) data) = (CaseOfRecursive.map g (CaseOfRecursive.map f data)) := by
--     cases data; dsimp [CaseOfRecursive.map]
--     simp only [Separated.map_comp_fun, NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]
--     congr 1
--     · congr; funext x; exact Expr.map_comp f g x
--     · congr; funext ⟨⟨b, guarded⟩, hb_g⟩; simp only [Function.comp_apply]; congr 1
--       · simp only [Separated.map_comp_fun, Binder.map_comp]
--       · exact GuardedRecursive.map_comp f g guarded

--   theorem GuardedRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (guarded : GuardedRecursive e1) : (GuardedRecursive.map (g ∘ f) guarded) = (GuardedRecursive.map g (GuardedRecursive.map f guarded)) := by
--     cases guarded
--     · dsimp [GuardedRecursive.map]; congr 1; exact WhereRecursive.map_comp f g _
--     · dsimp [GuardedRecursive.map]
--       simp only [NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]
--       congr 1; funext ⟨x, hx⟩; exact GuardedExprRecursive.map_comp f g x.val

--   theorem GuardedExprRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : GuardedExprRecursive e1) : (GuardedExprRecursive.map (g ∘ f) data) = (GuardedExprRecursive.map g (GuardedExprRecursive.map f data)) := by
--     cases data; dsimp [GuardedExprRecursive.map]
--     simp only [Separated.attach_map, ← Separated.comp_map]
--     congr 1
--     · congr; funext ⟨x, hx⟩; exact PatternGuardRecursive.map_comp f g x.val
--     · exact WhereRecursive.map_comp f g _

--   theorem PatternGuardRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : PatternGuardRecursive e1) : (PatternGuardRecursive.map (g ∘ f) data) = (PatternGuardRecursive.map g (PatternGuardRecursive.map f data)) := by
--     cases data; dsimp [PatternGuardRecursive.map]
--     simp only [Option.map_map, Function.comp_apply, Binder.map_comp]
--     congr 1; exact Expr.map_comp f g _

--   theorem LetInRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : LetInRecursive e1) : (LetInRecursive.map (g ∘ f) data) = (LetInRecursive.map g (LetInRecursive.map f data)) := by
--     cases data; dsimp [LetInRecursive.map]
--     simp only [NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]
--     congr 1
--     · congr; funext ⟨x, hx⟩; exact LetBindingRecursive.map_comp f g x.val
--     · exact Expr.map_comp f g _

--   theorem LetBindingRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (b : LetBindingRecursive e1) : (LetBindingRecursive.map (g ∘ f) b) = (LetBindingRecursive.map g (LetBindingRecursive.map f b)) := by
--     cases b
--     · dsimp [LetBindingRecursive.map]; simp only [Type_.map_comp, Labeled.map_value_comp_fun]
--     · dsimp [LetBindingRecursive.map]; congr 1; exact ValueBindingFieldsRecursive.map_comp f g _
--     · dsimp [LetBindingRecursive.map]; simp only [Binder.map_comp]; congr 2; exact WhereRecursive.map_comp f g _
--     · dsimp [LetBindingRecursive.map]

--   theorem ValueBindingFieldsRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : ValueBindingFieldsRecursive e1) : (ValueBindingFieldsRecursive.map (g ∘ f) data) = (ValueBindingFieldsRecursive.map g (ValueBindingFieldsRecursive.map f data)) := by
--     cases data; dsimp [ValueBindingFieldsRecursive.map]
--     simp only [Array.map_map, Function.comp_apply, Binder.map_comp]
--     congr 1; exact GuardedRecursive.map_comp f g _

--   theorem WhereRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : WhereRecursive e1) : (WhereRecursive.map (g ∘ f) data) = (WhereRecursive.map g (WhereRecursive.map f data)) := by
--     cases data; dsimp [WhereRecursive.map]
--     simp only [Option.map_map, NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]
--     congr 1
--     · exact Expr.map_comp f g _
--     · congr; funext ⟨t, bs⟩; simp only [Function.comp_apply]; congr 1
--       congr; funext ⟨x, hx⟩; exact LetBindingRecursive.map_comp f g x.val

--   theorem DoBlockRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : DoBlockRecursive e1) : (DoBlockRecursive.map (g ∘ f) data) = (DoBlockRecursive.map g (DoBlockRecursive.map f data)) := by
--     cases data; dsimp [DoBlockRecursive.map]
--     simp only [NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]
--     congr 1; funext ⟨x, hx⟩; exact DoStatementRecursive.map_comp f g x.val

--   theorem AdoBlockRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : AdoBlockRecursive e1) : (AdoBlockRecursive.map (g ∘ f) data) = (AdoBlockRecursive.map g (AdoBlockRecursive.map f data)) := by
--     cases data; dsimp [AdoBlockRecursive.map]
--     simp only [Array.attach_map, ← Array.comp_map]
--     congr 1
--     · congr; funext ⟨x, hx⟩; exact DoStatementRecursive.map_comp f g x.val
--     · exact Expr.map_comp f g _

--   theorem DoStatementRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (s : DoStatementRecursive e1) : (DoStatementRecursive.map (g ∘ f) s) = (DoStatementRecursive.map g (DoStatementRecursive.map f s)) := by
--     cases s
--     · dsimp [DoStatementRecursive.map]
--       simp only [NonEmptyArray.attach_map, ← NonEmptyArray.comp_map]
--       congr 1; funext ⟨x, hx⟩; exact LetBindingRecursive.map_comp f g x.val
--     · dsimp [DoStatementRecursive.map]; congr 1; exact Expr.map_comp f g _
--     · dsimp [DoStatementRecursive.map]; simp only [Binder.map_comp]; congr 2; exact Expr.map_comp f g _
--     · dsimp [DoStatementRecursive.map]
-- end

end PureScript.CST.Types

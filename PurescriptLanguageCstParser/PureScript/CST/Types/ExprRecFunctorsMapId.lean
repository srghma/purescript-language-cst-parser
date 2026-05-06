module

import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop
public import PurescriptLanguageCstParser.PureScript.CST.Types.PType
public import PurescriptLanguageCstParser.PureScript.CST.Types.ExprLeafs
public import PurescriptLanguageCstParser.PureScript.CST.Types.ExprRec
public import PurescriptLanguageCstParser.PureScript.CST.Types.ExprRecFunctorsMap
meta import PurescriptLanguageCstParser.GenerateFixed

@[expose] public section

namespace PureScript.CST.Types

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String
open PureScript.CST.Types


-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  id_map theorems                                                 ║
-- ╚══════════════════════════════════════════════════════════════════╝
set_option maxHeartbeats 900000
mutual
  theorem Expr.map_id {e : Type} (expr : Expr e) : Expr.map id expr = expr := by
    cases expr
    · simp only [Expr.map]   -- Hole
    · simp only [Expr.map]   -- Section
    · simp only [Expr.map]   -- Ident
    · simp only [Expr.map]   -- Constructor
    · simp only [Expr.map]   -- Boolean
    · simp only [Expr.map]   -- Char
    · simp only [Expr.map]   -- NonEmptyString
    · simp only [Expr.map]   -- Int
    · simp only [Expr.map]   -- Number
    · rename_i items; simp only [Expr.map]; rw [Expr.mapDelimited_id items]
    · rename_i fields; simp only [Expr.map]; rw [Expr.mapDelimitedRL_id fields]
    · rename_i w; simp only [Expr.map]
      have ih := Expr.map_id w.value
      cases w; simp only [ih]
    · rename_i e' t ty; simp only [Expr.map]
      have ih := Expr.map_id e'
      simp only [ih, Type_.map_id]
    · rename_i head tail; simp only [Expr.map]
      have ih_head := Expr.map_id head
      simp only [ih_head]
      have h : (fun we : { x // x ∈ tail } =>
            ({ we.val.1 with value := Expr.map id we.val.1.value }, Expr.map id we.val.2)) =
          fun we => we.val := by
        funext ⟨⟨w, e'⟩, hmem⟩
        have ih_w := Expr.map_id w.value
        have ih_e := Expr.map_id e'
        cases w; simp only [ih_w, ih_e]
      rw [h, NonEmptyArray.attach_map_val]
    · rename_i head ops; simp only [Expr.map]
      have ih_head := Expr.map_id head
      simp only [ih_head]
      have h : (fun ne : { x // x ∈ ops } => (ne.val.1, Expr.map id ne.val.2)) =
          fun ne => ne.val := by
        funext ⟨⟨n, e'⟩, hmem⟩
        have ih_e := Expr.map_id e'
        simp only [ih_e]
      rw [h, NonEmptyArray.attach_map_val]
    · simp only [Expr.map]   -- OpName
    · rename_i t e'; simp only [Expr.map]
      have ih := Expr.map_id e'
      simp only [ih]
    · rename_i data; simp only [Expr.map, RecordAccessorRecursive.map_id]
    · rename_i e' updates; simp only [Expr.map]
      have ih := Expr.map_id e'
      simp only [ih]
      have h : (fun u : { x // x ∈ updates } => RecordUpdateRecursive.map id u.val) =
          fun u => u.val := by
        funext ⟨u, _⟩; exact RecordUpdateRecursive.map_id u
      rw [h, DelimitedNonEmpty.attach_map_val]
    · rename_i fn args; simp only [Expr.map]
      have ih := Expr.map_id fn
      simp only [ih]
      have h : (fun a : { x // x ∈ args } => AppSpineRecursive.map id a.val) =
          fun a => a.val := by
        funext ⟨a, _⟩; exact AppSpineRecursive.map_id a
      rw [h, NonEmptyArray.attach_map_val]
    · rename_i data; simp only [Expr.map]; rw [LambdaRecursive.map_id data]
    · rename_i data; simp only [Expr.map]; rw [IfThenElseRecursive.map_id data]
    · rename_i data; simp only [Expr.map]; rw [CaseOfRecursive.map_id data]
    · rename_i data; simp only [Expr.map]; rw [LetInRecursive.map_id data]
    · rename_i data; simp only [Expr.map]; rw [DoBlockRecursive.map_id data]
    · rename_i data; simp only [Expr.map]; rw [AdoBlockRecursive.map_id data]
    · simp only [Expr.map, id_eq]
  termination_by sizeOf expr
  decreasing_by
    all_goals simp_wf
    all_goals simp_all only [Wrapped.sizeOf_value, NonEmptyArray.sizeOf_lt_of_mem,
      Array.sizeOf_lt_of_mem, DelimitedNonEmpty.sizeOf_attach_elem, Prod.mk.sizeOf_spec]
    all_goals try omega
    all_goals try decreasing_tactic
    ·
      rename_i h
      subst h
      simp_all
      all_goals try omega
      all_goals try decreasing_tactic
      all_goals aesop?
    ·
      rename_i h
      subst h
      simp_all
      all_goals try omega
      all_goals try decreasing_tactic
      all_goals aesop?
    ·
      rename_i h
      subst h
      simp_all
      all_goals try omega
      all_goals try decreasing_tactic
      all_goals aesop?
    ·
      rename_i h
      subst h
      simp_all
      all_goals try omega
      all_goals try decreasing_tactic
      all_goals aesop?

  theorem Expr.mapDelimited_id {e : Type} (d : Delimited (Expr e)) : Expr.mapDelimited id d = d := by
    cases d; rename_i w
    cases w with | mk open_ value close =>
    cases value with
    | none => simp only [Expr.mapDelimited]
    | some s =>
      simp only [Expr.mapDelimited]
      have h := Expr.mapSep_id s
      simp only [h]
  termination_by sizeOf d
  decreasing_by
    simp_wf
    simp only [Delimited.mk.sizeOf_spec, Wrapped.mk.sizeOf_spec, Option.some.sizeOf_spec] at *
    omega

  theorem Expr.mapSep_id {e : Type} (s : Separated (Expr e)) : Expr.mapSep id s = s := by
    cases s; rename_i head tail
    simp only [Expr.mapSep, Separated.mk.injEq]
    refine ⟨Expr.map_id head, ?_⟩
    have h : (fun x : { x // x ∈ tail } => (x.val.1, Expr.map id x.val.2)) = fun x => id x.val := by
      funext ⟨⟨tok, e'⟩, hmem⟩
      have ih_e := Expr.map_id e'
      simp only [ih_e, id_eq]
    rw [h, Array.attach_map_val]
    exact Array.map_id _
  termination_by sizeOf s
  decreasing_by
    · all_goals try omega; all_goals try decreasing_tactic; all_goals aesop?; exact Separated.sizeOf_head s
    · all_goals try omega; all_goals try decreasing_tactic; all_goals aesop?; simp_wf
      obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp hmem
      have : e' = s.tail[i].2 := by simp [h]
      rw [this]
      exact s.sizeOf_tail_get i hi

  theorem Expr.mapDelimitedRL_id {e : Type} (d : Delimited (RecordLabeled (Expr e))) : Expr.mapDelimitedRL id d = d := by
    cases d; rename_i w
    cases w with | mk open_ value close =>
    cases value with
    | none => simp only [Expr.mapDelimitedRL]
    | some s =>
      simp only [Expr.mapDelimitedRL]
      have h := Expr.mapSepRL_id s
      simp only [h]
  termination_by sizeOf d
  decreasing_by
    simp_wf
    simp only [Delimited.mk.sizeOf_spec, Wrapped.mk.sizeOf_spec, Option.some.sizeOf_spec] at *
    omega

  theorem Expr.mapSepRL_id {e : Type} (s : Separated (RecordLabeled (Expr e))) : Expr.mapSepRL id s = s := by
    cases s; rename_i head tail
    simp only [Expr.mapSepRL, Separated.mk.injEq]
    refine ⟨Expr.mapRL_id head, ?_⟩
    have h : (fun x : { x // x ∈ tail } => (x.val.1, Expr.mapRL id x.val.2)) = fun x => id x.val := by
      funext ⟨⟨tok, rl⟩, hmem⟩
      have ih_rl := Expr.mapRL_id rl
      simp only [ih_rl, id_eq]
    rw [h, Array.attach_map_val]
    exact Array.map_id _
  termination_by sizeOf s
  decreasing_by
    · all_goals try omega; all_goals try decreasing_tactic; all_goals aesop?; exact Separated.sizeOf_head s
    · all_goals try omega; all_goals try decreasing_tactic; all_goals aesop?; simp_wf
      obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp hmem
      have : rl = s.tail[i].2 := by simp [h]
      rw [this]
      exact s.sizeOf_tail_get i hi

  theorem Expr.mapRL_id {e : Type} (rl : RecordLabeled (Expr e)) : Expr.mapRL id rl = rl := by
    cases rl
    · simp only [Expr.mapRL]
    · simp only [Expr.mapRL, RecordLabeled.Field.injEq, true_and]
      exact Expr.map_id _
  termination_by sizeOf rl
  decreasing_by
    simp_wf; omega

  theorem RecordAccessorRecursive.map_id {e : Type} (data : RecordAccessorRecursive e) :
      RecordAccessorRecursive.map id data = data := by
    cases data
    simp only [RecordAccessorRecursive.map, RecordAccessorRecursive.mk.injEq, and_self, and_true]
    exact Expr.map_id _
  termination_by sizeOf data
  decreasing_by
    cases data <;> simp_wf <;> omega

  theorem RecordUpdateRecursive.map_id {e : Type} (u : RecordUpdateRecursive e) :
      RecordUpdateRecursive.map id u = u := by
    cases u
    · simp only [RecordUpdateRecursive.map, RecordUpdateRecursive.Leaf.injEq, true_and]
      exact Expr.map_id _
    · rename_i l updates
      simp only [RecordUpdateRecursive.map, RecordUpdateRecursive.Branch.injEq, true_and]
      have h : (fun u' : { x // x ∈ updates } => RecordUpdateRecursive.map id u'.val) =
          fun u' => u'.val := by
        funext ⟨u', _⟩
        exact RecordUpdateRecursive.map_id u'
      rw [h, DelimitedNonEmpty.attach_map_val]
  termination_by sizeOf u
  decreasing_by
    all_goals simp_wf
    all_goals simp_all only [DelimitedNonEmpty.sizeOf_attach_elem]
    all_goals try omega
    all_goals try decreasing_tactic
    all_goals aesop?

  theorem AppSpineRecursive.map_id {e : Type} (s : AppSpineRecursive e) : AppSpineRecursive.map id s = s := by
    cases s
    · simp only [AppSpineRecursive.map, Type_.map_id]
    · simp only [AppSpineRecursive.map, AppSpineRecursive.Term.injEq]
      exact Expr.map_id _
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf

  theorem LambdaRecursive.map_id {e : Type} (data : LambdaRecursive e) : LambdaRecursive.map id data = data := by
    cases data
    simp only [LambdaRecursive.map, LambdaRecursive.mk.injEq, true_and]
    have hb : Binder.map id = (id : Binder e → Binder e) := funext Binder.map_id
    have he : Expr.map id = (id : Expr e → Expr e) := funext Expr.map_id
    simp only [hb, he, NonEmptyArray.map, Array.map_id, id_eq, and_self]
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data
    simp_all only [LambdaRecursive.mk.sizeOf_spec, Nat.lt_add_left_iff_pos]
    all_goals try omega
    all_goals try decreasing_tactic
    all_goals aesop?

  theorem IfThenElseRecursive.map_id {e : Type} (data : IfThenElseRecursive e) :
      IfThenElseRecursive.map id data = data := by
    cases data
    simp only [IfThenElseRecursive.map, IfThenElseRecursive.mk.injEq, true_and]
    exact ⟨Expr.map_id _, Expr.map_id _, Expr.map_id _⟩
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals cases data
    all_goals simp_wf
    all_goals omega

  theorem CaseOfRecursive.map_id {e : Type} (data : CaseOfRecursive e) : CaseOfRecursive.map id data = data := by
    cases data
    rename_i keyword head of_ branches
    simp only [CaseOfRecursive.map, CaseOfRecursive.mk.injEq, true_and]
    refine ⟨Expr.mapSep_id head, ?_⟩
    have h : (fun x : { x // x ∈ branches } =>
          (x.val.1.map (Binder.map id), GuardedRecursive.map id x.val.2)) = fun x => x.val := by
      funext ⟨⟨b, g⟩, _⟩
      have hb : Binder.map id = (id : Binder e → Binder e) := funext Binder.map_id
      simp only [hb, Separated.map_id_fun, GuardedRecursive.map_id, id_eq]
    rw [h, NonEmptyArray.attach_map_val]
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    · cases data
      simp_wf
      omega
    · cases data
      simp_wf
      simp_all only [NonEmptyArray.sizeOf_lt_of_mem, Prod.mk.sizeOf_spec]
      omega

  theorem GuardedRecursive.map_id {e : Type} (g : GuardedRecursive e) : GuardedRecursive.map id g = g := by
    cases g
    · simp only [GuardedRecursive.map, GuardedRecursive.Unconditional.injEq, true_and]
      exact WhereRecursive.map_id _
    · rename_i patterns
      simp only [GuardedRecursive.map, GuardedRecursive.Guarded.injEq]
      have h : (fun b : { x // x ∈ patterns } => GuardedExprRecursive.map id b.val) =
          fun b => b.val := by
        funext ⟨b, _⟩
        exact GuardedExprRecursive.map_id b
      rw [h, NonEmptyArray.attach_map_val]
  termination_by sizeOf g
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    all_goals try decreasing_tactic
    · grind only
    -- all_goals simp_all only [NonEmptyArray.sizeOf_lt_of_mem]
    -- all_goals omega

  theorem GuardedExprRecursive.map_id {e : Type} (data : GuardedExprRecursive e) :
      GuardedExprRecursive.map id data = data := by
    cases data
    rename_i bar patterns separator where_
    simp only [GuardedExprRecursive.map, GuardedExprRecursive.mk.injEq, true_and]
    refine ⟨?_, WhereRecursive.map_id _⟩
    have h : (fun p : { x // x ∈ patterns } => PatternGuardRecursive.map id p.val) =
        fun p => p.val := by
      funext ⟨p, _⟩
      exact PatternGuardRecursive.map_id p
    rw [h, Separated.attach_map_val]
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals simp_all only [Separated.sizeOf_attach_elem]
    all_goals try omega
    all_goals try decreasing_tactic
    rename_i h property
    subst h
    simp_all
    cases property with
    | inl h =>
      subst h
      try omega
      aesop?
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      try omega
      aesop?
    all_goals omega

  theorem PatternGuardRecursive.map_id {e : Type} (data : PatternGuardRecursive e) :
      PatternGuardRecursive.map id data = data := by
    cases data
    rename_i binder expr
    simp only [PatternGuardRecursive.map, PatternGuardRecursive.mk.injEq]
    refine ⟨?_, Expr.map_id _⟩
    match binder with
    | none => rfl
    | some ⟨b, t⟩ =>
        change some (Binder.map id b, t) = some (b, t)
        rw [Binder.map_id]
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals omega
    all_goals try omega
    all_goals try decreasing_tactic

  theorem LetInRecursive.map_id {e : Type} (data : LetInRecursive e) : LetInRecursive.map id data = data := by
    cases data
    rename_i keyword bindings in_ body
    simp only [LetInRecursive.map, LetInRecursive.mk.injEq, true_and]
    refine ⟨?_, Expr.map_id _⟩
    have h : (fun b : { x // x ∈ bindings } => LetBindingRecursive.map id b.val) =
        fun b => b.val := by
      funext ⟨b, _⟩
      exact LetBindingRecursive.map_id b
    rw [h, NonEmptyArray.attach_map_val]
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals simp_all only [NonEmptyArray.sizeOf_lt_of_mem]
    all_goals try omega
    all_goals try decreasing_tactic
    all_goals omega

  theorem LetBindingRecursive.map_id {e : Type} (b : LetBindingRecursive e) : LetBindingRecursive.map id b = b := by
    cases b with
    | Signature labeled =>
        cases labeled
        simp only [LetBindingRecursive.map, Labeled.map_value, Type_.map_id]
    | Name fields =>
        simp only [LetBindingRecursive.map, ValueBindingFieldsRecursive.map_id]
    | Pattern binder token where_ =>
        simp only [LetBindingRecursive.map, Binder.map_id, WhereRecursive.map_id]
    | Error data =>
        simp only [LetBindingRecursive.map, id_eq]
  termination_by sizeOf b
  decreasing_by
    all_goals try simp_wf
    all_goals try omega
    all_goals try decreasing_tactic
    · simp_all only [LetBindingRecursive.Name.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
      rename_i h
      subst h
      simp_all
      try omega
      try decreasing_tactic
      aesop?
    · simp_all only [LetBindingRecursive.Pattern.sizeOf_spec, Nat.lt_add_left_iff_pos]
      rename_i h
      subst h
      simp_all
      try omega
      try decreasing_tactic
      aesop?

  theorem ValueBindingFieldsRecursive.map_id {e : Type} (data : ValueBindingFieldsRecursive e) :
      ValueBindingFieldsRecursive.map id data = data := by
    cases data
    rename_i name binders guarded
    simp only [ValueBindingFieldsRecursive.map, ValueBindingFieldsRecursive.mk.injEq, true_and]
    refine ⟨?_, GuardedRecursive.map_id guarded⟩
    have h : (fun b : { x // x ∈ binders } => Binder.map id b.val) = fun b => b.val := by
      funext ⟨b, _⟩
      exact Binder.map_id b
    rw [h]
    simpa using Array.attach_map_val binders
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data
    simp_all only [ValueBindingFieldsRecursive.mk.sizeOf_spec, Nat.lt_add_left_iff_pos]
    omega

  theorem WhereRecursive.map_id {e : Type} (data : WhereRecursive e) : WhereRecursive.map id data = data := by
    cases data
    rename_i expr bindings
    simp only [WhereRecursive.map, WhereRecursive.mk.injEq]
    refine ⟨Expr.map_id expr, ?_⟩
    match bindings with
    | none => rfl
    | some ⟨t, bs⟩ =>
        change some (t, bs.attach.map (fun ⟨b, _⟩ => LetBindingRecursive.map id b)) = some (t, bs)
        have h : (fun b : { x // x ∈ bs } => LetBindingRecursive.map id b.val) = fun b => b.val := by
          funext ⟨b, _⟩
          exact LetBindingRecursive.map_id b
        rw [h, NonEmptyArray.attach_map_val]
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals simp_all only [WhereRecursive.mk.sizeOf_spec, Option.some.sizeOf_spec,
      Prod.mk.sizeOf_spec, NonEmptyArray.sizeOf_lt_of_mem]
    all_goals try omega
    all_goals try decreasing_tactic
    all_goals aesop?

  theorem DoBlockRecursive.map_id {e : Type} (data : DoBlockRecursive e) : DoBlockRecursive.map id data = data := by
    cases data
    rename_i keyword statements
    simp only [DoBlockRecursive.map, DoBlockRecursive.mk.injEq, true_and]
    have h : (fun s : { x // x ∈ statements } => DoStatementRecursive.map id s.val) = fun s => s.val := by
      funext ⟨s, _⟩
      exact DoStatementRecursive.map_id s
    rw [h, NonEmptyArray.attach_map_val]
  termination_by sizeOf data
  decreasing_by
    simp_wf
    simp_all only [NonEmptyArray.sizeOf_lt_of_mem]
    all_goals try omega
    all_goals try decreasing_tactic
    all_goals aesop?

  theorem AdoBlockRecursive.map_id {e : Type} (data : AdoBlockRecursive e) : AdoBlockRecursive.map id data = data := by
    cases data
    rename_i keyword statements in_ result
    simp only [AdoBlockRecursive.map]
    have h : (fun s : { x // x ∈ statements } => DoStatementRecursive.map id s.val) = fun s => s.val := by
      funext ⟨s, _⟩
      exact DoStatementRecursive.map_id s
    rw [h]
    simpa [Expr.map_id] using
      congrArg
        (fun sts => ({ keyword := keyword, statements := sts, in_ := in_, result := Expr.map id result } :
          AdoBlockRecursive e))
        (Array.attach_map_val statements)
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals simp_all only [Array.sizeOf_lt_of_mem]
    all_goals try omega
    all_goals try decreasing_tactic
    all_goals aesop?

  theorem DoStatementRecursive.map_id {e : Type} (s : DoStatementRecursive e) : DoStatementRecursive.map id s = s := by
    cases s
    · rename_i t bs
      simp only [DoStatementRecursive.map]
      have h : (fun b : { x // x ∈ bs } => LetBindingRecursive.map id b.val) = fun b => b.val := by
        funext ⟨b, _⟩
        exact LetBindingRecursive.map_id b
      rw [h, NonEmptyArray.attach_map_val]
    · simp only [DoStatementRecursive.map, Expr.map_id]
    · simp only [DoStatementRecursive.map, Binder.map_id, Expr.map_id]
    · simp only [DoStatementRecursive.map, id_eq]
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf
    all_goals simp_all only [NonEmptyArray.sizeOf_lt_of_mem]
    all_goals omega
end

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  comp_map theorems                                               ║
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

-- instance : Functor Expr where map := Expr.map
-- instance : LawfulFunctor Expr where
--   map_const := rfl
--   id_map := Expr.map_id
--   comp_map := Expr.map_comp

-- instance : Functor RecordAccessorRecursive where map := RecordAccessorRecursive.map
-- instance : LawfulFunctor RecordAccessorRecursive where
--   map_const := rfl
--   id_map := RecordAccessorRecursive.map_id
--   comp_map := RecordAccessorRecursive.map_comp

-- instance : Functor RecordUpdateRecursive where map := RecordUpdateRecursive.map
-- instance : LawfulFunctor RecordUpdateRecursive where
--   map_const := rfl
--   id_map := RecordUpdateRecursive.map_id
--   comp_map := RecordUpdateRecursive.map_comp

-- instance : Functor AppSpineRecursive where map := AppSpineRecursive.map
-- instance : LawfulFunctor AppSpineRecursive where
--   map_const := rfl
--   id_map := AppSpineRecursive.map_id
--   comp_map := AppSpineRecursive.map_comp

-- instance : Functor LambdaRecursive where map := LambdaRecursive.map
-- instance : LawfulFunctor LambdaRecursive where
--   map_const := rfl
--   id_map := LambdaRecursive.map_id
--   comp_map := LambdaRecursive.map_comp

-- instance : Functor IfThenElseRecursive where map := IfThenElseRecursive.map
-- instance : LawfulFunctor IfThenElseRecursive where
--   map_const := rfl
--   id_map := IfThenElseRecursive.map_id
--   comp_map := IfThenElseRecursive.map_comp

-- instance : Functor CaseOfRecursive where map := CaseOfRecursive.map
-- instance : LawfulFunctor CaseOfRecursive where
--   map_const := rfl
--   id_map := CaseOfRecursive.map_id
--   comp_map := CaseOfRecursive.map_comp

-- instance : Functor GuardedRecursive where map := GuardedRecursive.map
-- instance : LawfulFunctor GuardedRecursive where
--   map_const := rfl
--   id_map := GuardedRecursive.map_id
--   comp_map := GuardedRecursive.map_comp

-- instance : Functor GuardedExprRecursive where map := GuardedExprRecursive.map
-- instance : LawfulFunctor GuardedExprRecursive where
--   map_const := rfl
--   id_map := GuardedExprRecursive.map_id
--   comp_map := GuardedExprRecursive.map_comp

-- instance : Functor PatternGuardRecursive where map := PatternGuardRecursive.map
-- instance : LawfulFunctor PatternGuardRecursive where
--   map_const := rfl
--   id_map := PatternGuardRecursive.map_id
--   comp_map := PatternGuardRecursive.map_comp

-- instance : Functor LetInRecursive where map := LetInRecursive.map
-- instance : LawfulFunctor LetInRecursive where
--   map_const := rfl
--   id_map := LetInRecursive.map_id
--   comp_map := LetInRecursive.map_comp

-- instance : Functor LetBindingRecursive where map := LetBindingRecursive.map
-- instance : LawfulFunctor LetBindingRecursive where
--   map_const := rfl
--   id_map := LetBindingRecursive.map_id
--   comp_map := LetBindingRecursive.map_comp

-- instance : Functor ValueBindingFieldsRecursive where map := ValueBindingFieldsRecursive.map
-- instance : LawfulFunctor ValueBindingFieldsRecursive where
--   map_const := rfl
--   id_map := ValueBindingFieldsRecursive.map_id
--   comp_map := ValueBindingFieldsRecursive.map_comp

-- instance : Functor WhereRecursive where map := WhereRecursive.map
-- instance : LawfulFunctor WhereRecursive where
--   map_const := rfl
--   id_map := WhereRecursive.map_id
--   comp_map := WhereRecursive.map_comp

-- instance : Functor DoBlockRecursive where map := DoBlockRecursive.map
-- instance : LawfulFunctor DoBlockRecursive where
--   map_const := rfl
--   id_map := DoBlockRecursive.map_id
--   comp_map := DoBlockRecursive.map_comp

-- instance : Functor AdoBlockRecursive where map := AdoBlockRecursive.map
-- instance : LawfulFunctor AdoBlockRecursive where
--   map_const := rfl
--   id_map := AdoBlockRecursive.map_id
--   comp_map := AdoBlockRecursive.map_comp

-- instance : Functor DoStatementRecursive where map := DoStatementRecursive.map
-- instance : LawfulFunctor DoStatementRecursive where
--   map_const := rfl
--   id_map := DoStatementRecursive.map_id
--   comp_map := DoStatementRecursive.map_comp

end PureScript.CST.Types

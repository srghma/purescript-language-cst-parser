module

import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop
public import PurescriptLanguageCstParser.PureScript.CST.Types.PType
public import PurescriptLanguageCstParser.PureScript.CST.Types.ExprLeafs
public import PurescriptLanguageCstParser.PureScript.CST.Types.ExprRec
meta import PurescriptLanguageCstParser.GenerateFixed

@[expose] public section

namespace PureScript.CST.Types

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String
open PureScript.CST.Types

mutual
  def Expr.map {e1 e2 : Type} (f : e1 → e2) (expr : Expr e1) : Expr e2 :=
    match expr with
    | .Hole n => .Hole n
    | .Section t => .Section t
    | .Ident n => .Ident n
    | .Constructor n => .Constructor n
    | .Boolean t v => .Boolean t v
    | .Char t v => .Char t v
    | .NonEmptyString t v => .NonEmptyString t v
    | .Int t v => .Int t v
    | .Number t v => .Number t v
    | .Array items => .Array (items.map (Expr.map f))
    | .Record fields => .Record (fields.map (fun r => { r with value := r.value.map f }))
    | .Parens wrapped => .Parens { wrapped with value := wrapped.value.map f }
    | .Typed expr t ty => .Typed (expr.map f) t ty
    | .Infix head tail => .Infix (head.map f) (tail.map (fun (w, e) => ({ w with value := w.value.map f }, e.map f)))
    | .Op head ops => .Op (head.map f) (ops.map (fun (n, e) => (n, e.map f)))
    | .OpName n => .OpName n
    | .Negate t e' => .Negate t (e'.map f)
    | .RecordAccessor data => .RecordAccessor (RecordAccessorRecursive.map f data)
    | .RecordUpdate expr updates => .RecordUpdate (expr.map f) (updates.map (RecordUpdateRecursive.map f))
    | .App fn args => .App (fn.map f) (args.map (AppSpineRecursive.map f))
    | .Lambda data => .Lambda (LambdaRecursive.map f data)
    | .If data => .If (IfThenElseRecursive.map f data)
    | .Case data => .Case (CaseOfRecursive.map f data)
    | .Let data => .Let (LetInRecursive.map f data)
    | .Do data => .Do (DoBlockRecursive.map f data)
    | .Ado data => .Ado (AdoBlockRecursive.map f data)
    | .Error data => .Error (f data)

  def RecordAccessorRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : RecordAccessorRecursive e1) : RecordAccessorRecursive e2 :=
    { expr := data.expr.map f, dot := data.dot, path := data.path }

  def RecordUpdateRecursive.map {e1 e2 : Type} (f : e1 → e2) (u : RecordUpdateRecursive e1) : RecordUpdateRecursive e2 :=
    match u with
    | .Leaf l t e' => .Leaf l t (e'.map f)
    | .Branch l updates => .Branch l (updates.map (RecordUpdateRecursive.map f))

  def AppSpineRecursive.map {e1 e2 : Type} (f : e1 → e2) (s : AppSpineRecursive e1) : AppSpineRecursive e2 :=
    match s with
    | .Type_ t ty => .Type_ t ty
    | .Term e' => .Term (e'.map f)

  def LambdaRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : LambdaRecursive e1) : LambdaRecursive e2 :=
    { symbol := data.symbol, binders := data.binders.map (fun b => b.map f), arrow := data.arrow, body := data.body.map f }

  def IfThenElseRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : IfThenElseRecursive e1) : IfThenElseRecursive e2 :=
    { keyword := data.keyword, cond := data.cond.map f, then_ := data.then_, true_ := data.true_.map f, else_ := data.else_, false_ := data.false_.map f }

  def CaseOfRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : CaseOfRecursive e1) : CaseOfRecursive e2 :=
    { keyword := data.keyword, head := data.head.map (Expr.map f), of := data.of, branches := data.branches.map (fun (b, g) => (b.map (Expr.map f), g.map f)) }

  def GuardedRecursive.map {e1 e2 : Type} (f : e1 → e2) (g : GuardedRecursive e1) : GuardedRecursive e2 :=
    match g with
    | .Unconditional t w => .Unconditional t (WhereRecursive.map f w)
    | .Guarded branches => .Guarded (branches.map (GuardedExprRecursive.map f))

  def GuardedExprRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : GuardedExprRecursive e1) : GuardedExprRecursive e2 :=
    { bar := data.bar, patterns := data.patterns.map (PatternGuardRecursive.map f), separator := data.separator, where_ := data.where_.map f }

  def PatternGuardRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : PatternGuardRecursive e1) : PatternGuardRecursive e2 :=
    { binder := data.binder.map (fun (b, t) => (b.map f, t)), expr := data.expr.map f }

  def LetInRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : LetInRecursive e1) : LetInRecursive e2 :=
    { keyword := data.keyword, bindings := data.bindings.map (LetBindingRecursive.map f), in_ := data.in_, body := data.body.map f }

  def LetBindingRecursive.map {e1 e2 : Type} (f : e1 → e2) (b : LetBindingRecursive e1) : LetBindingRecursive e2 :=
    match b with
    | .Signature l => .Signature l
    | .Name fields => .Name (ValueBindingFieldsRecursive.map f fields)
    | .Pattern b t w => .Pattern (b.map f) t (WhereRecursive.map f w)
    | .Error d => .Error (f d)

  def ValueBindingFieldsRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : ValueBindingFieldsRecursive e1) : ValueBindingFieldsRecursive e2 :=
    { name := data.name, binders := data.binders.map (fun b => b.map f), guarded := data.guarded.map f }

  def WhereRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : WhereRecursive e1) : WhereRecursive e2 :=
    { expr := data.expr.map f, bindings := data.bindings.map (fun (t, bs) => (t, bs.map (LetBindingRecursive.map f))) }

  def DoBlockRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : DoBlockRecursive e1) : DoBlockRecursive e2 :=
    { keyword := data.keyword, statements := data.statements.map (DoStatementRecursive.map f) }

  def AdoBlockRecursive.map {e1 e2 : Type} (f : e1 → e2) (data : AdoBlockRecursive e1) : AdoBlockRecursive e2 :=
    { keyword := data.keyword, statements := data.statements.map (DoStatementRecursive.map f), in_ := data.in_, result := data.result.map f }

  def DoStatementRecursive.map {e1 e2 : Type} (f : e1 → e2) (s : DoStatementRecursive e1) : DoStatementRecursive e2 :=
    match s with
    | .Let t bs => .Let t (bs.map (LetBindingRecursive.map f))
    | .Discard e' => .Discard (e'.map f)
    | .Bind b t e' => .Bind (b.map f) t (e'.map f)
    | .Error d => .Error (f d)
end

instance : Functor Expr where map := Expr.map
instance : Functor RecordAccessorRecursive where map := RecordAccessorRecursive.map
instance : Functor RecordUpdateRecursive where map := RecordUpdateRecursive.map
instance : Functor AppSpineRecursive where map := AppSpineRecursive.map
instance : Functor LambdaRecursive where map := LambdaRecursive.map
instance : Functor IfThenElseRecursive where map := IfThenElseRecursive.map
instance : Functor CaseOfRecursive where map := CaseOfRecursive.map
instance : Functor GuardedRecursive where map := GuardedRecursive.map
instance : Functor GuardedExprRecursive where map := GuardedExprRecursive.map
instance : Functor PatternGuardRecursive where map := PatternGuardRecursive.map
instance : Functor LetInRecursive where map := LetInRecursive.map
instance : Functor LetBindingRecursive where map := LetBindingRecursive.map
instance : Functor ValueBindingFieldsRecursive where map := ValueBindingFieldsRecursive.map
instance : Functor WhereRecursive where map := WhereRecursive.map
instance : Functor DoBlockRecursive where map := DoBlockRecursive.map
instance : Functor AdoBlockRecursive where map := AdoBlockRecursive.map
instance : Functor DoStatementRecursive where map := DoStatementRecursive.map

mutual
  theorem Expr.map_id {e : Type} (expr : Expr e) : expr.map id = expr := by
    match expr with
    | .Hole _ | .Section _ | .Ident _ | .Constructor _ | .Boolean _ _ | .Char _ _ | .NonEmptyString _ _ | .Int _ _ | .Number _ _ | .OpName _ => rfl
    | .Array items => simp only [map, id_eq, Delimited.map_id, Expr.map_id]
    | .Record fields => simp only [map, id_eq, Delimited.id_map, RecordLabeled.id_map, Expr.map_id]
    | .Parens w => simp only [map, id_eq, Wrapped.id_map, Expr.map_id]
    | .Typed expr t ty => simp only [map, id_eq, Expr.map_id, Type_.id_map]
    | .Infix head tail => simp only [map, id_eq, Expr.map_id, NonEmptyArray.id_map, Wrapped.id_map]
    | .Op head ops => simp only [map, id_eq, Expr.map_id, NonEmptyArray.id_map]
    | .Negate t e' => simp only [map, id_eq, Expr.map_id]
    | .RecordAccessor data => simp only [map, id_eq, RecordAccessorRecursive.map_id]
    | .RecordUpdate expr updates => simp only [map, id_eq, Expr.map_id, DelimitedNonEmpty.id_map, RecordUpdateRecursive.map_id]
    | .App fn args => simp only [map, id_eq, Expr.map_id, NonEmptyArray.id_map, AppSpineRecursive.map_id]
    | .Lambda data => simp only [map, id_eq, LambdaRecursive.map_id]
    | .If data => simp only [map, id_eq, IfThenElseRecursive.map_id]
    | .Case data => simp only [map, id_eq, CaseOfRecursive.map_id]
    | .Let data => simp only [map, id_eq, LetInRecursive.map_id]
    | .Do data => simp only [map, id_eq, DoBlockRecursive.map_id]
    | .Ado data => simp only [map, id_eq, AdoBlockRecursive.map_id]
    | .Error d => rfl

  theorem RecordAccessorRecursive.map_id {e : Type} (data : RecordAccessorRecursive e) : data.map id = data := by
    match data with | { expr, dot, path } => simp only [map, Expr.map_id, id_eq]

  theorem RecordUpdateRecursive.map_id {e : Type} (u : RecordUpdateRecursive e) : u.map id = u := by
    match u with
    | .Leaf l t e' => simp only [map, Expr.map_id, id_eq]
    | .Branch l updates => simp only [map, DelimitedNonEmpty.id_map, RecordUpdateRecursive.map_id]

  theorem AppSpineRecursive.map_id {e : Type} (s : AppSpineRecursive e) : s.map id = s := by
    match s with
    | .Type_ t ty => simp only [map, id_eq]
    | .Term e' => simp only [map, Expr.map_id]

  theorem LambdaRecursive.map_id {e : Type} (data : LambdaRecursive e) : data.map id = data := by
    match data with | { symbol, binders, arrow, body } => simp only [map, Binder.id_map, NonEmptyArray.id_map, Expr.map_id, id_eq]

  theorem IfThenElseRecursive.map_id {e : Type} (data : IfThenElseRecursive e) : data.map id = data := by
    match data with | { keyword, cond, then_, true_, else_, false_ } => simp only [map, Expr.map_id, id_eq]

  theorem CaseOfRecursive.map_id {e : Type} (data : CaseOfRecursive e) : data.map id = data := by
    match data with | { keyword, head, of, branches } => simp only [map, Expr.map_id, Separated.id_map, Binder.id_map, GuardedRecursive.map_id, NonEmptyArray.id_map, id_eq]

  theorem GuardedRecursive.map_id {e : Type} (g : GuardedRecursive e) : g.map id = g := by
    match g with
    | .Unconditional t w => simp only [map, WhereRecursive.map_id, id_eq]
    | .Guarded branches => simp only [map, NonEmptyArray.id_map, GuardedExprRecursive.map_id]

  theorem GuardedExprRecursive.map_id {e : Type} (data : GuardedExprRecursive e) : data.map id = data := by
    match data with | { bar, patterns, separator, where_ } => simp only [map, Separated.id_map, PatternGuardRecursive.map_id, WhereRecursive.map_id, id_eq]

  theorem PatternGuardRecursive.map_id {e : Type} (data : PatternGuardRecursive e) : data.map id = data := by
    match data with | { binder, expr } => simp only [map, Expr.map_id, Binder.id_map, id_eq]

  theorem LetInRecursive.map_id {e : Type} (data : LetInRecursive e) : data.map id = data := by
    match data with | { keyword, bindings, in_, body } => simp only [map, NonEmptyArray.id_map, LetBindingRecursive.map_id, Expr.map_id, id_eq]

  theorem LetBindingRecursive.map_id {e : Type} (b : LetBindingRecursive e) : b.map id = b := by
    match b with
    | .Signature l => rfl
    | .Name fields => simp only [map, ValueBindingFieldsRecursive.map_id]
    | .Pattern b t w => simp only [map, Binder.id_map, WhereRecursive.map_id]
    | .Error d => rfl

  theorem ValueBindingFieldsRecursive.map_id {e : Type} (data : ValueBindingFieldsRecursive e) : data.map id = data := by
    match data with | { name, binders, guarded } => simp only [map, Binder.id_map, GuardedRecursive.map_id, id_eq]

  theorem WhereRecursive.map_id {e : Type} (data : WhereRecursive e) : data.map id = data := by
    match data with | { expr, bindings } => simp only [map, Expr.map_id, NonEmptyArray.id_map, LetBindingRecursive.map_id, id_eq]

  theorem DoBlockRecursive.map_id {e : Type} (data : DoBlockRecursive e) : data.map id = data := by
    match data with | { keyword, statements } => simp only [map, NonEmptyArray.id_map, DoStatementRecursive.map_id, id_eq]

  theorem AdoBlockRecursive.map_id {e : Type} (data : AdoBlockRecursive e) : data.map id = data := by
    match data with | { keyword, statements, in_, result } => simp only [map, DoStatementRecursive.map_id, Expr.map_id, id_eq]

  theorem DoStatementRecursive.map_id {e : Type} (s : DoStatementRecursive e) : s.map id = s := by
    match s with
    | .Let t bs => simp only [map, NonEmptyArray.id_map, LetBindingRecursive.map_id]
    | .Discard e' => simp only [map, Expr.map_id]
    | .Bind b t e' => simp only [map, Binder.id_map, Expr.map_id]
    | .Error d => rfl

mutual
  theorem Expr.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (expr : Expr e1) : (expr.map (g ∘ f)) = (expr.map f |>.map g) := by
    match expr with
    | .Hole _ | .Section _ | .Ident _ | .Constructor _ | .Boolean _ _ | .Char _ _ | .NonEmptyString _ _ | .Int _ _ | .Number _ _ | .OpName _ => rfl
    | .Array items => simp only [map, Delimited.map_comp, Expr.map_comp]
    | .Record fields => simp only [map, Delimited.comp_map, RecordLabeled.comp_map, Expr.map_comp]
    | .Parens w => simp only [map, Wrapped.comp_map, Expr.map_comp]
    | .Typed expr t ty => simp only [map, Expr.map_comp, Type_.comp_map]
    | .Infix head tail => simp only [map, Expr.map_comp, NonEmptyArray.comp_map, Wrapped.comp_map]
    | .Op head ops => simp only [map, Expr.map_comp, NonEmptyArray.comp_map]
    | .Negate t e' => simp only [map, Expr.map_comp]
    | .RecordAccessor data => simp only [map, RecordAccessorRecursive.map_comp]
    | .RecordUpdate expr updates => simp only [map, Expr.map_comp, DelimitedNonEmpty.comp_map, RecordUpdateRecursive.map_comp]
    | .App fn args => simp only [map, Expr.map_comp, NonEmptyArray.comp_map, AppSpineRecursive.map_comp]
    | .Lambda data => simp only [map, LambdaRecursive.map_comp]
    | .If data => simp only [map, IfThenElseRecursive.map_comp]
    | .Case data => simp only [map, CaseOfRecursive.map_comp]
    | .Let data => simp only [map, LetInRecursive.map_comp]
    | .Do data => simp only [map, DoBlockRecursive.map_comp]
    | .Ado data => simp only [map, AdoBlockRecursive.map_comp]
    | .Error d => rfl

  theorem RecordAccessorRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : RecordAccessorRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { expr, dot, path } => simp only [map, Expr.map_comp]

  theorem RecordUpdateRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (u : RecordUpdateRecursive e1) : (u.map (g ∘ f)) = (u.map f |>.map g) := by
    match u with
    | .Leaf l t e' => simp only [map, Expr.map_comp]
    | .Branch l updates => simp only [map, DelimitedNonEmpty.comp_map, RecordUpdateRecursive.map_comp]

  theorem AppSpineRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (s : AppSpineRecursive e1) : (s.map (g ∘ f)) = (s.map f |>.map g) := by
    match s with
    | .Type_ t ty => simp only [map]
    | .Term e' => simp only [map, Expr.map_comp]

  theorem LambdaRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : LambdaRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { symbol, binders, arrow, body } => simp only [map, Binder.comp_map, NonEmptyArray.comp_map, Expr.map_comp]

  theorem IfThenElseRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : IfThenElseRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { keyword, cond, then_, true_, else_, false_ } => simp only [map, Expr.map_comp]

  theorem CaseOfRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : CaseOfRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { keyword, head, of, branches } => simp only [map, Expr.map_comp, Separated.comp_map, Binder.comp_map, GuardedRecursive.map_comp, NonEmptyArray.comp_map]

  theorem GuardedRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (guarded : GuardedRecursive e1) : (guarded.map (g ∘ f)) = (guarded.map f |>.map g) := by
    match guarded with
    | .Unconditional t w => simp only [map, WhereRecursive.map_comp]
    | .Guarded branches => simp only [map, NonEmptyArray.comp_map, GuardedExprRecursive.map_comp]

  theorem GuardedExprRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : GuardedExprRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { bar, patterns, separator, where_ } => simp only [map, Separated.comp_map, PatternGuardRecursive.map_comp, WhereRecursive.map_comp]

  theorem PatternGuardRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : PatternGuardRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { binder, expr } => simp only [map, Expr.map_comp, Binder.comp_map]

  theorem LetInRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : LetInRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { keyword, bindings, in_, body } => simp only [map, NonEmptyArray.comp_map, LetBindingRecursive.map_comp, Expr.map_comp]

  theorem LetBindingRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (b : LetBindingRecursive e1) : (b.map (g ∘ f)) = (b.map f |>.map g) := by
    match b with
    | .Signature l => rfl
    | .Name fields => simp only [map, ValueBindingFieldsRecursive.map_comp]
    | .Pattern b t w => simp only [map, Binder.comp_map, WhereRecursive.map_comp]
    | .Error d => rfl

  theorem ValueBindingFieldsRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : ValueBindingFieldsRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { name, binders, guarded } => simp only [map, Binder.comp_map, GuardedRecursive.map_comp]

  theorem WhereRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : WhereRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { expr, bindings } => simp only [map, Expr.map_comp, NonEmptyArray.comp_map, LetBindingRecursive.map_comp]

  theorem DoBlockRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : DoBlockRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { keyword, statements } => simp only [map, NonEmptyArray.comp_map, DoStatementRecursive.map_comp]

  theorem AdoBlockRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (data : AdoBlockRecursive e1) : (data.map (g ∘ f)) = (data.map f |>.map g) := by
    match data with | { keyword, statements, in_, result } => simp only [map, DoStatementRecursive.map_comp, Expr.map_comp]

  theorem DoStatementRecursive.map_comp {e1 e2 e3 : Type} (f : e1 → e2) (g : e2 → e3) (s : DoStatementRecursive e1) : (s.map (g ∘ f)) = (s.map f |>.map g) := by
    match s with
    | .Let t bs => simp only [map, NonEmptyArray.comp_map, LetBindingRecursive.map_comp]
    | .Discard e' => simp only [map, Expr.map_comp]
    | .Bind b t e' => simp only [map, Binder.comp_map, Expr.map_comp]
    | .Error d => rfl
end

instance : LawfulFunctor Expr where
  id_map := Expr.map_id
  comp_map := Expr.map_comp
  map_const := rfl

instance : LawfulFunctor RecordAccessorRecursive where id_map := RecordAccessorRecursive.map_id; comp_map := RecordAccessorRecursive.map_comp; map_const := rfl
instance : LawfulFunctor RecordUpdateRecursive where id_map := RecordUpdateRecursive.map_id; comp_map := RecordUpdateRecursive.map_comp; map_const := rfl
instance : LawfulFunctor AppSpineRecursive where id_map := AppSpineRecursive.map_id; comp_map := AppSpineRecursive.map_comp; map_const := rfl
instance : LawfulFunctor LambdaRecursive where id_map := LambdaRecursive.map_id; comp_map := LambdaRecursive.map_comp; map_const := rfl
instance : LawfulFunctor IfThenElseRecursive where id_map := IfThenElseRecursive.map_id; comp_map := IfThenElseRecursive.map_comp; map_const := rfl
instance : LawfulFunctor CaseOfRecursive where id_map := CaseOfRecursive.map_id; comp_map := CaseOfRecursive.map_comp; map_const := rfl
instance : LawfulFunctor GuardedRecursive where id_map := GuardedRecursive.map_id; comp_map := GuardedRecursive.map_comp; map_const := rfl
instance : LawfulFunctor GuardedExprRecursive where id_map := GuardedExprRecursive.map_id; comp_map := GuardedExprRecursive.map_comp; map_const := rfl
instance : LawfulFunctor PatternGuardRecursive where id_map := PatternGuardRecursive.map_id; comp_map := PatternGuardRecursive.map_comp; map_const := rfl
instance : LawfulFunctor LetInRecursive where id_map := LetInRecursive.map_id; comp_map := LetInRecursive.map_comp; map_const := rfl
instance : LawfulFunctor LetBindingRecursive where id_map := LetBindingRecursive.map_id; comp_map := LetBindingRecursive.map_comp; map_const := rfl
instance : LawfulFunctor ValueBindingFieldsRecursive where id_map := ValueBindingFieldsRecursive.map_id; comp_map := ValueBindingFieldsRecursive.map_comp; map_const := rfl
instance : LawfulFunctor WhereRecursive where id_map := WhereRecursive.map_id; comp_map := WhereRecursive.map_comp; map_const := rfl
instance : LawfulFunctor DoBlockRecursive where id_map := DoBlockRecursive.map_id; comp_map := DoBlockRecursive.map_comp; map_const := rfl
instance : LawfulFunctor AdoBlockRecursive where id_map := AdoBlockRecursive.map_id; comp_map := AdoBlockRecursive.map_comp; map_const := rfl
instance : LawfulFunctor DoStatementRecursive where id_map := DoStatementRecursive.map_id; comp_map := DoStatementRecursive.map_comp; map_const := rfl

end PureScript.CST.Types

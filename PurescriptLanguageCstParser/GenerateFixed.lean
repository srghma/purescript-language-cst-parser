-- `generate_fixed` – derives a fixed-point `inductive` (or `structure`) from a
-- functor-shaped inductive by declaring the recursive-position substitutions
-- explicitly with `fill`.
--
-- ── Non-mutual ────────────────────────────────────────────────────────────────
--   generate_fixed inductive Tree (a : Type) from TreeF
--     fill r with (Tree a)
--     deriving Repr, BEq
--
-- ── Mutual (inside `generate_fixed_mutual … end_generate_fixed_mutual` which is like `mutual … end` but `mutual` doesnt allow to use custom keywords) ───────────────────────────
--   generate_fixed_mutual
--     generate_fixed inductive Expr from Expr2F
--       fill e with Expr
--       fill s with Stmt
--     generate_fixed inductive Stmt from StmtF
--       fill e with Expr
--       fill s with Stmt
--   end_generate_fixed_mutual

import Lean

section
open Lean Meta Elab Command Term

--------------------------------------------------------------------------------
-- Syntax categories
--------------------------------------------------------------------------------

-- A single substitution clause, e.g. `fill r with (Tree a)`.
declare_syntax_cat fillClause
declare_syntax_cat fixed_kind
syntax "inductive" : fixed_kind
syntax "structure" : fixed_kind
syntax "fill" ident "with" term : fillClause

--------------------------------------------------------------------------------
-- Syntax-level identifier substitution
--------------------------------------------------------------------------------

private partial def substIdent (paramName : Name) (replacement : Syntax) : Syntax → Syntax
  | s@(.ident _ _ n _) =>
      let n' := n.eraseMacroScopes
      if n' == paramName || (n'.isStr && n'.getString! == paramName.toString) then
        replacement
      else
        s
  | .node info kind args =>
      .node info kind (args.map (substIdent paramName replacement))
  | other => other

--------------------------------------------------------------------------------
-- Build the constructor list for a fixed-point inductive
--------------------------------------------------------------------------------

/-- For each constructor of `functorName`, peel its Pi-type, skip the
    `iv.numParams` type-parameter binders, delab each field type, apply
    the `fills` substitutions, and return bracketedBinder syntax. -/
private def buildCtors (functorName : Name) (fills : Array (Name × Syntax))
    : CommandElabM (Array (TSyntax ``Lean.Parser.Command.ctor)) := do
  let env ← getEnv
  let some ci := env.find? functorName
    | throwError "generate_fixed: unknown inductive '{functorName}'"
  let iv := ci.inductiveVal!
  let mut result : Array (TSyntax ``Lean.Parser.Command.ctor) := #[]
  for ctorName in iv.ctors do
    let ctorCi ← getConstInfo ctorName
    match ctorCi with
    | .ctorInfo cv =>
      let fieldBinders ← liftTermElabM <|
          forallTelescope cv.type fun xs _ => do
            -- xs[0..numParams-1] are the functor's own type params; skip them.
            let fieldXs := xs.extract iv.numParams xs.size
            let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
            for fx in fieldXs do
              let decl ← fx.fvarId!.getDecl
              let fType ← inferType fx
              let fTypeStx ← PrettyPrinter.delab fType
              let mut fTypeSubst : Term := ⟨fTypeStx⟩
              for (p, repl) in fills do
                fTypeSubst := ⟨substIdent p repl fTypeSubst⟩
              let fId : Ident := mkIdent decl.userName
              let b : TSyntax ``Lean.Parser.Term.bracketedBinder ← `(bracketedBinder| ($fId : $fTypeSubst))
              binders := binders.push b
            return binders
      let ctorIdent := mkIdent ctorName.eraseMacroScopes.getString!.toName
      let ctor ←
        if fieldBinders.isEmpty then
          `(Lean.Parser.Command.ctor| | $ctorIdent:ident)
        else
          `(Lean.Parser.Command.ctor| | $ctorIdent:ident $fieldBinders*)
      result := result.push ctor
    | _ => throwError "generate_fixed: expected constructor info for '{ctorName}'"
  return result

--------------------------------------------------------------------------------
-- Build the field list for a fixed-point structure
--------------------------------------------------------------------------------

/-- Like `buildCtors` but produces `structField` syntax (no parentheses). -/
private def buildStructFields (functorName : Name) (fills : Array (Name × Syntax))
    : CommandElabM (Array Syntax) := do
  let env ← getEnv
  let some ci := env.find? functorName
    | throwError "generate_fixed: unknown '{functorName}'"
  let iv := ci.inductiveVal!
  let some ctorName := iv.ctors[0]?
    | throwError "generate_fixed: '{functorName}' has no constructors"
  let ctorCi ← getConstInfo ctorName
  match ctorCi with
  | .ctorInfo cv =>
    liftTermElabM <|
        forallTelescope cv.type fun xs _ => do
          let fieldXs := xs.extract iv.numParams xs.size
          let mut result : Array Syntax := #[]
          for fx in fieldXs do
            let decl ← fx.fvarId!.getDecl
            let fType ← inferType fx
            let fTypeStx ← PrettyPrinter.delab fType
            let mut fTypeSubst : Term := ⟨fTypeStx⟩
            for (p, repl) in fills do
              fTypeSubst := ⟨substIdent p repl fTypeSubst⟩
            let fId : Ident := mkIdent decl.userName
            -- structSimpleBinder: `name : type`
            let field : Syntax ← `(Lean.Parser.Command.structSimpleBinder| $fId:ident : $fTypeSubst)
            result := result.push field
          return result
  | _ => throwError "generate_fixed: expected constructor info for '{ctorName}'"

--------------------------------------------------------------------------------
-- Elaborator
--------------------------------------------------------------------------------
private def generateFixedSyntax (stx : Syntax) : CommandElabM Syntax := do
  -- stx is a `generate_fixed` command.
  -- The structure of the syntax is defined in the `elab` command below.
  let kw          := stx[1]
  let fixName     : Ident := ⟨stx[2]⟩
  let params      : Array (TSyntax [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]) :=
    stx[3].getArgs.map TSyntax.mk
  let functorName : Ident := ⟨stx[5]⟩
  let fillClauses := stx[6].getArgs
  let deriving?   := stx[7]

  let fills : Array (Name × Syntax) ← fillClauses.mapM fun fc => do
    -- fc is a `fillClause` node: "fill" ident "with" term
    let pId  : Ident := ⟨fc[1]⟩
    let repl : Syntax := fc[3]
    return (pId.getId, repl)

  let fName ← resolveGlobalConstNoOverload functorName
  let kwStr :=
    if kw.isToken "inductive" || (kw.getNumArgs > 0 && kw[0].isToken "inductive") then "inductive"
    else if kw.isToken "structure" || (kw.getNumArgs > 0 && kw[0].isToken "structure") then "structure"
    else ""

  match kwStr with
  | "inductive" => do
      let ctors ← buildCtors fName fills
      if deriving?.isNone then
        `(command| inductive $fixName $[$params]* : Type where $[$ctors]*)
      else
        let ds := deriving?[0] -- the `deriving` clause
        let ids : Array (TSyntax `Lean.Parser.Command.derivingClass) :=
            ds[1].getSepArgs.map fun id => ⟨Syntax.node .none ``Lean.Parser.Command.derivingClass #[id]⟩
        `(command| inductive $fixName $[$params]* : Type where $[$ctors]* deriving $[$ids],*)
  | "structure" => do
      let sfields ← buildStructFields fName fills
      let sfieldsCast : Array (TSyntax [`Lean.Parser.Command.structExplicitBinder, `Lean.Parser.Command.structImplicitBinder, `Lean.Parser.Command.structInstBinder, `Lean.Parser.Command.structSimpleBinder]) :=
        sfields.map TSyntax.mk
      if deriving?.isNone then
        `(command| structure $fixName $[$params]* where $[$sfieldsCast]*)
      else
        let ds := deriving?[0] -- the `deriving` clause
        let ids : Array (TSyntax `Lean.Parser.Command.derivingClass) :=
            ds[1].getSepArgs.map fun id => ⟨Syntax.node .none ``Lean.Parser.Command.derivingClass #[id]⟩
        `(command| structure $fixName $[$params]* where $[$sfieldsCast]* deriving $[$ids],*)
  | _ => throwError "generate_fixed: expected 'inductive' or 'structure'"

elab "generate_fixed" _kw:fixed_kind _fixName:ident _params:bracketedBinder*
     "from" _functorName:ident _fills:fillClause*
     _deriving?:(ppLine "deriving " Lean.Parser.Command.derivingClass,+)? : command => do
  let stx ← getRef
  let cmd ← generateFixedSyntax stx
  trace[Meta.debug] "generate_fixed expansion:\n{cmd}"
  elabCommand cmd

elab "generate_fixed_mutual" cmds:command+ "end_generate_fixed_mutual" : command => do
  let mut expanded : Array (TSyntax `command) := #[]
  for cmd in cmds do
    match cmd with
    | `(generate_fixed $_kw $_fixName $[$_params]* from $_functorName $[$_fills]* $[deriving $_ids,*]?) =>
        let exp ← generateFixedSyntax cmd
        expanded := expanded.push ⟨exp⟩
    | _ =>
        expanded := expanded.push ⟨cmd⟩
  let mutualCmd ← `(command| mutual $[$expanded]* end)
  trace[Meta.debug] "generate_fixed_mutual expansion:\n{mutualCmd}"
  elabCommand mutualCmd

end

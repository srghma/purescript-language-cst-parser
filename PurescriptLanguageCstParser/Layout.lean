module

public import PurescriptLanguageCstParser.Types

namespace PurescriptLanguageCstParser.Layout
open PurescriptLanguageCstParser.Types

def LayoutStack := List (SourcePos × LayoutDelim)

inductive LayoutDelim
  | LytRoot
  | LytTopDecl
  | LytTopDeclHead
  | LytDeclGuard
  | LytCase
  | LytCaseBinders
  | LytCaseGuard
  | LytLambdaBinders
  | LytParen
  | LytBrace
  | LytSquare
  | LytIf
  | LytThen
  | LytProperty
  | LytForall
  | LytTick
  | LytLet
  | LytLetStmt
  | LytWhere
  | LytOf
  | LytDo
  | LytAdo
  deriving Repr, BEq

def isIndented : LayoutDelim → Bool
  | .LytLet => true
  | .LytLetStmt => true
  | .LytWhere => true
  | .LytOf => true
  | .LytDo => true
  | .LytAdo => true
  | _ => false

def currentIndent (stk : LayoutStack) : Option SourcePos :=
  match stk with
  | (pos, lyt) :: rest =>
    if isIndented lyt then some pos else currentIndent rest
  | [] => none

def isTopDecl (tokPos : SourcePos) (stk : LayoutStack) : Bool :=
  match stk with
  | (lytPos, .LytWhere) :: (_, .LytRoot) :: _ =>
    tokPos.column == lytPos.column
  | _ => false

def lytToken (pos : SourcePos) (value : Token) : SourceToken :=
  { range := { start := pos, end := pos }
    leadingComments := []
    trailingComments := []
    value := value }

/-- State used during layout insertion -//
structure LayoutState where
  stk : LayoutStack
  acc : Array (SourceToken × LayoutStack)
  deriving Repr

def insertToken (token : SourceToken) (state : LayoutState) : LayoutState :=
  { state with acc := state.acc.push (token, state.stk) }

def pushStack (lytPos : SourcePos) (lyt : LayoutDelim) (state : LayoutState) : LayoutState :=
  { state with stk := (lytPos, lyt) :: state.stk }

def popStack (p : LayoutDelim → Bool) (state : LayoutState) : LayoutState :=
  match state.stk with
  | (pos, lyt) :: rest | p lyt => { state with stk := rest }
  | _ => state

def collapse (p : SourcePos → LayoutDelim → Bool) (state : LayoutState) : LayoutState :=
  let rec go (stk : LayoutStack) (acc : Array (SourceToken × LayoutStack)) : LayoutState :=
    match stk with
    | (lytPos, lyt) :: rest | p lytPos lyt =>
      let newAcc := if isIndented lyt then
        acc.push (lytToken (SourcePos.mk 0 0) (Token.LayoutEnd lytPos.column), rest) -- This is a placeholder for tokPos
      else acc
      go rest newAcc
    | _ => { stk := stk, acc := acc }
  -- Note: collapse needs tokPos, which is passed in insertLayout
  state -- Placeholder, will be implemented as a helper inside insertLayout

def insertLayout (src : SourceToken) (nextPos : SourcePos) (stack : LayoutStack) : (LayoutStack × Array (SourceToken × LayoutStack)) :=
  let tokPos := src.range.start

  -- Helpers implemented as local functions to access tokPos and nextPos
  let rec collapse' (p : SourcePos → LayoutDelim → Bool) (state : LayoutState) : LayoutState :=
    let rec go (stk : LayoutStack) (acc : Array (SourceToken × LayoutStack)) : LayoutState :=
      match stk with
      | (lytPos, lyt) :: rest | p lytPos lyt =>
        let newAcc := if isIndented lyt then
          acc.push (lytToken tokPos (Token.LayoutEnd lytPos.column), rest)
        else acc
        go rest newAcc
      | _ => { stk := stk, acc := acc }
    go state.stk state.acc

  let insertDefault (state : LayoutState) : LayoutState :=
    let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column < lytPos.column) state
    let state'' := insertSep state'
    insertToken src state''

  let insertSep (state : LayoutState) : LayoutState :=
    match state.stk with
    | (lytPos, .LytTopDecl) :: rest | tokPos.column == lytPos.column && tokPos.line != lytPos.line =>
      insertToken (lytToken tokPos (Token.LayoutSep tokPos.column)) { state with stk := rest }
    | (lytPos, .LytTopDeclHead) :: rest | tokPos.column == lytPos.column && tokPos.line != lytPos.line =>
      insertToken (lytToken tokPos (Token.LayoutSep tokPos.column)) { state with stk := rest }
    | (lytPos, lyt) :: _ | isIndented lyt && tokPos.column == lytPos.column && tokPos.line != lytPos.line =>
      if lyt == .LytOf then
        insertToken (lytToken tokPos (Token.LayoutSep tokPos.column)) (pushStack tokPos .LytCaseBinders state)
      else
        insertToken (lytToken tokPos (Token.LayoutSep tokPos.column)) state
    | _ => state

  let insertStart (lyt : LayoutDelim) (state : LayoutState) : LayoutState :=
    let currentS := state.stk
    let found := currentS.find? (fun (_, l) => isIndented l)
    match found with
    | some (pos, _) | nextPos.column <= pos.column => state
    | _ =>
      let state' := pushStack nextPos lyt state
      insertToken (lytToken nextPos (Token.LayoutStart nextPos.column)) state'

  let insertEnd (indent : Nat) (state : LayoutState) : LayoutState :=
    insertToken (lytToken tokPos (Token.LayoutEnd indent)) state

  let insertKwProperty (k : LayoutState → LayoutState) (state : LayoutState) : LayoutState :=
    let state' := insertDefault state
    match state'.stk with
    | (_, .LytProperty) :: rest => { state' with stk := rest }
    | _ => k state'

  let rec insert (state : LayoutState) : LayoutState :=
    match src.value with
    | .LowerName none "data" =>
      let state' := insertDefault state
      if isTopDecl tokPos state'.stk then
        pushStack tokPos .LytTopDecl state'
      else
        popStack (fun lyt => lyt == .LytProperty) state'

    | .LowerName none "class" =>
      let state' := insertDefault state
      if isTopDecl tokPos state'.stk then
        pushStack tokPos .LytTopDeclHead state'
      else
        popStack (fun lyt => lyt == .LytProperty) state'

    | .LowerName none "where" =>
      match state.stk with
      | (_, .LytTopDeclHead) :: rest =>
        let state' := { state with stk := rest }
        let state'' := insertToken src state'
        insertStart .LytWhere state''
      | (_, .LytProperty) :: rest =>
        let state' := { state with stk := rest }
        insertToken src state'
      | _ =>
        let state' := collapse' (fun lytPos lyt => if lyt == .LytDo then true else (isIndented lyt && tokPos.column <= lytPos.column)) state
        let state'' := insertToken src state'
        insertStart .LytWhere state''

    | .LowerName none "in" =>
      let state' := collapse' (fun _ lyt => if lyt == .LytLet || lyt == .LytAdo then false else isIndented lyt) state
      match state'.stk with
      | (pos1, .LytLetStmt) :: (pos2, .LytAdo) :: rest =>
        let state' := { state' with stk := rest }
        let state'' := insertEnd pos1.column state'
        let state''' := insertEnd pos2.column state''
        insertToken src state'''
      | (pos1, lyt) :: rest | isIndented lyt =>
        let state' := { state' with stk := rest }
        let state'' := insertEnd pos1.column state'
        insertToken src state''
      | _ =>
        let state' := insertDefault state'
        popStack (fun lyt => lyt == .LytProperty) state'

    | .LowerName none "let" =>
      insertKwProperty (fun state' =>
        match state'.stk with
        | (p, .LytDo) :: _ | p.column == tokPos.column =>
          insertStart .LytLetStmt state'
        | (p, .LytAdo) :: _ | p.column == tokPos.column =>
          insertStart .LytLetStmt state'
        | _ =>
          insertStart .LytLet state'
      ) state

    | .LowerName _ "do" =>
      insertKwProperty (insertStart .LytDo) state

    | .LowerName _ "ado" =>
      insertKwProperty (insertStart .LytAdo) state

    | .LowerName none "case" =>
      insertKwProperty (pushStack tokPos .LytCase) state

    | .LowerName none "of" =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      match state'.stk with
      | (_, .LytCase) :: rest =>
        let state' := { state' with stk := rest }
        let state'' := insertToken src state'
        let state''' := insertStart .LytOf state''
        pushStack nextPos .LytCaseBinders state'''
      | _ =>
        let state' := insertDefault state'
        popStack (fun lyt => lyt == .LytProperty) state'

    | .LowerName none "if" =>
      insertKwProperty (pushStack tokPos .LytIf) state

    | .LowerName none "then" =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      match state'.stk with
      | (_, .LytIf) :: rest =>
        let state' := { state' with stk := rest }
        let state'' := insertToken src state'
        pushStack tokPos .LytThen state''
      | _ =>
        let state' := insertDefault state'
        popStack (fun lyt => lyt == .LytProperty) state'

    | .LowerName none "else" =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      match state'.stk with
      | (_, .LytThen) :: rest =>
        let state' := { state' with stk := rest }
        insertToken src state'
      | _ =>
        let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column <= lytPos.column) state
        if isTopDecl tokPos state'.stk then
          insertToken src state'
        else
          let state' := insertSep state'
          let state'' := insertToken src state'
          popStack (fun lyt => lyt == .LytProperty) state''

    | .TokForall _ =>
      insertKwProperty (pushStack tokPos .LytForall) state

    | .TokBackslash =>
      let state' := insertDefault state
      pushStack tokPos .LytLambdaBinders state'

    | .TokRightArrow _ =>
      let state' := collapse' (fun lytPos lyt => if lyt == .LytDo then true else if lyt == .LytOf then false else (isIndented lyt && tokPos.column <= lytPos.column)) state
      let state'' := popStack (fun lyt => lyt == .LytCaseBinders || lyt == .LytCaseGuard || lyt == .LytLambdaBinders) state'
      insertToken src state''

    | .TokEquals =>
      let state' := collapse' (fun _ lyt => lyt == .LytWhere || lyt == .LytLet || lyt == .LytLetStmt) state
      match state'.stk with
      | (_, .LytDeclGuard) :: rest =>
        let state' := { state' with stk := rest }
        insertToken src state'
      | _ =>
        insertDefault state'

    | .TokPipe =>
      let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column <= lytPos.column) state
      match state'.stk with
      | (_, .LytOf) :: _ =>
        pushStack tokPos .LytCaseGuard (insertToken src state')
      | (_, .LytLet) :: _ =>
        pushStack tokPos .LytDeclGuard (insertToken src state')
      | (_, .LytLetStmt) :: _ =>
        pushStack tokPos .LytDeclGuard (insertToken src state')
      | (_, .LytWhere) :: _ =>
        pushStack tokPos .LytDeclGuard (insertToken src state')
      | _ =>
        insertDefault state'

    | .TokTick =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      match state'.stk with
      | (_, .LytTick) :: rest =>
        let state' := { state' with stk := rest }
        insertToken src state'
      | _ =>
        let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column <= lytPos.column) state
        let state'' := insertSep state'
        let state''' := insertToken src state''
        pushStack tokPos .LytTick state'''

    | .TokComma =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      match state' .stk with
      | (_, .LytBrace) :: _ =>
        insertToken src (pushStack tokPos .LytProperty state')
      | _ =>
        insertToken src state'

    | .TokDot =>
      let state' := insertDefault state
      match state'.stk with
      | (_, .LytForall) :: rest => { state' with stk := rest }
      | _ => pushStack tokPos .LytProperty state'

    | .TokLeftParen =>
      let state' := insertDefault state
      pushStack tokPos .LytParen state'

    | .TokLeftBrace =>
      let state' := insertDefault state
      let state'' := pushStack tokPos .LytBrace state'
      pushStack tokPos .LytProperty state''

    | .TokLeftSquare =>
      let state' := insertDefault state
      pushStack tokPos .LytSquare state'

    | .TokRightParen =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      let state'' := popStack (fun lyt => lyt == .LytParen) state'
      insertToken src state''

    | .TokRightBrace =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      let state'' := popStack (fun lyt => lyt == .LytProperty) state'
      let state''' := popStack (fun lyt => lyt == .LytBrace) state''
      insertToken src state'''

    | .TokRightSquare =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      let state'' := popStack (fun lyt => lyt == .LytSquare) state'
      insertToken src state''

    | .TokString _ _ =>
      let state' := insertDefault state
      popStack (fun lyt => lyt == .LytProperty) state'

    | .TokLowerName none _ =>
      let state' := insertDefault state
      popStack (fun lyt => lyt == .LytProperty) state'

    | .TokOperator _ _ =>
      let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column <= lytPos.column) state
      let state'' := insertSep state'
      insertToken src state''

    | _ =>
      insertDefault state

  let finalState := insert { stk := stack, acc := #[] }
  (finalState.stk, finalState.acc)

end PurescriptLanguageCstParser.Layout

import PurescriptLanguageCstParser.GenerateFixed

-- ---------------------------------------------------------------------------
-- Test 1 : Tree  (payload param `a`, recursive param `r`)
-- ---------------------------------------------------------------------------

namespace Test1

inductive TreeF (a r : Type) where
  | leaf (val : a)
  | node (left right : r)
  deriving Repr, BEq

generate_fixed inductive Tree (a : Type) from TreeF
  fill r with (Tree a)
  deriving Repr, BEq

-- Expected:  Tree : Type → Type
--            Tree.leaf : {a} → a → Tree a
--            Tree.node : {a} → Tree a → Tree a → Tree a
/-- info: Tree : Type → Type -/
#guard_msgs in
#check @Tree
/-- info: @Tree.leaf : {a : Type} → a → Tree a -/
#guard_msgs in
#check @Tree.leaf
/-- info: @Tree.node : {a : Type} → Tree a → Tree a → Tree a -/
#guard_msgs in
#check @Tree.node

def exTree : Tree Nat :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3))

/--
info: Test1.Tree.node (Test1.Tree.leaf 1) (Test1.Tree.node (Test1.Tree.leaf 2) (Test1.Tree.leaf 3))
-/
#guard_msgs in
#eval exTree

end Test1

-- ---------------------------------------------------------------------------
-- Test 2 : Expr  (no payload params, recursive param `r`)
-- ---------------------------------------------------------------------------

namespace Test2

inductive ExprF (r : Type) where
  | num (n : Int)
  | add (l r_ : r)
  | mul (l r_ : r)
  | neg (e : r)
  deriving Repr, BEq

generate_fixed inductive Expr from ExprF
  fill r with Expr
  deriving Repr, BEq

/-- info: Expr : Type -/
#guard_msgs in
#check @Expr
/-- info: Expr.num : Int → Expr -/
#guard_msgs in
#check @Expr.num
/-- info: Expr.add : Expr → Expr → Expr -/
#guard_msgs in
#check @Expr.add

def exExpr : Expr :=
  .add (.num 1) (.mul (.num 2) (.neg (.num 3)))

/--
info: Test2.Expr.add (Test2.Expr.num 1) (Test2.Expr.mul (Test2.Expr.num 2) (Test2.Expr.neg (Test2.Expr.num 3)))
-/
#guard_msgs in
#eval exExpr

end Test2

-- ---------------------------------------------------------------------------
-- Test 3 : Mutual recursion  (Expr2F / StmtF)
-- ---------------------------------------------------------------------------

namespace Test3

inductive Expr2F (e s : Type) where
  | num  (n : Int)
  | add  (l r : e)
  | ifE  (cond : s) (thenB elseB : e)
  deriving Repr, BEq

inductive StmtF (e s : Type) where
  | assign (var : String) (rhs : e)
  | seq    (a b : s)
  | whileS (cond : e) (body : s)
  deriving Repr, BEq

-- Inside `mutual … end`, each `generate_fixed` elaborates to a bare
-- `inductive` which Lean's mutual-block elaborator threads correctly.
generate_fixed_mutual
  generate_fixed inductive Expr from Expr2F
    fill e with Expr
    fill s with Stmt

  generate_fixed inductive Stmt from StmtF
    fill e with Expr
    fill s with Stmt
end_generate_fixed_mutual
/-- info:
inductive Test3.Expr : Type
number of parameters: 0
constructors:
Test3.Expr.num : Int → Expr
Test3.Expr.add : Expr → Expr → Expr
Test3.Expr.ifE : Stmt → Expr → Expr → Expr
 -/
#guard_msgs in
#print Expr
/-- info:
inductive Test3.Stmt : Type
number of parameters: 0
constructors:
Test3.Stmt.assign : String → Expr → Stmt
Test3.Stmt.seq : Stmt → Stmt → Stmt
Test3.Stmt.whileS : Expr → Stmt → Stmt
 -/
#guard_msgs in
#print Stmt

def exStmt : Stmt :=
  .whileS
    (.add (.num 1) (.num 2))
    (.assign "x"
      (.ifE
        (.seq (.assign "skip" (.num 0)) (.assign "skip" (.num 0)))
        (.num 0)
        (.num 1)))

/--
info:
Test3.Stmt.whileS
  (Test3.Expr.add (Test3.Expr.num 1) (Test3.Expr.num 2))
  (Test3.Stmt.assign
    "x"
    (Test3.Expr.ifE
      (Test3.Stmt.seq (Test3.Stmt.assign "skip" (Test3.Expr.num 0)) (Test3.Stmt.assign "skip" (Test3.Expr.num 0)))
      (Test3.Expr.num 0)
      (Test3.Expr.num 1)))
-/
#guard_msgs in
#eval exStmt

end Test3

-- ---------------------------------------------------------------------------
-- Test 4 : RoseTree  (recursive parameter nested inside `List`)
-- ---------------------------------------------------------------------------

namespace Test4

inductive RoseTreeF (a r : Type) where
  | node (val : a) (children : List r)
  deriving Repr, BEq

-- `fill r with (RoseTree a)` rewrites `List r` → `List (RoseTree a)` because
-- `substIdent` walks into the `List r` application and replaces the `r` leaf.
generate_fixed inductive RoseTree (a : Type) from RoseTreeF
  fill r with (RoseTree a)
  deriving Repr, BEq

/-- info: RoseTree : Type → Type -/
#guard_msgs in
#check @RoseTree

def exRoseTree : RoseTree String :=
  .node "root" [.node "child1" [], .node "child2" [.node "grandchild" []]]

/--
info: Test4.RoseTree.node
  "root"
  [Test4.RoseTree.node "child1" [], Test4.RoseTree.node "child2" [Test4.RoseTree.node "grandchild" []]]
-/
#guard_msgs in
#eval exRoseTree

end Test4

-- ---------------------------------------------------------------------------
-- Test 5 : Mutual inductive + structure
-- ---------------------------------------------------------------------------

namespace Test5

inductive ExprF (error e m : Type) where
  | num      (n : Int)
  | add      (l r : e)
  | metadata (meta_ : m)
  | err      (e : error)
  deriving Repr, BEq

structure MetadataF (error e m : Type) where
  expr     : e
  meta_     : m
  hasError : Option error
  deriving Repr, BEq

generate_fixed_mutual
  generate_fixed inductive Expr (error : Type) from ExprF
    fill e with (Expr error)
    fill m with (Metadata error)
    deriving Repr, BEq

  generate_fixed structure Metadata (error : Type) from MetadataF
    fill e with (Expr error)
    fill m with (Metadata error)
    deriving Repr, BEq
end_generate_fixed_mutual

/-- info:
inductive Test5.Expr : Type → Type
number of parameters: 1
constructors:
Test5.Expr.num : {error : Type} → Int → Expr error
Test5.Expr.add : {error : Type} → Expr error → Expr error → Expr error
Test5.Expr.metadata : {error : Type} → Metadata error → Expr error
Test5.Expr.err : {error : Type} → error → Expr error
 -/
#guard_msgs in
#print Expr
/-- info:
structure Test5.Metadata (error : Type) : Type
number of parameters: 1
fields:
  Test5.Metadata.expr : Expr error
  Test5.Metadata.meta_ : Metadata error
  Test5.Metadata.hasError : Option error
constructor:
  Test5.Metadata.mk {error : Type} (expr : Expr error) (meta_ : Metadata error) (hasError : Option error) :
    Metadata error
 -/
#guard_msgs in
#print Metadata

def ex5 : Expr String := .add (.num 1) (.err "oops")

/--
info: Test5.Expr.add (Test5.Expr.num 1) (Test5.Expr.err "oops")
-/
#guard_msgs in
#eval ex5

end Test5

-- ---------------------------------------------------------------------------
-- Test 6 : Mixed declarations in generate_fixed_mutual
-- ---------------------------------------------------------------------------

namespace Test6

inductive ExprF (e : Type) where
  | num (n : Int)
  | add (l r : e)
  deriving Repr

generate_fixed_mutual
  generate_fixed inductive Expr from ExprF
    fill e with Expr

  inductive ExprTag where
    | lit
    | bin
end_generate_fixed_mutual

deriving instance Repr, BEq for Expr
deriving instance Repr, BEq for ExprTag

/-- info:
inductive Test6.Expr : Type
number of parameters: 0
constructors:
Test6.Expr.num : Int → Expr
Test6.Expr.add : Expr → Expr → Expr
 -/
#guard_msgs in
#print Expr
/-- info:
inductive Test6.ExprTag : Type
number of parameters: 0
constructors:
Test6.ExprTag.lit : ExprTag
Test6.ExprTag.bin : ExprTag
 -/
#guard_msgs in
#print ExprTag

end Test6

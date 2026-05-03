module
-- prelude
-- public import PurescriptLanguageCstParser.PureScript.CST.Types.PType
-- public import PurescriptLanguageCstParser.PureScript.CST.Types.Expr

-- mutual
--   public inductive Expr (error : Type) where
--     | num (val : Int)
--     | add (l r : Expr error)
--     | ifE (cond : Expr error) (thenE elseE : Expr error)
--     deriving Repr, BEq

--   private structure Metadata (error : Type) where
--     expr : Expr error
--     meta_ : Metadata error
--     hasError : Option error
--     deriving Repr, BEq
-- end

public inductive Expr (w : Type) : Type where
  | num (n : Int) : Expr w
  | add (l : Expr w) (r : Expr w) : Expr w
  | err (e : w) : Expr w

#print Expr

public inductive ExprF (e s : Type) where
  | num (val : Int)
  | add (l r : e)
  | ifE (cond : s) (thenE elseE : e)

#print ExprF

import Regex.Data.Anchor
import Regex.Data.Classes

namespace Regex.Data

/--
An inductive type that represents a regular expression.
-/
inductive Expr : Type where
  | empty : Expr
  | epsilon : Expr
  | anchor : Anchor → Expr
  | char : Char → Expr
  | group : Nat → Expr → Expr
  | alternate : Expr → Expr → Expr
  | concat : Expr → Expr → Expr
  | star : Expr → Expr
  | classes : Classes → Expr
deriving Repr, Inhabited

end Regex.Data

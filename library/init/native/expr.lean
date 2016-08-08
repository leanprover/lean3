prelude
import init.option
import init.meta.expr
import init.meta.level
-- import init.meta.environment

constant environment : Type.{1}

definition lookup (e : environment) (n : name) : option (list level -> expr) :=
  option.none

-- inductive typed (e : environment) : expr → expr :=
-- | const : Π n ls, typed e ((lookup e n) ls) expr.const n ls
-- | app : Π f x n info domain codomain,
--   typed (expr.pi n info domain codomain) f ->
--   typed domain x ->
--   typed (instantiate codomain domain) (f x)
-- | pi : 

-- inductive step : expr → state → expr → state :=
-- | 

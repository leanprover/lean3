prelude
import init.meta.tactic
import init.meta.simp_tactic
import init.meta.defeq_simp_tactic
import init.meta.rewrite_tactic
import init.meta.expr
import init.meta.unfold_tactic
import init.monad
import init.list
import init.combinator
import init.wf
import init.relation
import init.meta.injection_tactic
import init.measurable
import init.applicative

namespace backend

meta_definition compiler (e : expr) : string := to_string e

end backend

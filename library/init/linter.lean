prelude

import init.data.option.basic
import init.meta.declaration
import init.meta.tactic

meta constant pos_info_provider : Type
meta constant pos_info_provider.expr_pos : pos_info_provider → option pos

meta structure linter :=
(lint : pos_info_provider → declaration → tactic unit)

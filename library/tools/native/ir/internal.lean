/-
Copyright (c) 2017 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

-- Functions used by the VM compiler which are required by the native compiler
-- as well.
meta constant native.is_internal_cnstr : expr → option unsigned
meta constant native.is_internal_cases : expr → option unsigned
meta constant native.is_internal_proj : expr → option unsigned
meta constant native.get_nat_value : expr → option nat
meta constant native.dump_format : string → format → nat
meta constant native.get_quote_expr : expr -> option expr
meta constant native.serialize_quote_macro : expr -> string


import data.sigma
open function

namespace Lob

inductive TypeExpr : Type₁ :=
| Arrow : TypeExpr → TypeExpr → TypeExpr
| QuotedTermExpr : TypeExpr → TypeExpr

open TypeExpr

inductive TermExpr : TypeExpr → Type :=
| Lob : ∀ { LT : TypeExpr }, TermExpr (Arrow (QuotedTermExpr LT) LT) → TermExpr LT

open TermExpr

definition denoteTermExpr : Π {typeExpr : TypeExpr}, TermExpr typeExpr → Type₁
| _ (@Lob typeExpr1 termExpr1) := (denoteTermExpr termExpr1) (Lob termExpr1)

end Lob

-- Backward chaining with tagged rules
constants {P Q R S T : Prop} (Hpq : P → Q) (Hqr : Q → R) (Hrs : R → S) (Hst : S → T)
attribute Hpq [backward]
attribute Hqr [backward]
attribute Hrs [backward]
attribute Hst [backward]

definition lemma1 (p : P) : Q := by blast
definition lemma2 (p : P) : R := by blast
definition lemma3 (p : P) : S := by blast
definition lemma4 (p : P) : T := by blast

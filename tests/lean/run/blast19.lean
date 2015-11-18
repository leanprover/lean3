-- Backward chaining with hypotheses
constants {P Q R S T : Prop}

definition lemma1 : (P → Q) → P → Q := by blast
definition lemma2 : (P → Q) → (Q → R) → P → R := by blast
definition lemma3 : (P → Q) → (Q → R) → (R → S) → P → S := by blast
definition lemma4 : (P → Q) → (Q → R) → (R → S) → (S → T) → P → T := by blast

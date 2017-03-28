constants (f : ℕ → ℕ) (a b c : ℕ) (fab : f a = f b) (fbc : f b = f c)
constants (p : ℕ → Prop) (pfa : p (f a)) (pfb : p (f b)) (pfc :p (f c))

attribute [simp] fbc

example : p (f a) :=
by simp [fab]; exact pfc

example : p (f a) :=
by simp_only [fab]; exact pfb

example : p (f a) :=
by do tactic.simp_only [```(fab)],
      tactic.applyc ``pfb

example (h : p (f a)) : p (f c) :=
by simp [fab] at h; assumption

example (h : p (f a)) : p (f b) :=
by simp_only [fab] at h; assumption

example (h : p (f a)) : p (f b) :=
by do eh ← tactic.get_local `h,
      tactic.simp_only_at eh [```(fab)],
      tactic.assumption

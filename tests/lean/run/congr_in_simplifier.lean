-- Note: these examples used to fail before we implemented custom `mk_congr_fun` and `mk_congr` in the app-builder.
-- Issue: the app-builder was not convinced that `x` was a pi type.

def α : Type := ℕ → ℕ

example (x y : α) (H : x = y) (n : ℕ) : x n = y n :=
by simp [H]

example (x y : α) (H₁ : x = y) (m n : ℕ) (H₂ : m = n) : x m = y n :=
by simp [H₁, H₂]

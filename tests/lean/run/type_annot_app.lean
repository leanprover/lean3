def f : ℕ → ℕ := λ _, 0

theorem A (x : ℕ) : f x = 0 := rfl
theorem B (x : ℕ) : (f : _) x = 0 := rfl
theorem C (x : ℕ) : (f : ℕ → ℕ) x = 0 := rfl

example (x) : f x = 0 := by simp [A] --ok
example (x) : f x = 0 := by have := A x; rw this --ok
example (x) : f x = 0 := by simp [B] --fails
example (x) : f x = 0 := by have := B x; rw this --fails
example (x) : f x = 0 := by simp [C] --fails
example (x) : f x = 0 := by have := C x; rw this --fails

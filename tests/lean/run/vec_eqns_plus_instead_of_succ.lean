open nat

inductive Vec (X : Type*) : ℕ → Type*
| nil {} : Vec 0
| cons   : X → Pi {n : nat}, Vec n → Vec (n + 1)

namespace Vec

def get₁ {A : Type} : Π {n : ℕ}, Vec A (n + 1) → A
| n (cons x₁ xs) := x₁

def get₂ {A : Type} : Π {n : ℕ}, Vec A (n + 2) → A
| n (cons x₁ (cons x₂ xs)) := x₂

def get₃ {A : Type} : Π {n : ℕ}, Vec A (n + 3) → A
| n (cons x₁ (cons x₂ (cons x₃ xs))) := x₃

def get₄ {A : Type} : Π {n : ℕ}, Vec A (n + 4) → A
| n (cons x₁ (cons x₂ (cons x₃ (cons x₄ xs)))) := x₄

end Vec

import Mathlib

theorem algebra_180832 {d : ℕ → ℕ → ℤ} (h1 : ∀ a b, d a b + d b a = 0)
    (h2 : ∀ a b c, d a b + d b c + d c a = 0) :
    ∃ f : ℕ → ℤ, ∀ a b, d a b = f a - f b := by

  use fun a => d a 0
  intro a b
  have eq1 := h2 a b 0
  have eq2 := h1 0 a
  have eq3 : d 0 a = -d a 0 := by
    linarith 
  rw [eq3] at eq1
  linarith
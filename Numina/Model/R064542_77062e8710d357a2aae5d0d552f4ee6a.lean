import Mathlib

theorem algebra_5528 {a b c : ℤ} (h : ∀ x : ℝ, (x + 3) * (x + 7) * (x + 11) = x^3 + a * x^2 + b * x + c) :
    a + b + c = 383 := by
  have eq1 := h 1
  norm_num at eq1
  have h1 : (a : ℝ) + (b : ℝ) + (c : ℝ) = 383 := by
    linarith
  have h2 : a + b + c = 383 := by
    exact_mod_cast h1
  exact h2
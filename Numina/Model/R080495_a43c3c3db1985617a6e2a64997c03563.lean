import Mathlib

theorem algebra_22006 (a b c : ℤ) (h : ∀ x y : ℝ, 2 * x + 3 * y ≠ 0 →
    (8 * x ^ 3 + 27 * y ^ 3) / (2 * x + 3 * y) = a * x ^ 2 + b * x * y + c * y ^ 2) :
    a + b + c = 7 := by
  have eq1 := h 1 1 (by norm_num)
  norm_num at eq1
  have h1 : (a : ℝ) + (b : ℝ) + (c : ℝ) = 7 := by
    linarith
  have h2 : a + b + c = 7 := by
    exact_mod_cast h1
  exact h2
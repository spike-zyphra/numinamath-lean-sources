import Mathlib

theorem algebra_21188 (r : ℝ) (hr : r > 0) (h : ∀ x y, x^2 - 4 * x + y^2 - 6 * y - 36 = 0 → (x - 2)^2 + (y - 3)^2 = r^2) :
    r = 7 := by

  have h1 := h 2 10 (by norm_num)
  have eq1 : (2 - (2 : ℝ)) ^ 2 + (10 - (3 : ℝ)) ^ 2 = r ^ 2 := by
    simpa using h1
  have eq2 : r ^ 2 = 49 := by
    norm_num at eq1 ⊢
    linarith

  have eq4 : r = 7 := by
    nlinarith
  exact_mod_cast eq4
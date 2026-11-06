import Mathlib

theorem algebra_60424 {f : ℝ → ℝ} (h : ∀ x, 4 * f (f x) - 2 * f x - 3 * x = 0) :
    f 0 = 0 := by
  have h1 := h 0
  have eq1 : 4 * f (f 0) - 2 * f 0 - 3 * (0 : ℝ) = 0 := h1
  have eq2 : 4 * f (f 0) - 2 * f 0 = 0 := by linarith
  have h2 : f (f 0) = f 0 / 2 := by
    linarith
  have h3 := h (f 0)
  have eq3 : 4 * f (f (f 0)) - 2 * f (f 0) - 3 * (f 0 : ℝ) = 0 := h3
  rw [show f (f 0) = f 0 / 2 by linarith [h2]] at eq3
  have h4 : f (f 0 / 2) = f 0 := by
    nlinarith
  have h5 := h (f 0 / 2)
  have eq5 : 4 * f (f (f 0 / 2)) - 2 * f (f 0 / 2) - 3 * (f 0 / 2 : ℝ) = 0 := h5
  rw [show f (f 0 / 2) = f 0 by linarith [h4]] at eq5
  have eq6 : 4 * f (f 0) - 2 * f 0 - 3 * (f 0 / 2 : ℝ) = 0 := by
    linarith [eq5]
  have eq7 : f 0 = 0 := by
    linarith [eq2, eq6]
  exact_mod_cast eq7
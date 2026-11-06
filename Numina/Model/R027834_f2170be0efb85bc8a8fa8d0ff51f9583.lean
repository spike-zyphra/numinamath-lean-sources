import Mathlib

theorem algebra_12047 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x^3 + a * x^2 + b * x + 2)
    (h : ∀ x, f (2 - x) = -f (2 + x)) : f 1 = 4 := by

  have h1 := h 0
  have eq1 : f 2 = 0 := by
    have eq2 : f (2 - (0 : ℝ)) = -f (2 + (0 : ℝ)) := by
      simpa using h1
    norm_num at eq2 ⊢
    linarith
  have eq2 : f 2 = 2^3 + a * 2^2 + b * 2 + 2 := by
    apply hf
  rw [eq2] at eq1
  have eq3 : 2 * a + b + 5 = 0 := by
    linarith

  have h2 := h 1
  have eq4 : f 1 = 1^3 + a * 1^2 + b * 1 + 2 := by
    apply hf
  have eq5 : f 3 = 3^3 + a * 3^2 + b * 3 + 2 := by
    apply hf
  have eq6 : f 1 = - (f 3) := by
    have eq7 : f (2 - (1 : ℝ)) = -f (2 + (1 : ℝ)) := by 
      simpa using h2
    norm_num at eq7 ⊢
    linarith
  rw [eq5] at eq6
  rw [eq4] at eq6

  have eq7 : 10 * a + 4 * b + 32 = 0 := by
    linarith
  have eq8 : 5 * a + 2 * b = -16 := by
    linarith
  have eq9 : a = -6 := by
    nlinarith [eq3, eq8]
  have eq10 : b = 7 := by
    linarith [eq9, eq3]
  have eq11 : f 1 = 4 := by
    rw [hf 1]
    rw [eq9, eq10]
    norm_num
  exact eq11
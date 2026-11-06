import Mathlib

theorem algebra_17043 {b c : ℤ} (h : ∀ x : ℝ, x ^ 2 - 8 * x + 8 = (x + b) ^ 2 - c) :
    b + c = 4 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h (-1 : ℝ)
  have eq4 : (b : ℝ) ^ 2 - (c : ℝ) = 8 := by
    norm_num at eq1
    nlinarith
  have eq5 : (1 + (b : ℝ)) ^ 2 - (c : ℝ) = 1 := by
    norm_num at eq2
    nlinarith
  have eq6 : (-1 + (b : ℝ)) ^ 2 - (c : ℝ) = 17 := by
    norm_num at eq3
    nlinarith
  have hb : (b : ℝ) = -4 := by
    nlinarith [eq4, eq5]
  have hc : (c : ℝ) = 8 := by
    nlinarith [eq4, hb]
  have hb_int : b = -4 := by
    exact_mod_cast hb
  have hc_int : c = 8 := by
    exact_mod_cast hc
  linarith [hb_int, hc_int]
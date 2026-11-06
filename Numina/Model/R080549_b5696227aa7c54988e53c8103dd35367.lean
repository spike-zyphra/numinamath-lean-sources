import Mathlib

theorem algebra_321005 (x : ℝ) (h : 0 ≤ x ^ 3 + 2020 ∧ 0 ≤ 2030 - x ^ 3)
    (h' : Real.sqrt (x ^ 3 + 2020) - Real.sqrt (2030 - x ^ 3) = 54) :
    28 * Real.sqrt (x ^ 3 + 2020) + 27 * Real.sqrt (2030 - x ^ 3) = 2007 := by
  have hx1 : 0 ≤ x^3 + 2020 := h.1
  have hx2 : 0 ≤ 2030 - x^3 := h.2
  have h3 : (Real.sqrt (x^3 + 2020)) ^ 2 = x^3 + 2020 := Real.sq_sqrt (by linarith [hx1])
  have h4 : (Real.sqrt (2030 - x^3)) ^ 2 = 2030 - x^3 := Real.sq_sqrt (by linarith [hx2])
  have h5 : (Real.sqrt (x^3 + 2020)) ^ 2 + (Real.sqrt (2030 - x^3)) ^ 2 = 4050 := by
    linarith [h3, h4]
  have ha : Real.sqrt (x ^ 3 + 2020) = 63 := by
    nlinarith [Real.sqrt_nonneg (x ^ 3 + 2020), Real.sqrt_nonneg (2030 - x ^ 3), sq_nonneg (Real.sqrt (x ^ 3 + 2020) - Real.sqrt (2030 - x ^ 3)), sq_nonneg (Real.sqrt (x ^ 3 + 2020) + Real.sqrt (2030 - x ^ 3)), h5, h']
  have hb : Real.sqrt (2030 - x ^ 3) = 9 := by
    nlinarith [Real.sqrt_nonneg (x ^ 3 + 2020), Real.sqrt_nonneg (2030 - x ^ 3), sq_nonneg (Real.sqrt (x ^ 3 + 2020) - Real.sqrt (2030 - x ^ 3)), sq_nonneg (Real.sqrt (x ^ 3 + 2020) + Real.sqrt (2030 - x ^ 3)), h5, h']
  rw [ha, hb]
  norm_num
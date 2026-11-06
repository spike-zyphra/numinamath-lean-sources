import Mathlib

open Real

theorem algebra_181244 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x + 1 / y = 3) (h2 : y + 2 / x = 3) :
    x * y ≤ 3 + sqrt 7 := by

  have eq1 : x * y = 3 * y - 1 := by
    have h1' : x + 1 / y = 3 := h1
    field_simp at h1' ⊢
    nlinarith [h1']

  have eq2 : x * y = 3 * x - 2 := by
    have h2' : y + 2 / x = 3 := h2
    field_simp at h2' ⊢
    nlinarith [h2']

  have eq3 : 3 * y - 1 = 3 * x - 2 := by
    nlinarith [eq1, eq2]

  have eq4 : y = x - 1 / 3 := by
    nlinarith

  have eq5 : 3 * x ^ 2 - 10 * x + 6 = 0 := by
    rw [eq4] at eq2
    field_simp at eq2 ⊢
    nlinarith [eq2]

  have h3 : (x - (5 + Real.sqrt 7) / 3) * (x - (5 - Real.sqrt 7) / 3) = 0 := by
    nlinarith [eq5, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7)]

  cases' (mul_eq_zero.1 h3) with h4 h5

  · -- Case x = (5 + Real.sqrt 7) / 3
    have hx1 : x = (5 + Real.sqrt 7) / 3 := by linarith
    have hy1 : y = (4 + Real.sqrt 7) / 3 := by
      rw [hx1] at eq4
      linarith
    rw [hx1, hy1]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7), Real.sqrt_nonneg 7]

  · -- Case x = (5 - Real.sqrt 7) / 3
    have hx2 : x = (5 - Real.sqrt 7) / 3 := by linarith
    have hy2 : y = (4 - Real.sqrt 7) / 3 := by
      rw [hx2] at eq4
      linarith
    rw [hx2, hy2]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7), Real.sqrt_nonneg 7]
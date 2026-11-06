import Mathlib

theorem algebra_325702 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : abs x + y = 3) (h2 : abs x * y + x ^ 3 = 0) :
    x + y = 4 - Real.sqrt 13 := by
  by_cases h : x ≥ 0
  · -- Case x ≥ 0, so |x| = x
    rw [abs_of_nonneg h] at h1 h2
    have h3 : y = 3 - x := by linarith
    rw [h3] at h2
    have h4 : x * (3 - x) + x ^ 3 = 0 := by linarith
    have h5 : x ^ 3 - x ^ 2 + 3 * x = 0 := by 
      nlinarith
    have h6 : x * (x ^ 2 - x + 3) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - x + 3), sq_nonneg (x)]
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case x = 0, which is impossible
      exfalso
      exact hx (by linarith)
    · -- Case x^2 - x + 3 = 0, which has no real solutions
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x)]
  · -- Case x < 0, so |x| = -x
    rw [abs_of_neg (lt_of_not_ge h)] at h1 h2
    have h3 : y = x + 3 := by linarith
    rw [h3] at h2
    have h4 : x ^ 3 - x ^ 2 - 3 * x = 0 := by 
      nlinarith
    have h5 : x * (x ^ 2 - x - 3) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - x - 3), sq_nonneg (x)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case x = 0, which is impossible
      exfalso
      exact hx (by linarith)
    · -- Case x^2 - x - 3 = 0
      have h_eq1 : x ^ 2 - x - 3 = 0 := by linarith
      have h_eq2 : x ^ 2 - x - 3 = (x - (1 + Real.sqrt 13) / 2) * (x - (1 - Real.sqrt 13) / 2) := by
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (13:ℝ) by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ (13:ℝ) by norm_num)]
      have h_eq3 : (x - (1 + Real.sqrt 13) / 2) * (x - (1 - Real.sqrt 13) / 2) = 0 := by 
        rw [←h_eq2]
        linarith
      cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
      · -- Case where x = (1 + √13)/2, which contradicts x < 0
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (13:ℝ) by norm_num), Real.sqrt_nonneg 13]
      · -- Case where x = (1 - √13)/2, which is valid
        have hx_eq : x = (1 - Real.sqrt 13) / 2 := by linarith
        have hy_eq : y = (7 - Real.sqrt 13) / 2 := by
          rw [h3, hx_eq]
          linarith
        linarith [hx_eq, hy_eq]
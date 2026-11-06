import Mathlib

theorem algebra_166550 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : Real.sqrt x + Real.sqrt y = 3) (h2 : Real.sqrt (x + 5) + Real.sqrt (y + 3) = 5) :
    (x, y) = (4, 1) ∨ (x, y) = (121 / 64, 169 / 64) := by
  have h3 : Real.sqrt x ≥ 0 := by positivity
  have h4 : Real.sqrt y ≥ 0 := by positivity
  have eq1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have eq2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have eq3 : Real.sqrt x ^ 2 + Real.sqrt y ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) = 9 := by
    nlinarith [h1, Real.sqrt_nonneg x, Real.sqrt_nonneg y, eq1, eq2]
  have h5 : Real.sqrt (x + 5) ≥ 0 := by positivity
  have h6 : Real.sqrt (y + 3) ≥ 0 := by positivity
  have h7 : Real.sqrt (x + 5) ^ 2 = x + 5 := by
    have h8 : 0 ≤ x + 5 := by nlinarith
    exact Real.sq_sqrt h8
  have h9 : Real.sqrt (y + 3) ^ 2 = y + 3 := by
    have h10 : 0 ≤ y + 3 := by nlinarith
    exact Real.sq_sqrt h10
  have eq4 : Real.sqrt (x + 5) ^ 2 + Real.sqrt (y + 3) ^ 2 + 2 * (Real.sqrt (x + 5) * Real.sqrt (y + 3)) = 25 := by
    nlinarith [h2, Real.sqrt_nonneg (x + 5), Real.sqrt_nonneg (y + 3), h7, h9]
  have h10 : Real.sqrt y = 3 - Real.sqrt x := by linarith
  have h11 : y = (3 - Real.sqrt x) ^ 2 := by
    calc
      y = (Real.sqrt y) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (3 - Real.sqrt x) ^ 2 := by rw [h10]
  have h14 : (Real.sqrt x - 2) * (Real.sqrt x - 11 / 8) = 0 := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg (x + 5), Real.sqrt_nonneg (y + 3),
      Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith),
      Real.sq_sqrt (show 0 ≤ (x + 5 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (y + 3 : ℝ) by nlinarith),
      h1, h2, h11]
  cases' (mul_eq_zero.1 h14) with h15 h16
  · -- sqrt(x) = 2
    have h17 : Real.sqrt x = 2 := by linarith
    have hx_eq : x = 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] at h17
      · nlinarith
      all_goals nlinarith
    have hy_eq : y = 1 := by
      have h18 : Real.sqrt y = 1 := by
        linarith [h1, h17]
      have h19 : y = Real.sqrt y ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      rw [h19, h18]
      norm_num
    left
    exact Prod.ext hx_eq hy_eq
  · -- sqrt(x) = 11/8
    have h18 : Real.sqrt x = 11 / 8 := by linarith
    have hx_eq : x = 121 / 64 := by
      rw [Real.sqrt_eq_iff_sq_eq] at h18
      · nlinarith
      all_goals nlinarith
    have hy_eq : y = 169 / 64 := by
      have h19 : Real.sqrt y = 13 / 8 := by
        linarith [h1, h18]
      have h20 : y = Real.sqrt y ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      rw [h20, h19]
      norm_num
    right
    exact Prod.ext hx_eq hy_eq
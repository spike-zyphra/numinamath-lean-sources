import Mathlib

theorem algebra_157037 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : x - y^2 = 3) (h2 : x^2 + y^4 = 13) :
    x = (3 + Real.sqrt 17) / 2 := by
  have h3 : x = y^2 + 3 := by linarith
  rw [h3] at h2
  have eq1 : 2 * y^4 + 6 * y^2 - 4 = 0 := by
    nlinarith [h2]
  have eq2 : y^4 + 3 * y^2 - 2 = 0 := by
    nlinarith
  have h4 : y^2 = (-3 + Real.sqrt 17) / 2 := by
    have h5 : y^4 + 3 * y^2 - 2 = 0 := eq2
    have h6 : (y^2) ^ 2 + 3 * (y^2) - 2 = 0 := by nlinarith
    have h7 : y^2 > 0 := by
      nlinarith [hy]
    have h8 : (y^2 - (-3 + Real.sqrt 17)/2) * (y^2 - (-3 - Real.sqrt 17)/2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case where y^2 = (-3 + sqrt(17))/2 > 0
      have h11 : y^2 = (-3 + Real.sqrt 17)/2 := by
        linarith
      exact h11
    · -- Case where y^2 = (-3 - sqrt(17))/2 < 0, contradiction since y^2 ≥ 0
      have h11 : y^2 = (-3 - Real.sqrt 17)/2 := by
        nlinarith
      have h12 : (-3 - Real.sqrt 17)/2 < 0 := by
        have h13 : Real.sqrt 17 > 0 := Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num)
        have h14 : Real.sqrt 17 > 3 := by
          have h15 : Real.sqrt 17 > Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          have h16 : Real.sqrt 9 = 3 := Real.sqrt_eq_cases.mpr (by norm_num)
          linarith
        linarith
      linarith [h11, h12, sq_nonneg y]
  have hx_eq : x = (3 + Real.sqrt 17) / 2 := by
    rw [show x = y^2 + 3 by linarith [h1]]
    rw [h4]
    ring_nf
  exact hx_eq